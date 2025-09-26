import C::*;

module branch_alu(
    input xlen_t      rs1,
    input xlen_t      rs2,
    input xlen_t      pc,
    input xlen_t      imm,
    input ctrl_set_t  op,
    output logic      taken_o,
    output xlen_t     target_pc_o
);
    /* Branch decision logic */
    always_comb begin : branch_taken_comp
        unique case (op)
            JAL, JALR: taken_o = '1;
            BEQ:       taken_o = (rs1 == rs2);
            BNE:       taken_o = (rs1 != rs2);
            BLT:       taken_o = $signed(rs1) < $signed(rs2);
            BGE:       taken_o = $signed(rs1) >= $signed(rs2);
            BLTU:      taken_o = rs1 < rs2;
            BGEU:      taken_o = rs1 >= rs2;
            default:   taken_o = 'x; // don't care
        endcase
    end

    /* Branch address resolution */
    pc_t adder_in, adder_out, adder_out_fix;
    assign adder_in = (op == JALR) ? rs1 : pc;
    assign adder_out = adder_in + imm;
    assign adder_out_fix = (op == JALR) ? (adder_out & ~pc_t'(1)) : adder_out;

    assign target_pc_o = adder_out_fix;

endmodule


module fu_branch #() (
    input logic clk,
    input logic rstn,
    input fu_input_t fuinput_i,
    input logic      fuinput_i_valid,
    output logic      fuinput_i_ready,

    // branch do not use the fu_output_t port
    output completion_port_t branch_completion_o,

    // From/To BP
    bq_push_if.slave bq_push_io,
    bq_pop_if.bq     bq_pop_io,
    // Squash intf
    squash_if.slave  squash_io
); 

    /* The branch Queue */
    /* The idea of the branch queue is to flush at commit while allowing 
     * branches to execute out of order.
     * 
     * Branches must be inserted after they are predicted.
     */
    logic [$clog2(NR_BQ_ENTRIES)-1:0] pred_id_q, commit_id_q;
    logic [$clog2(NR_BQ_ENTRIES):0] count_q;

    // Branch Queue Entry
    typedef struct packed {
        id_t   id;             // Debug only ?
        xlen_t pc;             // Debug only ?
        bp_t   bp;             // Branch prediction
        logic  missprediction; // Actual outcome
    } bq_entry_t;

    // The branch queue
    bq_entry_t [NR_BQ_ENTRIES-1:0]    bq;
    // Second READ/WRITE port
    xlen_t                            resolved_pc_i;
    logic [$clog2(NR_BQ_ENTRIES)-1:0] resolved_id_i;
    logic                             resolved_taken_i;
    logic                             resolved_pc_i_valid;
    // First READ port
    bq_entry_t                        commit_entry_o;
    logic                             commit_entry_pop;
    // Misc
    logic                             bq_empty, bq_full;
    // BQ <-> Frontend
    assign bq_push_io.ready     = !bq_full;
    assign bq_push_io.bqid      = pred_id_q;

    logic match_prediction;
    logic match_taken;
    logic missprediction;
    assign match_taken      = bq[resolved_id_i].bp.taken == resolved_taken_i;
    assign match_prediction = bq[resolved_id_i].bp.pcnext == resolved_pc_i;
    assign missprediction   = resolved_taken_i ? !match_prediction :
                                                 !match_taken;
    assign bq_empty         = count_q == '0;
    assign bq_full          = count_q[$clog2(NR_BQ_ENTRIES)];

    always @(posedge clk) begin : bw_writes
        if(!rstn) begin
            count_q <= 0;
            pred_id_q <= 0;
            commit_id_q <= 0;
        end else begin
            if (squash_io.valid) begin
                // Reset all counter to 0
                // Don't care of squash_io.id as the BQ entry index
                // is allocated dynamically
                count_q <= 0; 
                pred_id_q <= 0;
                commit_id_q <= 0;
            end else begin
                if(bq_push_io.valid) begin // Push new entry InO
                    `ifndef SYNTHESIS
                    assert (!bq_full) else 
                        $error("PUSH in full bq");
                    `endif
                    bq[pred_id_q].bp <= bq_push_io.bp;
                    bq[pred_id_q].pc <= bq_push_io.pc;
                    bq[pred_id_q].id <= bq_push_io.id;
                    pred_id_q        <= pred_id_q + 1;
                end
                if(resolved_pc_i_valid) begin // Update entry OoO
                    bq[resolved_id_i].bp.pcnext <= resolved_pc_i;
                    bq[resolved_id_i].bp.taken  <= resolved_taken_i;
                    bq[resolved_id_i].missprediction <= missprediction;
                end
                if(commit_entry_pop) begin // Pop committed entry InO
                    `ifndef SYNTHESIS
                    assert (!bq_empty) else
                        $error("POP in empty bq");
                    `endif
                    commit_id_q <= commit_id_q + 1;
                end
                // count_q single case assignement
                case ({bq_push_io.valid, commit_entry_pop})
                    2'b10: count_q <= count_q + 1;
                    2'b01: count_q <= count_q - 1;
                    default: count_q <= count_q;
                endcase
            end
        end
    end
    always_comb begin
        commit_entry_o   = bq[commit_id_q]; // Default assignement
        // Bypass writed values
        if(resolved_pc_i_valid && commit_id_q == resolved_id_i) begin
            commit_entry_o.bp.pcnext        = resolved_pc_i;
            commit_entry_o.bp.taken         = resolved_taken_i;
            commit_entry_o.missprediction   = missprediction;
        end
    end

    `ifndef SYNTHESIS
    always_ff @(negedge clk) begin
        for(int i = 0; i < count_q; i++) begin
            bq_id_t idx = bq_id_t'(i) + commit_id_q;
            bq_entry_t e = bq[idx];
            `LOG(EX, "BQ[%x] : pc=%x (sn=%x) target=%x(%d) missp=%d",
                idx, e.pc, e.id, e.bp.pcnext, e.bp.taken, e.missprediction);
        end
        if(resolved_pc_i_valid) begin
            `LOG(EX, "BQ[%x] <- target=%x(%d) missp=%d",
                resolved_id_i, resolved_pc_i, resolved_taken_i, missprediction);
        end
    end
    `endif

    /* Branch alu */
    xlen_t     balu_rs1;
    xlen_t     balu_rs2;
    xlen_t     balu_pc;
    xlen_t     balu_imm;
    ctrl_set_t balu_op;
    logic      balu_taken_o;
    xlen_t     balu_target_pc_o;

    branch_alu branch_alu(
        .rs1(balu_rs1),
        .rs2(balu_rs2),
        .pc(balu_pc),
        .imm(balu_imm),
        .op(balu_op),
        .taken_o(balu_taken_o),
        .target_pc_o(balu_target_pc_o)
    );

    // FUinp --> BALU
    assign balu_rs1 = fuinput_i.rs1val;
    assign balu_rs2 = fuinput_i.rs2val;
    assign balu_pc  = fuinput_i.pc;
    assign balu_imm = fuinput_i.imm;
    assign balu_op  = fuinput_i.op.ctrl;



    // BQ --> Issue
    assign fuinput_i_ready  = 1'b1; // Always ready because already inserted

    // BALU --> BQ
    assign resolved_pc_i        = balu_target_pc_o;
    assign resolved_id_i        = fuinput_i.bqid;
    assign resolved_taken_i     = balu_taken_o;
    assign resolved_pc_i_valid   = fuinput_i_valid;

    /* BQ --> ROB: Mark completion without delay */
    assign branch_completion_o.id    = fuinput_i.id;
    assign branch_completion_o.valid = fuinput_i_valid;
    /* Rob --> BQ */
    // Pop when commit instruction is head of ROB
    assign commit_entry_pop = bq_pop_io.pop;
    /* BQ -> Commit */
    assign bq_pop_io.bp             = commit_entry_o.bp;
    assign bq_pop_io.missprediction = commit_entry_o.missprediction;

endmodule
