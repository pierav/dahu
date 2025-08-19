module branch_alu(
    input xlen_t      rs1,
    input xlen_t      rs2,
    input xlen_t      pc,
    input xlen_t      imm,
    input ctrl_set_t  op,
    output logic      taken_o,
    output xlen_t     target_pc_o
);

    xlen_t diff;
    logic zero, sign, carry;
    // Single subtraction with carry-out
    assign {carry, diff} = {1'b0, rs1} - {1'b0, rs2}; 
    assign zero = (diff == 64'd0);
    assign sign = diff[63];

    /* Branch decision logic */
    always_comb begin : branch_taken_comp
        unique case (op)
            JAL, JALR: taken_o = '1;
            BLT:       taken_o = sign;
            BLTU:      taken_o = ~carry;
            BGE:       taken_o = ~sign;
            BGEU:      taken_o = carry;
            BEQ:       taken_o = zero;
            BNE:       taken_o = ~zero;
            default:   taken_o = 'x; // don't care
        endcase
    end

    /* Branch address resolution */
    pc_t adder_in, adder_out, adder_out_fix;
    assign adder_in = (op == JALR) ? rs1 : pc;
    assign adder_out = adder_in + imm;
    assign adder_out_fix = (op == JALR) ? (adder_out & ~64'd1) : adder_out;

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
    input bp_t bp_i,
    input logic bp_i_valid,
    output logic bp_i_ready,

    // Core   
    input rob_entry_t   retire_entry_i,
    input logic         retire_entry_i_valid
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
    // First WRITE port
    bp_t                              insert_entry_i;
    logic                             insert_entry_i_valid;
    // Second READ/WRITE port
    xlen_t                            resolved_pc_i;
    logic [$clog2(NR_BQ_ENTRIES)-1:0] resolved_id_i;
    logic                             resolved_taken_i;
    logic                             resoled_pc_i_valid;
    // First READ port
    bq_entry_t                        commit_entry_o;
    logic                             commit_entry_pop;
    // Misc
    logic                             bq_empty, bq_full;

    logic match_prediction;
    logic match_taken;
    logic missprediction;
    assign match_taken      = bq[resolved_id_i].bp.taken == resolved_taken_i;
    assign match_prediction = bq[resolved_id_i].bp.pcnext == resolved_pc_i;
    assign missprediction   = resolved_taken_i ? match_prediction :
                                                 match_taken;
    assign commit_entry_o   = bq[commit_id_q];
    assign bq_empty         = count_q == '0;
    assign bq_full          = !count_q[$clog2(NR_BQ_ENTRIES)];

    always @(posedge clk) begin : bw_writes
        if(!rstn) begin
            count_q <= 0;
            pred_id_q <= 0;
            commit_id_q <= 0;
        end else begin
            if(insert_entry_i_valid) begin // Push new entry InO
                assert (!bq_full) else 
                    $error("PUSH in full bq");
                bq[pred_id_q].bp <= insert_entry_i;
                count_q          <= count_q + 1;
                pred_id_q        <= pred_id_q + 1;
            end
            if(resoled_pc_i_valid) begin // Update entry OoO
                bq[resolved_id_i].bp.pcnext <= resolved_pc_i;
                bq[resolved_id_i].bp.taken  <= resolved_taken_i;
                bq[resolved_id_i].missprediction <= missprediction;
            end
            if(commit_entry_pop) begin // Pop committed entry InO
                assert (!bq_empty) else
                    $error("POP in empty bq");
                count_q <= count_q - 1;
                commit_id_q <= commit_id_q + 1;
            end
        end
    end

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

    // BQ <-> Frontend
    assign insert_entry_i_valid = bp_i_valid;
    assign insert_entry_i       = bp_i;
    assign bp_i_ready           = !bq_full;

    // BQ --> Issue
    assign fuinput_i_ready  = 1'b1; // Always ready because already inserted

    // BALU --> BQ
    assign resolved_pc_i        = balu_target_pc_o;
    assign resolved_id_i        = bq_id_t'(fuinput_i.id);
    assign resolved_taken_i     = balu_taken_o;
    assign resoled_pc_i_valid   = fuinput_i_valid;

    /* BQ --> ROB: Mark completion without delay */
    assign branch_completion_o.id    = fuinput_i.id;
    assign branch_completion_o.valid = fuinput_i_valid;
    /* Rob --> BQ */
    // Pop when commit instruction is head of BQ
    assign commit_entry_pop = retire_entry_i_valid &&
                              !bq_empty && /* commit_entry_o valid */
                              commit_entry_o.id == retire_entry_i.id;

endmodule
