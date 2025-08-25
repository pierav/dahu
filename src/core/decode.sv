import C::*;

module decode #() (
    input clk,
    input rstn,
    input fetch_data_t in_i,  // Instruction to process
    input logic in_i_valid,  // Instruction to process is here
    output logic in_i_ready, // Ready to decode new one
    output di_t di_o,        // The renammed instruction 
    output logic di_o_valid, // The instruction is renammed
    input logic di_o_ready,   // The next stage is ready
    // To BQ
    bq_push_if.master bq_push_io,
    // Squash intf
    squash_if.slave  squash_io

);
    bp_t bp_i;
    assign bp_i = in_i.bp;

    si_t decode_si;
    /* Decode */
    static_decoder #() sdecoder (
        .pc_i(in_i.pc),
        .data_i(in_i.data),
        .si_o(decode_si)
    );

    logic is_fault;
    dynamic_decoder_fault ddecoder (
        .clk(clk),
        .rstn(rstn),
        .si_i(decode_si),
        .fs_i(RV::Initial),
        .priv_lvl_i(RV::PRIV_LVL_M),
        .frm_i(3'b0),
        .tvm_i(1'b0),
        .tw_i(1'b0),
        .tsr_i(1'b0),
        .debug_mode_i(1'b0),
        .is_fault_o(is_fault)
    );

    // TODO Stall allocation sq, lq
    id_t inst_id_q;
    always_ff @(posedge clk) begin
        if(!rstn) begin
            inst_id_q <= '0;
        end else begin
            if (squash_io.valid) begin
                // Reset to the expected id
                inst_id_q <= squash_io.id + 1; 
            end else begin
                if(in_i_valid && di_o_ready) begin
                    inst_id_q <= inst_id_q + 1;
                end
            end
        end
    end


    /* Direct branch resolution */
    logic isBranch, isDirectBranch, isIndirectBranch, isUncondBranch;
    assign isBranch = decode_si.fu == FU_CTRL;
    assign isDirectBranch = isBranch &&
        decode_si.op inside { BLT, BLTU, BGE, BGEU, BEQ, BNE, JAL };
    assign isIndirectBranch = isBranch &&
        decode_si.op inside { JALR };

    /* Direct Branch computation */
    pc_t direct_branch_target;
    assign direct_branch_target = in_i.pc + decode_si.imm; // J or B imm ?

    logic misspredict_direct;
    assign misspredict_direct = isDirectBranch &&
                                bp_i.taken &&
                                bp_i.pcnext != direct_branch_target;

    // TODO resolve direct branch missprediction here !
    // TODO latch bpred ?
    assign bq_push_io.bp = bp_i;
    assign bq_push_io.pc = di_o.si.pc;
    assign bq_push_io.id = di_o.id;
    assign bq_push_io.valid = isBranch && in_i_valid && di_o_ready; // Push only one time

    /* Output instruction to next stage */
    always_comb begin : output_process
        di_o = '0; // base assignement 
        di_o.si     = decode_si;
        di_o.bqid   = isBranch ? bq_push_io.bqid : '0;
        di_o.id     = inst_id_q;
        di_o.fault  = is_fault;
    end

    // TODO BQ full
    // logic stall;
    // assign stall = 
    /* Ready valid */
    assign in_i_ready = di_o_ready; // Cannot stall
    assign di_o_valid = in_i_valid; // Cannot stall

    always_ff @(posedge clk) begin
        if(!di_o_ready) begin
            $display("Decode: (port0) next stage not ready");
        end else if(!in_i_valid) begin
            $display("Decode: (port0) no valids inputs");
        end else begin
            $display("Decode: (port0) %s: pc %x (sn=%x) %s <- %s %s",
                di_o_valid ?  "SUCCESS " : "FAILURE",
                di_o.si.pc, di_o.id,
                di_o.si.rs1_valid ? dumpAReg(di_o.si.rs1) : "",
                di_o.si.rs2_valid ? dumpAReg(di_o.si.rs2) : "",
                di_o.si.rd_valid ? dumpAReg(di_o.si.rd) : "");
        end
    end

    assert property (
        @(posedge clk) disable iff (!rstn)
            in_i_valid |-> di_o.si.valid
    );

endmodule

