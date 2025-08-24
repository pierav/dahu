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
    bq_push_if.master bq_push_io

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

    di_t decode_di;
    dynamic_decoder ddecoder (
        .clk(clk),
        .rstn(rstn),
        .si_i(decode_si),
        .si_i_valid(in_i_valid),
        .fs_i(RV::Initial),
        .priv_lvl_i(RV::PRIV_LVL_M),
        .frm_i(3'b0),
        .tvm_i(1'b0),
        .tw_i(1'b0),
        .tsr_i(1'b0),
        .debug_mode_i(1'b0),
        .di_o(decode_di),
        .di_o_ready(di_o_ready) // TODO Stall allocation sq, lq
    );

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
        di_o        = decode_di; // Base assignement
        if (isBranch) begin
            di_o.bqid   = bq_push_io.bqid;
        end
    end

    // TODO BQ full
    // logic stall;
    // assign stall = 
    /* Ready valid */
    assign in_i_ready = di_o_ready; // Cannot stall
    assign di_o_valid = in_i_valid; // Cannot stall


    assert property (
        @(posedge clk) disable iff (!rstn)
            in_i_valid |-> di_o.si.valid
    );

endmodule

