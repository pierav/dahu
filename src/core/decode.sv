import C::*;

module decode #() (
    input clk,
    input rstn,
    input fetch_data_t in_i,  // Instruction to process
    input logic in_i_valid,  // Instruction to process is here
    output logic in_i_ready, // Ready to decode new one
    output di_t di_o,        // The renammed instruction 
    output logic di_o_valid, // The instruction is renammed
    input logic di_o_ready   // The next stage is ready

);
    si_t decode_si;
    /* Decode */
    static_decoder #() sdecoder (
        .pc_i(in_i.pc),
        .data_i(in_i.data),
        .si_o(decode_si)
    );

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
        .di_o(di_o),
        .di_o_ready(di_o_ready)
    );

    /* Ready valid */
    assign in_i_ready = di_o_ready; // Cannot stall
    assign di_o_valid = in_i_valid; // Cannot stall

    assert property (
        @(posedge clk) disable iff (!rstn)
            in_i_valid |-> di_o.si.valid
    );

endmodule

