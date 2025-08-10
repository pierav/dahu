import C::*;

module core #() (
    input clk,
    input rstn,

    input logic fetch_addr_ready, // Cache is ready to accept new request
    output logic fetch_addr_valid, // Cache response
    output logic[XLEN-1:0] fetch_addr, // Fetch addr

    input logic fetch_data_valid, // Received data from cache
    input logic[32-1:0] fetch_data, // Fetch data
    
    output logic exit_o,
    output logic [C::XLEN-1:0] exit_code_o
);
    // Frontend 
    logic [XLEN-1:0] pc_q, pc_d;
    logic [XLEN-1:0] if2dec_pc_q, if2dec_pc_d;

    // Send to cache
    assign fetch_addr_valid = fetch_addr_ready; // Always req when ready
    assign fetch_addr = pc_q;
    
    assign pc_d = pc_q + 4;
    always_ff @(posedge clk) begin
        if(!rstn) begin
            if2dec_pc_q <= 0;
            pc_q <= 0;
        end else begin 
            // Not stalled (PC issued to memory)
            if(fetch_addr_valid) begin
                if2dec_pc_q <= if2dec_pc_d;
                pc_q <= pc_d;
            end
        end
    end
    
    assign if2dec_pc_d = pc_q;
            
    // Decode
    si_t si;
    di_t di;
    logic decoder_valid;

    static_decoder #() sdecoder (
        .pc_i(if2dec_pc_q),
        .data_i(fetch_data),
        .si_o(si)
    );

    dynamic_decoder ddecoder (
        .clk(clk),
        .rstn(rstn),
        .si_i(si),
        .input_ready_i(fetch_data_valid),
        .fs_i(RV::Initial),
        .priv_lvl_i(RV::PRIV_LVL_M),
        .frm_i(3'b0),
        .tvm_i(1'b0),
        .tw_i(1'b0),
        .tsr_i(1'b0),
        .debug_mode_i(1'b0),
        .di_o(di),
        .output_valid_o(decoder_valid)
    );
    
    always_ff @(posedge clk) begin
        if(decoder_valid) begin
            // First check oracle
            handler_pkg::dpi_instr_decode(
                {12'b0, di.id}, di.si.pc, di.si.tinst);
            // Then check HW decoder
            if(!di.si.valid) begin
                $error("invalid inst m!", di.si.tinst);
            end
        end
    end
    
    initial begin
        $display($time, ": Hello from core");
        exit_o      = 0;
        exit_code_o = 0;

        repeat (1000000) @(posedge clk);
        exit_o      = 1;
        exit_code_o = 42;
    end

    property valid_decoded_insts;
    @(posedge clk) disable iff (!rstn)
        decoder_valid |-> di.si.valid;
    endproperty

    // assert property (valid_decoded_insts)
    //     else $error("Invalid inst");

endmodule
