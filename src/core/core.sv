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
    // Fetch 
    logic [XLEN-1:0] pc_q, pc_d;
    logic [XLEN-1:0] if2dec_pc_q, if2dec_pc_d;

    // Decode
    si_t decode_si;
    di_t decode_di;
    logic decoder_ready;
    logic decoder_valid;

    /* Rename */
    di_t rename_di_i;
    di_t rename_di_o;
    logic rename_ready;


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
            if(fetch_addr_valid && decoder_ready) begin
                if2dec_pc_q <= if2dec_pc_d;
                pc_q <= pc_d;
            end
        end
    end
    
    assign if2dec_pc_d = pc_q;
            
    /* Decode */
    assign decoder_ready = rename_ready;
    static_decoder #() sdecoder (
        .pc_i(if2dec_pc_q),
        .data_i(fetch_data),
        .si_o(decode_si)
    );

    dynamic_decoder ddecoder (
        .clk(clk),
        .rstn(rstn),
        .si_i(decode_si),
        .input_ready_i(fetch_data_valid),
        .fs_i(RV::Initial),
        .priv_lvl_i(RV::PRIV_LVL_M),
        .frm_i(3'b0),
        .tvm_i(1'b0),
        .tw_i(1'b0),
        .tsr_i(1'b0),
        .debug_mode_i(1'b0),
        .di_o(decode_di),
        .output_valid_o(decoder_valid)
    );
    

    // /* Decode to rename stage */
    // di_t dec2ren_id_q, dec2ren_id_d;
    // @always_ff @(posedge clk) begin
    //     if(!rstn) begin 
    //         dec2ren_id_q <= 0;
    //     end else begin
    //         dec2ren_id_q <= dec2ren_id_d;
    //     end
    // end

    /* Rename */
    assign rename_di_i = decode_di; // Bypass pipeline stage
    rename #() rename (
        .clk(clk),
        .rstn(rstn),
        .di_i(rename_di_i),
        .di_o(rename_di_o),
        .di_o_valid(rename_ready)
    );

    /* DPI tracer */
    always_ff @(posedge clk) begin
        if(decoder_valid && rename_ready) begin
            // First check oracle
            handler_pkg::dpi_instr_decode(
                {12'b0, decode_di.id},
                decode_di.si.pc,
                decode_di.si.tinst);
            // Then check HW decoder
            if(!decode_di.si.valid) begin
                $error("invalid inst m!", decode_di.si.tinst);
            end
        end
        if(decoder_valid && rename_ready) begin
            handler_pkg::dpi_instr_renamed(
                32'(rename_di_o.id),
                rename_di_o.si.pc, 
                32'(rename_di_o.prs1),
                32'(rename_di_o.prs1_renammed),
                32'(rename_di_o.prs2),
                32'(rename_di_o.prs2_renammed),
                32'(rename_di_o.prd)
            );
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
        decoder_valid |-> decode_di.si.valid;
    endproperty

    // assert property (valid_decoded_insts)
    //     else $error("Invalid inst");

endmodule
