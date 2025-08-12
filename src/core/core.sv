import C::*;

module core #() (
    input clk,
    input rstn,

    input logic fetch_addr_ready, // Cache is ready to accept new request
    output logic fetch_addr_valid, // Cache response
    output logic[XLEN-1:0] fetch_addr, // Fetch addr

    input logic fetch_data_valid, // Received data from cache
    input logic[32-1:0] fetch_data, // Fetch data
    output logic fetch_data_ready, // Received data from cache

    output logic exit_o,
    output logic [C::XLEN-1:0] exit_code_o
);
    // Fetch
    fetch_data_t fetch_o;
    logic fetch_o_valid;
    logic fetch_o_ready;

    // Decode
    fetch_data_t decode_in_i; // Instruction to process
    logic decode_in_i_valid;  // Instruction to process is here
    logic decode_in_i_ready;  // Ready to decode new one
    di_t decode_di_o;         // The renammed instruction 
    logic decode_di_o_valid;  // The instruction is renammed
    logic decode_di_o_ready;  // The next stage is ready

    /* Rename */
    di_t  rename_di_i;       // Instruction to process
    logic rename_di_i_valid; // Instruction to process is here
    logic rename_di_i_ready; // Ready to decode new one
    di_t  rename_di_o;       // The renammed instruction 
    logic rename_di_o_valid; // The instruction is renammed
    logic rename_di_o_ready; // The next stage is ready

    /* Issue */
    di_t issue_di_i;
    logic issue_di_i_valid;
    logic issue_di_i_ready;
    fu_input_t issue_fuinput_o;
    logic issue_fuinput_o_valid;
    logic issue_fuinput_o_ready;
    
    /* Execute stage */
    logic execute_fuinput_i_ready;
    assign execute_fuinput_i_ready = 1'b1; // TODO fake stage

    // Pipeline stages handle
    /* Fetch -> decode */
    fetch_data_t if2dec_q, if2dec_d;
    logic if2dec_valid_q, if2dec_valid_d;
    // Decode -> rename
    di_t dec2ren_di_q, dec2ren_di_d;
    logic dec2ren_di_valid_q, dec2ren_di_valid_d;
    /* Rename to issue */
    di_t ren2issue_di_q, ren2issue_di_d;
    logic ren2issue_di_valid_q, ren2issue_di_valid_d;
    /* Issue -> Execute */
    fu_input_t issue2execute_fuinput_q, issue2execute_fuinput_d;
    logic issue2execute_fuinput_valid_q,
          issue2execute_fuinput_valid_d;


    // Forward pipe regs input
    assign if2dec_d = fetch_o;
    assign if2dec_valid_d = fetch_o_valid;
    assign dec2ren_di_d = decode_di_o;
    assign dec2ren_di_valid_d = decode_di_o_valid;
    assign ren2issue_di_d = rename_di_o;
    assign ren2issue_di_valid_d = rename_di_o_valid;
    assign issue2execute_fuinput_d = issue_fuinput_o;
    assign issue2execute_fuinput_valid_d = issue_fuinput_o_valid;

    // Forward Stage inputs
    assign decode_in_i = if2dec_q;
    assign decode_in_i_valid = if2dec_valid_q;
    assign rename_di_i = dec2ren_di_q; 
    assign rename_di_i_valid = dec2ren_di_valid_q;
    assign issue_di_i = ren2issue_di_q;
    assign issue_di_i_valid = ren2issue_di_valid_q;
    // assign execute... // TODO exe stage

    // Backward Ready propagation (ungated for now ?)
    // Use !next_pipe_stage || next_stage_ready
    //        |                  \-- Next stage is going to be bubble
    //        \--------------------- Fill bublle stage
    assign fetch_o_ready = !if2dec_valid_q || decode_in_i_ready;
    assign decode_di_o_ready = !dec2ren_di_valid_q || rename_di_i_ready;
    assign rename_di_o_ready = !ren2issue_di_valid_q || issue_di_i_ready;
    assign issue_fuinput_o_ready = !issue2execute_fuinput_valid_d || execute_fuinput_i_ready;

    always_ff @(posedge clk) begin
        if(!rstn) begin
            // if2dec_q <= '0;
            // dec2ren_di_q <= '0;
            // ren2issue_di_q <= '0;
        end else begin
            if(decode_in_i_ready/* && fetch_o_valid*/) begin 
                if2dec_q <= if2dec_d;
                if2dec_valid_q <= if2dec_valid_d;
            end
            if(rename_di_i_ready/* && decode_di_o_valid*/) begin
                dec2ren_di_q <= dec2ren_di_d;
                dec2ren_di_valid_q <= dec2ren_di_valid_d;
            end
            if(issue_di_i_ready/* && rename_di_o_valid*/) begin
                ren2issue_di_q <= ren2issue_di_d;
                ren2issue_di_valid_q <= ren2issue_di_valid_d;
            end
            if(execute_fuinput_i_ready) begin 
                issue2execute_fuinput_q <= issue2execute_fuinput_d;
                issue2execute_fuinput_valid_q <= issue2execute_fuinput_valid_d;
            end
        end
    end

    /* Fetch */
    fetch #() fetch (
        .clk(clk),
        .rstn(rstn),
        .fetch_addr_ready(fetch_addr_ready), // Cache is ready to accept new request
        .fetch_addr_valid(fetch_addr_valid), // Cache response
        .fetch_addr(fetch_addr), // Fetch addr
        .fetch_data_valid(fetch_data_valid), // Received data from cache
        .fetch_data(fetch_data), // Fetch data
        .fetch_data_ready(fetch_data_ready),
        .fetch_o(fetch_o),
        .fetch_o_valid(fetch_o_valid),
        .fetch_o_ready(fetch_o_ready)
    );

    /* Decode */
    decode #() decode (
        .clk(clk),
        .rstn(rstn),
        .in_i(decode_in_i),  // Instruction to process
        .in_i_valid(decode_in_i_valid),  // Instruction to process is here
        .in_i_ready(decode_in_i_ready), // Ready to decode new one
        .di_o(decode_di_o),        // The decoded instruction 
        .di_o_valid(decode_di_o_valid), // The instruction is decoded
        .di_o_ready(decode_di_o_ready)   // The next stage is ready
    );


    /* Rename */
    rename #() rename (
        .clk(clk),
        .rstn(rstn),
        .di_i(rename_di_i),        // Instruction to process
        .di_i_valid(rename_di_i_valid),  // Instruction to process is here
        .di_i_ready(rename_di_i_ready), // Ready to rename new one
        .di_o(rename_di_o),        // The renammed instruction 
        .di_o_valid(rename_di_o_valid), // The instruction is renammed
        .di_o_ready(rename_di_o_ready)   // The next stage is ready

    );

    /* Issue */   
    issue #() issue (
        .clk(clk),
        .rstn(rstn),
        .di_i(issue_di_i),
        .di_i_valid(issue_di_i_valid),
        .di_i_ready(issue_di_i_ready),
        .fuinput_o(issue_fuinput_o),
        .fuinput_o_valid(issue_fuinput_o_valid),
        .fuinput_o_ready(issue_fuinput_o_ready)
    );

    initial begin
        handler_pkg::dpi_monitor_init();
    end
    /* DPI tracer (at pipeline stage) */
    /* Use negedge to display after everything is computed */
    always_ff @(negedge clk) begin
        if(dec2ren_di_valid_q) begin
            // First check oracle
            handler_pkg::dpi_instr_decode(
                {12'b0, dec2ren_di_q.id},
                dec2ren_di_q.si.pc,
                dec2ren_di_q.si.tinst);
            // Then check HW decoder
            if(!dec2ren_di_q.si.valid) begin
                $error("invalid inst m!", dec2ren_di_q.si.tinst);
            end
        end
        if(ren2issue_di_valid_q) begin
            handler_pkg::dpi_instr_renamed(
                32'(ren2issue_di_q.id),
                ren2issue_di_q.si.pc, 
                32'(ren2issue_di_q.prs1),
                32'(ren2issue_di_q.prs1_renammed),
                32'(ren2issue_di_q.prs2),
                32'(ren2issue_di_q.prs2_renammed),
                32'(ren2issue_di_q.prd)
            );
        end
        if(issue2execute_fuinput_valid_q) begin
            handler_pkg::dpi_instr_issue(
                32'(issue2execute_fuinput_q.id),
                issue2execute_fuinput_q.pc,
                issue2execute_fuinput_q.rs1val,
                issue2execute_fuinput_q.rs2val
            );
        end
        handler_pkg::dpi_tick();
    end
 
    initial begin
        $display("*** Hello from core (src/core/core.sv)");
        exit_o      = 0;
        exit_code_o = 0;

        repeat (1000000) @(posedge clk);
        exit_o      = 1;
        exit_code_o = 42;
    end

    // assert property (valid_decoded_insts)
    //     else $error("Invalid inst");

endmodule
