import C::*;

module fetch #() (
    input logic clk,
    input logic rstn,
    /* Cache protocol */
    input logic fetch_addr_ready, // Cache is ready to accept new request
    output logic fetch_addr_valid, // Cache response
    output logic[XLEN-1:0] fetch_addr, // Fetch addr
    input logic fetch_data_valid, // Received data from cache
    input logic[32-1:0] fetch_data, // Fetch data
    output logic fetch_data_ready, // Received data from cache
    /* F1 <-> Dec */
    output fetch_data_t fetch_o,
    output logic        fetch_o_valid,
    input logic         fetch_o_ready,
    // Squash intf
    squash_if.slave  squash_io
);
    // Send to cache
    logic [XLEN-1:0] pc_q, pc_d;
    bp_t prediction_0;

    typedef struct packed {
        pc_t pc; // TODO fetch addr
        logic allocated;
        logic killed;
        bp_t bp;
    } shr_icache_t;

    // TODO double buffer requests to symplify reeadyness
    // and overlap 2 cycles ? (fow now assume 1 cycle => 1 buffer)
    //      with critical readyness...
    shr_icache_t outstanding_req_q, outstanding_req_d;

    logic emmit_fetch;
    assign emmit_fetch = fetch_addr_ready && fetch_o_ready;
    
    assign outstanding_req_d.pc         = pc_q;
    assign outstanding_req_d.allocated  = emmit_fetch;
    assign outstanding_req_d.killed     = squash_io.valid;
    assign outstanding_req_d.bp         = prediction_0;

    assign fetch_addr_valid             = emmit_fetch; // Always req when ready
    assign fetch_addr                   = pc_q;

    // Compute next pc
    bpred bpred (
        .clk(clk),
        .rstn(rstn),
        .valid(fetch_addr_valid), // Always predict
        .ready(fetch_o_ready),
        .pc(pc_q),
        .prediction_0(prediction_0),
        .squash_io(squash_io)
    );

    assign pc_d = prediction_0.pcnext;

    always_ff @(posedge clk) begin
        if(!rstn) begin
            pc_q <= 64'h8000_0000;
            outstanding_req_q <= '0;
        end else begin
            outstanding_req_q <= outstanding_req_d;
            if(squash_io.valid) begin
                pc_q <= squash_io.resolved_pc;
            end else begin 
                if(emmit_fetch) begin
                    // Not stalled (PC issued to memory)
                    pc_q <= pc_d;
                end
            end
        end
    end

    assign fetch_o.pc    = outstanding_req_q.pc;
    assign fetch_o.bp    = outstanding_req_q.bp;
    assign fetch_o_valid = !outstanding_req_q.killed &&
                           fetch_data_valid;
    assign fetch_o.data  = fetch_data;
    assign fetch_data_ready = 1'b1; // ?
endmodule

