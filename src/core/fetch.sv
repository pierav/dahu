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
    output logic fetch_o_valid,
    input logic fetch_o_ready
);
    // Send to cache
    logic [XLEN-1:0] pc_q, pc_d;
    logic [XLEN-1:0] pq_buff_q, pc_buff_d;

    assign fetch_addr_valid = fetch_addr_ready; // Always req when ready
    assign fetch_addr = pc_q;
    assign pc_buff_d = pc_q;

    // Compute next pc
    assign pc_d = pc_q + 4;

    always_ff @(posedge clk) begin
        if(!rstn) begin
            pc_q <= 0;
            pq_buff_q <= 0;
        end else begin 
            // Not stalled (PC issued to memory)
            if(fetch_addr_valid && fetch_o_ready) begin
                pq_buff_q <= pc_buff_d;
                pc_q <= pc_d;
            end
        end
    end

    assign fetch_o.pc = pq_buff_q;
    assign fetch_o.data = fetch_data;
    assign fetch_o_valid = fetch_data_valid;

    assign fetch_data_ready = 1'b1; // ?
endmodule

