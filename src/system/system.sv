/* Main system */
/* Must be ASIC ready */

module system #() (
  input  logic clk,
  input  logic rstn,
  output logic exit_o,
  output logic [C::XLEN-1:0] exit_code_o
);

  logic [C::XLEN-1:0] fetch_addr;
  logic [32-1:0] fetch_data;

  parameter unsigned ADDR_WIDTH = 20;
  
  logic fetch_addr_valid, fetch_addr_ready;
  logic fetch_data_valid, fetch_data_ready;
   
  core #() core (
    .clk(clk),
    .rstn(rstn),
    .fetch_addr_ready(fetch_addr_ready),
    .fetch_addr_valid(fetch_addr_valid),
    .fetch_addr(fetch_addr),
    .fetch_data_valid(fetch_data_valid),
    .fetch_data(fetch_data),
    .fetch_data_ready(fetch_data_ready),
    .exit_o(exit_o),
    .exit_code_o(exit_code_o)
  );

  /* Fake Memory */
  sram1rw #(
    .ADDR_WIDTH(ADDR_WIDTH),
    .DATA_WIDTH(32)
  ) simram (
    .clk(clk),
    .we(1'b0),
    .addr(fetch_addr[ADDR_WIDTH-1+2:2]),
    .wdata(32'b0),
    .rdata(fetch_data)
  );
  // SRAM always valid (1 cycle latency)
  always_ff @(posedge clk) begin
    if(!rstn) begin
      fetch_data_valid <= 0;
      fetch_addr_ready <= 0;
    end else  begin
      fetch_data_valid <= fetch_addr_valid;
      fetch_addr_ready <= 1'b1; // Sram always realy
    end
  end

endmodule
