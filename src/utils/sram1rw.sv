module sram1rw #(
  parameter ADDR_WIDTH = 8,
  parameter DATA_WIDTH = 32
)(
  input  logic                   clk,
  input  logic                   we,       // Write enable
  input  logic [ADDR_WIDTH-1:0] addr,     // Address
  input  logic [DATA_WIDTH-1:0] wdata,    // Write data
  output logic [DATA_WIDTH-1:0] rdata     // Read data
);
  // Memory array
  logic [DATA_WIDTH-1:0] mem [(2**ADDR_WIDTH)-1:0];

  // Synchronous read and write
  always_ff @(posedge clk) begin
    if (we) begin
      mem[addr] <= wdata;
    end
    rdata <= mem[addr];
  end
endmodule
