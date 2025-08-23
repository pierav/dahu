module sram2r1w #(
  parameter ADDR_WIDTH = 8,
  parameter DATA_WIDTH = 32
)(
  input  logic                   clk,
  input  logic [ADDR_WIDTH-1:0] raddr,    // R Address
  output logic [DATA_WIDTH-1:0] rdata,    // Read data
  input  logic [ADDR_WIDTH-1:0] raddr2,    // R Address
  output logic [DATA_WIDTH-1:0] rdata2,    // Read data
  input  logic                  we,      // Write enable
  input  logic [ADDR_WIDTH-1:0] waddr,    // W Address
  input  logic [DATA_WIDTH-1:0] wdata     // Write data
);
  // Memory array
  logic [DATA_WIDTH-1:0] mem [(2**ADDR_WIDTH)-1:0];

  // Synchronous reads and write
  always_ff @(posedge clk) begin
    if (we) begin
      mem[waddr] <= wdata;
    end
    rdata <= mem[raddr];
    rdata2 <= mem[raddr2];
  end
endmodule
