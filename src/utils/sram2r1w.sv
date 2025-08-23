module sram2r1w #(
  parameter ADDR_WIDTH = 8,
  parameter DATA_WIDTH = 32
)(
  input  logic                   clk,
  input  logic [ADDR_WIDTH-1:0] raddr,    // Read address 1
  output logic [DATA_WIDTH-1:0] rdata,    // Read data 1
  input  logic [ADDR_WIDTH-1:0] raddr2,   // Read address 2
  output logic [DATA_WIDTH-1:0] rdata2,   // Read data 2
  input  logic                   we,      // Write enable
  input  logic [ADDR_WIDTH-1:0] waddr,    // Write address
  input  logic [DATA_WIDTH-1:0] wdata,    // Write data
  input  logic [DATA_WIDTH/8-1:0] wmask   // Write mask: one bit per byte
);

  // Memory array
  logic [DATA_WIDTH-1:0] mem [(2**ADDR_WIDTH)-1:0];

  // Synchronous read and write with byte masking
  always_ff @(posedge clk) begin
    // Write with mask
    if (we) begin
      for (int i = 0; i < DATA_WIDTH/8; i++) begin
        if (wmask[i])
          mem[waddr][8*i +: 8] <= wdata[8*i +: 8];
      end
    end

    // Reads (synchronous)
    rdata  <= mem[raddr];
    rdata2 <= mem[raddr2];
  end
endmodule
