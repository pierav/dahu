/* Main system */
/* Must be ASIC ready */

module system #() (
  input  logic clk,
  input  logic rstn,
  output logic exit_o,
  output logic [C::XLEN-1:0] exit_code_o
);

  logic [C::XLEN-1:0] fetch_addr;
  logic [32-1:0]      fetch_data;
  logic [C::XLEN-1:0] fetch_data64;
  logic               fetch_bo_q;

  parameter unsigned ADDR_WIDTH = 20;
  
  dcache_ports_if dcache_ports_io();

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
    .exit_code_o(exit_code_o),
    .dcache_ports_io(dcache_ports_io)
  );

  // // Fake write port TODO
  assign dcache_ports_io.wready = '1;

  // Fake sram read port TODO
  assign dcache_ports_io.load_a_ready = '1;
  always_ff @(posedge clk) begin 
    dcache_ports_io.load_d_valid <= dcache_ports_io.load_a_valid;
    fetch_bo_q <= fetch_addr[2];
  end

  always_ff @(negedge clk) begin 
    if(dcache_ports_io.wvalid) begin
      $display("MEM STORES @=%x, D=%x, MASK=%x",
        dcache_ports_io.waddr, dcache_ports_io.wdata,
        dcache_ports_io.wmask);
    end
    if (dcache_ports_io.load_d_valid) begin
      $display("MEM LOAD ... returns D=%x",
        dcache_ports_io.load_d_data);
    end
    if(dcache_ports_io.load_a_valid) begin
      $display("MEM LOAD @=%x, returns ...",
        dcache_ports_io.load_a_addr);
    end

  end

  /* Fake Memory */
  sram2r1w #(
    .ADDR_WIDTH(ADDR_WIDTH),
    .DATA_WIDTH(64)
  ) simram (
    .clk(clk),
    // 1 read port for fetch
    .raddr(fetch_addr[ADDR_WIDTH-1+3:3]),
    .rdata(fetch_data64),
    // 1 read port for load
    .raddr2(dcache_ports_io.load_a_addr[ADDR_WIDTH-1+3:3]),
    .rdata2(dcache_ports_io.load_d_data),
    // 1 write port for stores
    .we(dcache_ports_io.wvalid),
    .waddr(dcache_ports_io.waddr[ADDR_WIDTH-1+3:3]),
    .wdata(dcache_ports_io.wdata),
    .wmask(dcache_ports_io.wmask)
  );
  // Select word
  assign fetch_data = fetch_bo_q ? fetch_data64[63:32] : fetch_data64[31:0];

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
