/* Main system */
/* Must be ASIC ready */

module system #() (
  input  logic clk,
  input  logic rstn,
  output logic exit_o,
  output logic [C::XLEN-1:0] exit_code_o
);

  initial begin
      log_init();
      `LOG(COMMIT, "Hello from logger");
  end

  always @(posedge clk) begin
    #0 `LOG(PIPE, "======================================== #0 posedge ========================================");
  end

  always @(negedge clk) begin
    #0 `LOG(PIPE, "======================================== #0 negedge ========================================");
  end
  
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

  // Retrieves addresses
  xlen_t raddr, waddr;
  logic  rv, wv;
  assign rv = dcache_ports_io.load_a_valid;
  assign wv = dcache_ports_io.wvalid;
  assign raddr = dcache_ports_io.load_a_addr;
  assign waddr = dcache_ports_io.waddr;
  logic[XLEN-1-3:0] raddrw, waddrw;
  assign raddrw = raddr[XLEN-1:3];
  assign waddrw = waddr[XLEN-1:3];
  /* Addr splitter */
  logic uart_rvalid, mem_rvalid;
  logic uart_wvalid, mem_wvalid;
  assign uart_rvalid = rv && raddr >= RANGES_UART_BASE && raddr < RANGES_UART_END; // TODO
  assign mem_rvalid  = rv && raddr >= RANGES_MEM_BASE  && raddr < RANGES_MEM_END;
  assign uart_wvalid = wv && waddr >= RANGES_UART_BASE && waddr < RANGES_UART_END; // TODO
  assign mem_wvalid  = wv && waddr >= RANGES_MEM_BASE  && waddr < RANGES_MEM_END;
  /* Save current request */
  logic uart_rvalid_q, mem_rvalid_q;
  logic uart_wvalid_q, mem_wvalid_q;
  xlen_t raddr_q, waddr_q;
  always_ff @(posedge clk) begin
    uart_rvalid_q  <= uart_rvalid;
    mem_rvalid_q <= mem_rvalid;
  end

  always_ff @(negedge clk) begin 
    if(dcache_ports_io.wvalid) begin
      `LOG(MEM, "MEM STORES @=%x, D=%x, MASK=%x (MAP: %s)",
        dcache_ports_io.waddr, dcache_ports_io.wdata,
        dcache_ports_io.wmask,
          uart_wvalid ? "UART" :
          mem_wvalid  ? "MEM"  : "BAD_ADDR"
        );
    end
    if (dcache_ports_io.load_d_valid) begin
      `LOG(MEM, "MEM LOAD ... returns D=%x (MAP: %s)",
          dcache_ports_io.load_d_data,
          uart_rvalid_q ? "UART" :
          mem_rvalid_q  ? "MEM"  : "BAD_ADDR"
        );
    end
    if(dcache_ports_io.load_a_valid) begin
      `LOG(MEM, "MEM LOAD @=%x (MAP: %s) returns ...",
        dcache_ports_io.load_a_addr,
          uart_rvalid ? "UART" :
          mem_rvalid  ? "MEM"  : "BAD_ADDR"
        );
    end
  end

  xlen_t        mem_rata;
  xlen_t        uart_rdata;
  
  logic [8-1:0] uart_rdata8;
  assign uart_rdata = {8{uart_rdata8}};

  uart8250 uart8250 (
    .clk(clk),
    .rstn(rstn),
    .rvalid(uart_rvalid),
    .raddr(raddr[2:0]),
    .rdata(uart_rdata8),
    // Write port
    .wvalid(uart_wvalid),
    .waddr(waddr[2:0]),
    .wdata(dcache_ports_io.wdata[8-1:0])
  );

  /* Fake Memory */
  sram2r1w #(
    .ADDR_WIDTH(MEM_ADDR_WIDTH - 3),
    .DATA_WIDTH(64)
  ) simram (
    .clk(clk),
    // 1 read port for fetch
    .raddr(fetch_addr[MEM_ADDR_WIDTH-1:3]),
    .rdata(fetch_data64),
    // 1 read port for load
    .raddr2(dcache_ports_io.load_a_addr[MEM_ADDR_WIDTH-1:3]),
    .rdata2(mem_rata),
    // 1 write port for stores
    .we(mem_wvalid),
    .waddr(dcache_ports_io.waddr[MEM_ADDR_WIDTH-1:3]),
    .wdata(dcache_ports_io.wdata),
    .wmask(dcache_ports_io.wmask)
  );

  assign dcache_ports_io.load_d_data = uart_rvalid_q ? uart_rdata :
                                       mem_rvalid_q  ? mem_rata :
                                       64'hbadabadabadabada;

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
