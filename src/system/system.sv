/* Main system */
/* Must be ASIC ready */

module system #() (
  input  logic clk,
  input  logic rstn,
  output logic exit_o,
  output logic [C::XLEN-1:0] exit_code_o
);

  logic [C::XLEN-1:0] rdata;
  logic [20-1:0] addr_q, addr_d;
  logic [20-1:0] addr_q_buf;

  sram1rw #(
    .ADDR_WIDTH(20),
    .DATA_WIDTH(C::XLEN)
  ) simram (
    .clk,
    .we(0),
    .addr(addr_q),
    .wdata(0),
    .rdata
  );

  always_comb begin
    addr_d = addr_q + 1;
  end

  always_ff @(posedge clk) begin
    if(!rstn) begin
      addr_q <= 0;
      addr_q_buf <= 0;
    end else begin
      addr_q_buf <= addr_q;
      addr_q <= addr_d;
    end
    // $display($time, ": mem[%x]=%x", addr_q_buf, rdata);
  end



  initial begin
    $display("Hello from system");
    exit_o      = 0;
    exit_code_o = 0;

    repeat (1000000) @(posedge clk);
    exit_o      = 1;
    exit_code_o = 42;
  end

  always_ff @(posedge clk) begin
    // $display($time, ": rstn = %d exit_o = %d", rstn, exit_o);
  end
endmodule
