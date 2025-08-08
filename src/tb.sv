/* Minimal test bench */
/* Unused with verilator ! TODO setup for questa simulation */

module tb;
  localparam int unsigned CLOCK_PERIOD = 10ns;
  longint unsigned cycles;

  logic clk;
  logic rstn;
  logic exit_o;
  logic [C::XLEN-1:0] exit_code_o;

  system #() dut (
    .clk,
    .rstn,
    .exit_o,
    .exit_code_o
  );

  /* Clock generation */
  initial forever #(CLOCK_PERIOD/2) clk = ~clk;

  /* Reset generation */
  initial begin
    rstn = 0;                // Assert reset (active low)
    repeat (5) @(posedge clk); // Hold reset asserted for 5 cycles
    rstn = 1;                // Deassert reset
  end

  always_ff @(posedge clk) begin
    cycles <= cycles + 1;
  end

  /* Simulation termination */
  always_ff @(posedge clk) begin
    if (exit_o) begin
      if (exit_code_o != 0) begin
          $display("FAILURE (cycle %d): exitcode: %d", cycles, exit_code_o);
      end else begin
          $display("SUCCESS: elaplsed cycles: %d", cycles);
      end
      $finish();
    end
  end

endmodule
