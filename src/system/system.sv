/* Main system */
/* Must be ASIC ready */

module system #() (
  input  logic clk,
  input  logic rstn,
  output logic exit_o,
  output logic [C::XLEN-1:0] exit_code_o
);
  initial begin
    $display("Hello from system");
    exit_o      = 0;
    exit_code_o = 0;

    repeat (20) @(posedge clk);
    exit_o      = 1;
    exit_code_o = 42;
  end

  always_ff @(posedge clk) begin
    $display($time, ": rstn = %d exit_o = %d", rstn, exit_o);
  end
endmodule
