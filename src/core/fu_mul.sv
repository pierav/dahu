
import C::*;

module fu_mul #(
    parameter int PIPE_OUT = 2 // Number of pipe stages
) (
    input  logic                 clk,
    input  logic                 rstn,
    input  fu_input_t            fuinput_i,
    input  logic                 fuinput_i_valid,
    output logic                 fuinput_i_ready,
    output fu_output_t           fuoutput_o,
    output logic                 fuoutput_o_valid,
    squash_if.slave              squash_io
);
    arith_mul_base  #(
        .PIPE_OUT(PIPE_OUT)
    ) arith_mul_base (
        .clk(clk),
        .rstn(rstn),
        .fuinput_i(fuinput_i),
        .fuinput_i_valid(fuinput_i_valid),
        .fuinput_i_ready(fuinput_i_ready),
        .fuoutput_o(fuoutput_o),
        .fuoutput_o_valid(fuoutput_o_valid),
        .squash(squash_io.valid)
    );

endmodule

