
import C::*;

module fu_div #(
    parameter int WIDTH = 64,
    parameter int BPC   = 8
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

    parameter logic [WIDTH-1:0] DIV_INT_MIN = (1 << (WIDTH-1));
    parameter logic [WIDTH-1:0] DIV_INT_M1 = '1;
    
    typedef enum logic [1:0] {IDLE, RUN, DONE} state_e;

    typedef struct packed {
        pc_t pc;
        id_t id;
        preg_id_t prd;
    } fu_save_t;

    // At init: initialise those fields
    fu_save_t save_q;
    div_set_t op_q;
    logic     neg_a_q, neg_b_q;
    logic     isword_q;
    
    // datapath
    state_e           state_q;
    logic [WIDTH-1:0] dividend_q, divisor_q;
    logic [WIDTH-1:0] quo_q, rem_q;
    int               bit_index_q;

    // final result
    logic [WIDTH-1:0] result_q;
    logic             result_fast_valid_q;

    /* First pass: perform sign extension */    
    logic [WIDTH-1:0] a;
    logic [WIDTH-1:0] b;

    logic is_signed_i;
    assign is_signed_i = fuinput_i.op.div inside {DIV, REM};
    assign a = fuinput_i.size == SIZE_D ? fuinput_i.rs1val :
                                          ext32to64(fuinput_i.rs1val[32-1:0], is_signed_i);
    assign b = fuinput_i.size == SIZE_D ? fuinput_i.rs2val:
                                          ext32to64(fuinput_i.rs2val[32-1:0], is_signed_i);

    always_ff @(posedge clk) begin
        if (!rstn) begin
            state_q            <= IDLE;
        end else if (squash_io.valid) begin
            state_q            <= IDLE;
        end else begin
            unique case (state_q)
                IDLE: begin
                    if (fuinput_i_valid) begin
                        // save things
                        save_q.pc   <= fuinput_i.pc;
                        save_q.id   <= fuinput_i.id;
                        save_q.prd  <= fuinput_i.prd;
                        op_q        <= fuinput_i.op.div;
                        isword_q    <= fuinput_i.size == SIZE_W;
                        // Handle corner cases here
                        if (b == '0) begin
                            unique case (fuinput_i.op.div)
                                DIV, DIVU: result_q <= '1; // -1
                                REM, REMU: result_q <= a;
                            endcase
                            result_fast_valid_q <= 1'b1;
                            state_q <= DONE;
                        end else if ((fuinput_i.op == DIV) &&
                                     (a == DIV_INT_MIN) &&
                                     (b == DIV_INT_M1)) begin
                            // signed overflow: INT_MIN / -1
                            result_q            <= '1;
                            result_fast_valid_q <= 1'b1;
                            state_q        <= DONE;
                        end else begin
                            neg_a_q    <= a[WIDTH-1];
                            neg_b_q    <= b[WIDTH-1];
                            if (fuinput_i.op == DIV || fuinput_i.op == REM) begin
                                // signed: take absolute values
                                dividend_q <= a[WIDTH-1] ? (~a + 1) : a;
                                divisor_q  <= b[WIDTH-1] ? (~b + 1) : b;
                            end else begin
                                dividend_q <= a;
                                divisor_q  <= b;
                            end
                            quo_q       <= '0;
                            rem_q       <= '0;
                            bit_index_q <= WIDTH-1;
                            state_q     <= RUN;
                            result_fast_valid_q <= 1'b0;
                        end
                    end else begin
                        result_fast_valid_q <= 1'b0;
                    end
                end

                RUN: begin
                    // iterative unsigned division (multi-bit per cycle)
                    int iter;
                    logic [WIDTH-1:0] q = quo_q;
                    logic [WIDTH-1:0] r = rem_q;
                    int next_bit = bit_index_q;

                    for (iter = 0; iter < BPC; iter++) begin
                        if (next_bit >= 0) begin
                            r = {r[WIDTH-2:0], dividend_q[next_bit]};
                            if (r >= divisor_q) begin
                                r = r - divisor_q;
                                q[next_bit] = 1'b1;
                            end
                            next_bit -= 1;
                        end
                    end
                    quo_q <= q;
                    rem_q <= r;
                    bit_index_q <= next_bit;
                    if (next_bit < 0) begin
                        state_q <= DONE;
                    end
                end

                DONE: begin
                    // TODO use internals buffer to delay bypass
                    state_q <= IDLE;
                end
            endcase
        end
    end

    // TODO Let thoses computations inside the bypass cycle ? 
    xlen_t rfinal;
    always_comb begin
        rfinal = '0;
        if (result_fast_valid_q) begin
            rfinal = result_q; // TODO Recycle rem_q ?
        end else begin
            unique case (op_q)
                DIV:  rfinal = (neg_a_q ^ neg_b_q) ? (~quo_q + 1) : quo_q;
                REM:  rfinal = neg_a_q ? (~rem_q + 1) : rem_q;
                DIVU: rfinal = quo_q;
                REMU: rfinal = rem_q;
            endcase
        end
        if(isword_q) begin
            rfinal = ext32to64(rfinal[32-1:0], 
                op_q inside {DIV, REM});
        end
    end

    // outputs
    assign fuoutput_o_valid = state_q == DONE;
    assign fuoutput_o.pc    = save_q.pc;
    assign fuoutput_o.id    = save_q.id;
    assign fuoutput_o.prd   = save_q.prd;
    assign fuoutput_o.rdval = rfinal;
    assign fuinput_i_ready  = state_q == IDLE;

endmodule
