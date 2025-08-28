
import C::*;

module fu_mul #(
    parameter int PIPE_OUT = 2 // Number of pipe stages
    // TODO 1) try retiming
    // TODO 2) PIPE_IN ?
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

    xlen_t a, b;
    assign a = fuinput_i.op.mul != MULW ? fuinput_i.rs1val :
                                          sext32to64(fuinput_i.rs1val[32-1:0]);
    assign b = fuinput_i.op.mul != MULW  ? fuinput_i.rs2val:
                                          sext32to64(fuinput_i.rs2val[32-1:0]);

    logic sa, sb;
    assign sa = a[XLEN-1] & fuinput_i.op.mul inside {MULH, MULHSU};
    assign sb = b[XLEN-1] & fuinput_i.op.mul inside {MULH};

    logic [XLEN*2-1:0] val_d;
    assign val_d = $signed({sa, a}) * $signed({sb, b});

    typedef struct packed {
        pc_t pc;
        id_t id;
        mul_set_t op;
        preg_id_t prd;
        logic [XLEN*2-1:0] val; // TODO 64 or 128
        logic valid;
    } mult_pipe_entry_t;

    mult_pipe_entry_t pipe_input;
    mult_pipe_entry_t pipe_output;
    mult_pipe_entry_t pipe_q [PIPE_OUT]; // Output pipeline
    assign pipe_output = pipe_q[0];

    assign pipe_input.pc = fuinput_i.pc;
    assign pipe_input.id = fuinput_i.id;
    assign pipe_input.op = fuinput_i.op.mul;
    assign pipe_input.prd = fuinput_i.prd;
    assign pipe_input.valid = fuinput_i_valid;
    assign pipe_input.val = val_d;

    always_ff @(posedge clk) begin
        if(!rstn) begin
            for(int i = 0; i < PIPE_OUT; i++) begin
                pipe_q[i].valid <= '0;
            end
        end else begin
            if(squash_io.valid) begin
                for(int i = 0; i < PIPE_OUT; i++) begin
                    pipe_q[i].valid <= '0;
                end
            end else begin 
                for(int i = 0; i < PIPE_OUT-1; i++) begin
                    pipe_q[i] <= pipe_q[i+1];
                end
                pipe_q[PIPE_OUT-1] <= pipe_input;
            end
        end
    end

    xlen_t rdval;
    always_comb begin
        rdval = '0;
        unique case (pipe_output.op)
            MULH,
            MULHU,
            MULHSU: rdval = pipe_output.val[XLEN*2-1:XLEN];
            MULW:   rdval = sext32to64(pipe_output.val[32-1:0]);
            MUL:    rdval = pipe_output.val[XLEN-1:0];
        endcase
    end
    
    // outputs
    assign fuoutput_o_valid = pipe_output.valid;
    assign fuoutput_o.pc    = pipe_output.pc;
    assign fuoutput_o.id    = pipe_output.id;
    assign fuoutput_o.prd   = pipe_output.prd;
    assign fuoutput_o.rdval = rdval;
    assign fuinput_i_ready  = '1; // Always ready (Pipelined)
    // TODO as int divider user pipe out to kackup wb ports

endmodule

