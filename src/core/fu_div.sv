
module fu_div #() (
    input logic clk,
    input logic rstn,
    input fu_input_t fuinput_i,
    input logic      fuinput_i_valid,
    output logic      fuinput_i_ready,
    output fu_output_t fuoutput_o,
    output logic       fuoutput_o_valid,
    // Squash intf
    squash_if.slave  squash_io
);

    typedef struct packed{
        pc_t pc; // metadata
        id_t id; // metadata
        preg_id_t prd;
    } fu_save_t;
    
    fu_save_t save_q;
    logic div_done_q;

    always_ff @(posedge clk) begin
        if(!rstn) begin
            div_done_q <= '0; // ?? 
            // Nothing to clear now ?
        end
            if(squash_io.valid) begin
                div_done_q <= '0; // ?? 
                // Nothing to clear now ?
            end else begin
                if (fuinput_i_valid) begin
                    save_q.pc <= fuinput_i.pc;
                    save_q.id <= fuinput_i.id;
                    save_q.prd <= fuinput_i.prd;
                end
                // 1 cycle layency to stress wb now
                div_done_q <= fuinput_i_valid;
                if (fuinput_i_valid) begin
                    $warning("UNIMPLEMENTED DIV a=%x b=%x",
                        fuinput_i.rs1val, fuinput_i.rs2val);
                end
            end
    end

    assign fuoutput_o_valid = div_done_q;
    assign fuoutput_o.pc    = save_q.pc;
    assign fuoutput_o.id    = save_q.id;
    assign fuoutput_o.prd   = save_q.prd;
    assign fuoutput_o.rdval = 64'hdeadbeefdeadbeef;

    assign fuinput_i_ready  = '1; // TODO

endmodule
