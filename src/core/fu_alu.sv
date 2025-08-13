
module fu_alu #() (
    input logic clk,
    input logic rstn,
    input fu_input_t fuinput_i,
    output fu_output_t fuoutput_o
); 
    /*** Retrieve inputs ***/
    logic[XLEN-1:0] opa64, opb64;
    logic[32-1:0] opa32, opb32;
    logic[5:0] shift_amt;
    logic isword;
    assign isword = fuinput_i.op inside {ADDW, SUBW, SRLW, SLLW, SRAW};
    assign opa64 = fuinput_i.rs1val;
    assign opb64 = fuinput_i.rs2val;
    assign opa32 = opa64[32-1:0];
    assign opb32 = opb64[32-1:0];
    assign shift_amt = fuinput_i.imm[5:0];
    
    /*** Generic adder ***/
    logic negate;
    logic [XLEN-1+1+1:0] adder_opa, adder_opb, adder_res66;
    logic [32-1:0] adder_res32;
    logic [XLEN-1:0] adder_res64, adder_res32sext;
    logic [XLEN-1:0] adder_final_result;
    logic needneg;
    logic adder_isneg;
    logic adder_islt;
    // First layer: conditioning (0 for cmp, 1 for substraction)
    assign needneg              = fuinput_i.op inside {SUB, SUBW, SLT, SLTU};
    assign adder_opa            = {1'b0, opa64, 1'b1};
    assign adder_opb            = {1'b0, opb64, 1'b0} ^ {XLEN+1+1{needneg}};
    // Mid layers: perform addition
    assign adder_res66          = adder_opa + adder_opb;
    assign adder_res64          = adder_res66[XLEN-1+1:1];
    assign adder_res32          = adder_res64[32-1:0];
    assign adder_res32sext      = {{XLEN - 32{adder_res32[31]}}, adder_res32};
    // Last layer: uncondition + sext
    assign adder_final_result   = isword ? adder_res32sext : adder_res64;
    logic slt_res_signed        = adder_res64[XLEN-1]; // sign bit
    logic slt_res_unsigned      = adder_res66[XLEN+1]; // carry-out

    /*** Barrel shifter ***/
    logic[XLEN-1:0] res64, res32sext, shifter_final_result;
    logic[32-1:0]   res32;
    logic[XLEN-1:0] opa64_rev, shift_opa64, shift_res64, shift_res64_rev;
    logic[32-1:0]   opa32_rev, shift_opa32, shift_res32, shift_res32_rev;
    logic [XLEN-1+1:0]  shift_opa65, shift_res65;
    logic [32-1+1:0]    shift_opa33, shift_res33;
    logic shift_l, shift_a;
    // Retrieve inputs
    assign shift_l              = fuinput_i.op inside {SLL, SLLW};
    assign shift_a              = fuinput_i.op inside {SRA, SRAW};
    // First layer : fix inputs for (left or arthiemtic shifts)
    assign opa64_rev            = {<<{opa64}}; // Reverse bits
    assign opa32_rev            = {<<{opa32}};
    assign shift_opa64          = shift_l ? opa64_rev : opa64;
    assign shift_opa32          = shift_l ? opa32_rev : opa32;
    // Add an extra bit to sign extend
    assign shift_opa65          = {shift_a & shift_opa64[XLEN-1], shift_opa64};
    assign shift_opa33          = {shift_a & shift_opa32[32-1], shift_opa32};
    // Mid layers : perform the shift  
    assign shift_res65          = $unsigned($signed(shift_opa65) >>> shift_amt[5:0]);
    assign shift_res33          = $unsigned($signed(shift_opa33) >>> shift_amt[4:0]);
    assign shift_res64          = shift_res65[XLEN-1:0];
    assign shift_res32          = shift_res33[32-1:0];
    // Last layer : fit output for left shift
    assign shift_res64_rev      = {<<{shift_res64}}; // Reverse bits
    assign shift_res32_rev      = {<<{shift_res32}};
    assign res64                = shift_l ? shift_res64_rev : shift_res64;
    assign res32                = shift_l ? shift_res32_rev : shift_res32;
    assign res32sext            = {{XLEN - 32{res32[31]}}, res32};
    assign shifter_final_result = isword ? res32sext : res64;

    // TODO assert not shift_l and shift_a

    /* Final selection */
    logic [XLEN-1:0] result;
    always_comb begin
        result = '0;
        unique case (fuinput_i.op.alu) // use alu set to avoid incomplteness
            ADD, SUB, ADDW, SUBW, LUI, AUIPC: 
                result = adder_final_result;
            SLL, SRL, SRA, SLLW, SRLW, SRAW: 
                result = shifter_final_result;
            AND:
                result = opa64 & opb64;
            OR:
                result = opa64 | opb64;
            XOR:
                result = opa64 ^ opb64;
            SLT:
                result = XLEN'(slt_res_signed);
            SLTU: 
                result = XLEN'(slt_res_unsigned);
        endcase
    end

    /* Output */
    assign fuoutput_o.pc    = fuinput_i.pc;
    assign fuoutput_o.id    = fuinput_i.id;
    assign fuoutput_o.prd   = fuinput_i.prd;
    assign fuoutput_o.rdval = result;

endmodule
