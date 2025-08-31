import C::*;


module decode #() (
    input clk,
    input rstn,
    input fetch_data_t in_i,  // Instruction to process
    input logic in_i_valid,  // Instruction to process is here
    output logic in_i_ready, // Ready to decode new one
    output di_t di_o,        // The renammed instruction 
    output logic di_o_valid, // The instruction is renammed
    input logic di_o_ready,   // The next stage is ready
    // To BQ
    bq_push_if.master bq_push_io,
    // Squash intf
    squash_if.slave  squash_io

);
    bp_t bp_i;
    assign bp_i = in_i.bp;

    si_t decode_si;
    /* Decode */
    static_decoder #() sdecoder (
        .pc_i(in_i.pc),
        .data_i(in_i.data),
        .si_o(decode_si)
    );

    /* JAL uop decomposition */
    /* It's mandatory to split jal and jalr because the branch unit 
     * cannot wb instructions.
     * Also, the branch unit do now own an adder to do PC + 4;
     * So, it's simpler to split jal and jalr here in 2 uop:
     * INPUT:
     *      - jal[r] rd, [imm|rs1]
     * OUTPUT:
     *      1) auipc rd, 4
     *      2) j[r] rd, [imm|rs1]
     *
     * When decomposing into multiple µops,
     * pass the captured source mappings of the original instruction
     * to the first generated uop.
     *
     * For JALR:
     * -  Save prs1 at AUIPC rename entry.
     * -  Attach oldprs1 to the branch µop,
     *    even if the RMT has been updated in the meantime.
     *
     * This avoids dependence on exact RMT update timing.
     */

    RV::utype_t auipccode;
    always_comb begin
        auipccode = 32'h00004097; // auipc ra, 4 :) (A bit hacky...)
        auipccode.rd = decode_si.rd;
    end
    si_t uop_extra_q, conv_uop_0;
    logic uop_extra_valid_q, uop_extra_valid_d;
    assign conv_uop_0.pc       = decode_si.pc;
    assign conv_uop_0.tinst    = auipccode;
    assign conv_uop_0.fu       = FU_ALU;
    assign conv_uop_0.op       = AUIPC;
    assign conv_uop_0.rs1      = decode_si.rs1; // Force valid read of the RMT
    assign conv_uop_0.rs1_valid= '0;
    assign conv_uop_0.rs2      = '0;
    assign conv_uop_0.rs2_valid= '0;
    assign conv_uop_0.rd       =  decode_si.rd;
    assign conv_uop_0.rd_valid = '1; // Otherwise, why create uop...
    assign conv_uop_0.imm      =  4; // Do PC + 4 :)
    assign conv_uop_0.use_uimm = '0;
    assign conv_uop_0.size     = SIZE_D;
    assign conv_uop_0.valid    = '1;

    logic is_jal_or_jalr;
    logic is_trig_uop_jal;
    assign is_jal_or_jalr = decode_si.fu == FU_CTRL &&
                            decode_si.op inside { JAL, JALR };
    assign is_trig_uop_jal = in_i_valid &&
                             is_jal_or_jalr && 
                             decode_si.rd_valid; // Avoid useless uop for x0 W
    // TODO back to back jal ?

    /* Arbitration between uop and decoded op */
    // FETCH || DEC  || RE
    //==========================
    //  JAL  ||      ||
    //  ADDI || UOP  || 
    //    O  || JAL  || UOP
    //       || ADDI || JAL
    //       ||      || ADDI

    logic push_uop;
    assign push_uop = di_o_ready && is_trig_uop_jal;
    // backup the generated uops
    always_ff @(posedge clk) begin
        if(!rstn) begin
            uop_extra_q <= '0;
            uop_extra_valid_q <= '0;
        end else begin
            if (squash_io.valid) begin
                uop_extra_q <= '0;
                uop_extra_valid_q <= '0;
            end else begin
                if(push_uop) begin
                    uop_extra_q <= decode_si; // Do the jalr after the auipc
                end
                uop_extra_valid_q <= 
                    push_uop ? '1 :
                    di_o_ready ? '0 : uop_extra_valid_q;
            end
        end
    end


    // uop selection 
    si_t uop_si;
    logic uop_si_valid;

    logic is_uop;
    logic is_uop_last;
    RV::jtype_t tinst;
    always_comb begin
        tinst = '0;
        if (uop_extra_valid_q) begin // conv 1 uop (PRIORITARY over uop0)
            uop_si          = uop_extra_q;
            // Do not handle RD here (no need to rename and wb here)
            // This wb is alreayd done in conv 0
            uop_si.rd_valid = '0;
            uop_si.rd       = '0; // x0 
            uop_si_valid    = '1;
            tinst = uop_extra_q.tinst; // for the dpi tracer: create fake inst
            tinst.rd = '0; // x0
            uop_si.tinst = tinst;
        end else if (push_uop) begin // When detected use conv 0 uop
            uop_si          = conv_uop_0;
            uop_si_valid    = '1;
        end else begin // Otherwise use input
            uop_si          = decode_si;
            uop_si_valid    = in_i_valid;
        end
    end

    assign is_uop = uop_extra_valid_q || push_uop;
    assign is_uop_last = uop_extra_valid_q;

    // We have to stall 1 cycle the previous stage.
    // Insert the bubble as late as possible ? 
    // In this way the pipe buffer will be filler ?
    assign in_i_ready = di_o_ready && !uop_extra_valid_q; // D or Q ?


    logic is_fault;
    dynamic_decoder_fault ddecoder (
        .clk(clk),
        .rstn(rstn),
        .si_i(uop_si),
        .fs_i(RV::XS_OFF),
        .priv_lvl_i(RV::PRIV_LVL_M),
        .frm_i(3'b0),
        .tvm_i(1'b0),
        .tw_i(1'b0),
        .tsr_i(1'b0),
        .debug_mode_i(1'b0),
        .is_fault_o(is_fault)
    );

    // TODO Stall allocation sq, lq
    id_t inst_id_q;
    always_ff @(posedge clk) begin
        if(!rstn) begin
            inst_id_q <= '0;
        end else begin
            if (squash_io.valid) begin
                // Reset to the expected id
                inst_id_q <= squash_io.id + 1; 
            end else begin
                if(uop_si_valid && di_o_ready) begin
                    inst_id_q <= inst_id_q + 1;
                end
            end
        end
    end

    /* Direct branch resolution */
    logic isBranch, isDirectBranch, isIndirectBranch, isUncondBranch;
    assign isBranch = uop_si.fu == FU_CTRL;
    assign isDirectBranch = isBranch &&
        uop_si.op inside { BLT, BLTU, BGE, BGEU, BEQ, BNE, JAL };
    assign isIndirectBranch = isBranch &&
        uop_si.op inside { JALR };

    /* Direct Branch computation */
    pc_t direct_branch_target;
    assign direct_branch_target = in_i.pc + uop_si.imm; // J or B imm ?

    logic misspredict_direct;
    assign misspredict_direct = isDirectBranch &&
                                bp_i.taken &&
                                bp_i.pcnext != direct_branch_target;

    // TODO resolve direct branch missprediction here !
    // TODO latch bpred ?
    assign bq_push_io.bp = bp_i;
    assign bq_push_io.pc = di_o.si.pc;
    assign bq_push_io.id = di_o.id;
    assign bq_push_io.valid = isBranch && uop_si_valid && di_o_ready; // Push only one time

    /* Output instruction to next stage */
    always_comb begin : output_process
        di_o = '0; // base assignement 
        di_o.si     = uop_si;
        di_o.bqid   = isBranch ? bq_push_io.bqid : '0;
        di_o.id     = inst_id_q;
        di_o.fault  = is_fault;
        di_o.is_uop = is_uop;
        di_o.is_uop_last = is_uop_last;
    end
    assign di_o_valid = uop_si_valid; // Cannot stall

    // TODO BQ full
    // logic stall;
    // assign stall = 
    /* Ready valid */

    always_ff @(posedge clk) begin
        if(!di_o_ready) begin
            `LOG(DEC, "Decode: (port0) next stage not ready");
        end else if(!in_i_valid) begin
            `LOG(DEC, "Decode: (port0) no valids inputs");
        end else begin
            `LOG(DEC, "Decode: (port0) %s: pc %x (sn=%x) %s <- %s %s | imm=%x (%s%s)",
                di_o_valid ?  "SUCCESS " : "FAILURE",
                di_o.si.pc, di_o.id,
                di_o.si.rs1_valid ? dumpAReg(di_o.si.rs1) : "",
                di_o.si.rs2_valid ? dumpAReg(di_o.si.rs2) : "",
                di_o.si.rd_valid ? dumpAReg(di_o.si.rd) : "",
                di_o.si.imm,
                push_uop ? "Use UOP0" : "",
                uop_extra_valid_q ? "Use UOP1": "");
        end
    end

    // assert property (
    //     @(posedge clk) disable iff (!rstn)
    //         in_i_valid |-> di_o.si.valid
    // );

endmodule

