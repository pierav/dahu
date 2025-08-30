import C::*;

module dynamic_decoder_fault #() (
    input clk,
    input rstn,

    input si_t si_i,

    /* Csr flags */
    input RV::xs_t fs_i,
    input RV::priv_lvl_t priv_lvl_i,
    input logic [2:0] frm_i,
    input logic tvm_i,
    input logic tw_i,
    input logic tsr_i,
    input logic debug_mode_i,
    output logic is_fault_o
);

  logic isfault;
  // Some check
  always_comb begin : isfault_comb
    isfault = 0; // No fault by default
    /* SRET can only be executed in S and M mode */
    if(si_i.op == C::SRET && priv_lvl_i == RV::PRIV_LVL_U) isfault = 1;
    /* S-Mode and Trap SRET */
    if(si_i.op == C::SRET && priv_lvl_i == RV::PRIV_LVL_S && tsr_i) isfault = 1;
    /* MRET  can only be executed in S and M mode */
    if(si_i.op == C::MRET && priv_lvl_i !=  RV::PRIV_LVL_M) isfault = 1;
    /* DRET can only be executed in debug mode */
    if(si_i.op == C::DRET && !debug_mode_i) isfault = 1;
    /* if timeout wait is set, trap on an illegal instruction in S Mode */
    if(si_i.op == C::WFI && priv_lvl_i == RV::PRIV_LVL_S && tw_i) isfault = 1;
    /* Canned be used in user mode */
    if(si_i.op == C::WFI && priv_lvl_i == RV::PRIV_LVL_U) isfault = 1;
    if(si_i.op == C::FENCE_VMA && priv_lvl_i == RV::PRIV_LVL_U)  isfault = 1;
    /* check TVM flag */
    if(si_i.op == C::FENCE_VMA && priv_lvl_i == RV::PRIV_LVL_S && tvm_i) isfault = 1;
    /* FPU must be active */
    if(si_i.fu == C::FU_FPU && fs_i != RV::XS_OFF) isfault = 1;
    /* FPU: check rounding mode */
    // TODO
  end
  assign is_fault_o = isfault;

endmodule
