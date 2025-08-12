import C::*;

module dynamic_decoder #() (
    input clk,
    input rstn,

    input si_t si_i,
    input logic si_i_valid,

    /* Csr flags */
    input RV::xs_t fs_i,
    input RV::priv_lvl_t priv_lvl_i,
    input logic [2:0] frm_i,
    input logic tvm_i,
    input logic tw_i,
    input logic tsr_i,
    input logic debug_mode_i,
  
    output di_t di_o,
    input logic di_o_ready
);
  logic[20-1:0] cpt;
  logic isfault;

  assign di_o.si = si_i;
  assign di_o.valid = 1'b0;
  assign di_o.id = cpt;
  assign di_o.fault = isfault;
  
  always_ff @(posedge clk) begin
    if(si_i_valid && di_o_ready) begin
      cpt <= cpt + 1;
    end
  end

  // Some check
  always_comb begin : isfaultconb
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
    if(si_i.fu == C::FU_FPU && fs_i != RV::Off) isfault = 1;
    /* FPU: check rounding mode */
    // TODO
  end

endmodule
