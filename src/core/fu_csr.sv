
module fu_csr #() (
    input logic clk,
    input logic rstn,
    input fu_input_t fuinput_i,
    input logic      fuinput_i_valid,
    output logic      fuinput_i_ready,
    output fu_output_t fuoutput_o,
    output logic       fuoutput_o_valid,
    input logic rob_head_is_csr_i,
    csr_if.master csr_io
); 

    /* Retrieve inputs */
    logic is_csr_i;
    RV::csr_addr_t csr_addr_i;
    xlen_t csr_wdata_i;
    logic csr_need_write_i;
    logic csr_violation_i;
    none_set_t op_i;
    assign is_csr_i = fuinput_i.op inside {CSR_WRITE, CSR_SET, CSR_CLEAR, CSR_READ};
    assign csr_addr_i = fuinput_i.rs2val[11:0];
    assign csr_wdata_i = fuinput_i.rs1val;
    assign csr_need_write_i = fuinput_i.op inside {CSR_WRITE, CSR_SET, CSR_CLEAR};
    assign csr_violation_i = csr_addr_i.priv_lvl != RV::PRIV_LVL_M; // TODO read csr
    assign op_i = fuinput_i.op.none;

    /* Read path (All modification are applied after the reg wb) */
    // Performes early read
    xlen_t csr_rdata;
    assign csr_io.raddr = csr_addr_i;
    assign csr_rdata    = csr_io.rdata;
    
    // Write path (save csr in buffer): cannot be speculative
    RV::csr_addr_t csr_addr_q, csr_addr_d;
    logic csr_valid_q, csr_valid_d;
    xlen_t csr_data_q, csr_data_d;

    // Save Reg Write in buffer until commit
    assign csr_addr_d  = csr_addr_i;
    assign csr_valid_d = fuinput_i_valid && csr_need_write_i;
    assign csr_data_d  = op_i == CSR_WRITE ? csr_wdata_i :
                         op_i == CSR_SET   ? csr_wdata_i | csr_rdata :
                         op_i == CSR_CLEAR ? (~csr_wdata_i) & csr_rdata :
                         '0;

    always_ff @(posedge clk) begin
        if (!rstn) begin
            csr_addr_q <= '0;
            csr_valid_q <= '0;
            csr_data_q <= '0;
        end else begin
            csr_addr_q <= csr_addr_d;
            csr_valid_q <= csr_valid_d;
            csr_data_q <= csr_data_d;
        end
    end

    /* When commit write CSR */
    assign csr_io.waddr  = csr_addr_q;
    assign csr_io.wdata  = csr_data_q;
    assign csr_io.wvalid = '0; // TODO

    /* Output */
    assign fuoutput_o.pc    = fuinput_i.pc;
    assign fuoutput_o.id    = fuinput_i.id;
    assign fuoutput_o.prd   = fuinput_i.prd;
    assign fuoutput_o.rdval = is_csr_i ? csr_rdata : '0;
    assign fuoutput_o_valid = fuinput_i_valid;

    /* Do CSR one by one */
    assign fuinput_i_ready  = !csr_valid_q; // No RaW CSR !

endmodule
