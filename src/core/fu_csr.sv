
module fu_csr #() (
    input logic clk,
    input logic rstn,
    input fu_input_t fuinput_i,
    input logic      fuinput_i_valid,
    output logic      fuinput_i_ready,
    output fu_output_t fuoutput_o,
    output logic       fuoutput_o_valid,
    output logic       completion_o_valid,
    // Core   
    input rob_entry_t   retire_entry_i,
    input logic         retire_entry_i_valid,
    csr_if.master csr_io,
    // Squash intf
    squash_if.slave  squash_io
);

    /* Retrieve inputs */
    logic is_csr_i;
    RV::csr_addr_t csr_addr_i;
    xlen_t csr_wdata_i;
    logic csr_need_write_i;
    logic csr_violation_i;
    none_set_t op_i;
    assign is_csr_i = fuinput_i.op inside {CSR_WRITE, CSR_SET, CSR_CLEAR, CSR_READ};
    assign csr_addr_i = fuinput_i.imm[11:0];
    assign csr_wdata_i = fuinput_i.rs1val;
    assign csr_need_write_i = fuinput_i.op inside {CSR_WRITE, CSR_SET, CSR_CLEAR};
    assign csr_violation_i = csr_addr_i.priv_lvl != RV::PRIV_LVL_M; // TODO read csr
    assign op_i = fuinput_i.op.none;

    /* Read path (All modification are applied after the reg wb) */
    // Performes early read
    xlen_t csr_rdata;
    assign csr_io.rvalid = fuinput_i_valid && is_csr_i;
    assign csr_io.raddr  = csr_addr_i;
    assign csr_rdata     = csr_io.rdata;

    // Write path (save csr in buffer): cannot be speculative
    typedef struct packed {
        id_t id;
        RV::csr_addr_t addr;
        xlen_t data;
        logic valid;
    } csr_write_entry_t;

    csr_write_entry_t csrq[1]; // Fifo of inflights CSR Writes
    csr_write_entry_t csrw;

    // Save Reg Write in buffer until commit
    assign csrw.id    = fuinput_i.id;
    assign csrw.addr  = csr_addr_i;
    assign csrw.valid = fuinput_i_valid && csr_need_write_i;
    assign csrw.data  = op_i == CSR_WRITE ? csr_wdata_i :
                        op_i == CSR_SET   ? csr_wdata_i | csr_rdata :
                        op_i == CSR_CLEAR ? (~csr_wdata_i) & csr_rdata :
                        '0;
    logic csrq_pop;
    assign csrq_pop = retire_entry_i_valid &&
                      csrq[0].valid &&
                      csrq[0].id == retire_entry_i.id;
    always_ff @(posedge clk) begin
        if (!rstn) begin
            csrq[0].valid <= '0;
        end else begin
            if (squash_io.valid) begin
                csrq[0].valid <= '0; // Same as reset
            end else begin 
                if(csrw.valid) begin
                    csrq[0] <= csrw;
                end
                if(csrq_pop) begin 
                    csrq[0].valid <= '0;
                end
            end
        end
    end

    always_comb begin
        if (fuinput_i_valid) begin
            unique case(op_i)
                CSR_WRITE, CSR_READ, CSR_SET, CSR_CLEAR:; // Already done
                MRET, SRET, DRET: $error("TODO (M|S|D)RET");
                ECALL, EBREAK: $error("TODO e(call|break)");
                WFI: $error("TODO");
                FENCE:; /* Ignore for now */
                FENCE_I, FENCE_VMA: $error("TODO");
            endcase
        end
    end

    /* When commit write CSR */
    assign csr_io.waddr  = csrq[0].addr;
    assign csr_io.wdata  = csrq[0].data;
    assign csr_io.wvalid = csrq_pop;

    /* Output */
    assign fuoutput_o.pc    = fuinput_i.pc;
    assign fuoutput_o.id    = fuinput_i.id;
    assign fuoutput_o.prd   = fuinput_i.prd;
    assign fuoutput_o.rdval = is_csr_i ? csr_rdata : '0;
    assign fuoutput_o_valid = is_csr_i ? fuinput_i_valid : '0;
    assign completion_o_valid = fuinput_i_valid; // Always complete

    /* Do CSR one by one */
    assign fuinput_i_ready  = !csrq[0].valid; // No RaW CSR !

endmodule
