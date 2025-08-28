import C::*;

module csr_file #()(
    input  logic clk,
    input  logic rstn,
    csr_if.slave csr_io,
    // Core   
    input rob_entry_t   retire_entry_i,
    input logic         retire_entry_i_valid
);

    // Csr logic
    typedef struct packed {
        xlen_t cycle;
        xlen_t instret;
    } all_csr_t;

    all_csr_t csrs_q, csrs_d;

    always_ff @(posedge clk) begin
        if(!rstn) begin
            csrs_q <= '0;
        end else begin
            csrs_q <= csrs_d;
        end
    end

    // Write logic
    always_comb begin
        csrs_d = csrs_q;
        /* Default updates */
        csrs_d.cycle = csrs_q.cycle + 1;
        csrs_d.instret += XLEN'(retire_entry_i_valid && retire_entry_i.is_uop_final);
        /* User updates */
        if (csr_io.wvalid) begin
            case (csr_io.waddr)
                RV::CSR_CYCLE,
                RV::CSR_MCYCLE:  csrs_d.cycle   = csr_io.wdata;
                RV::CSR_INSTRET,
                RV::CSR_MINSTRET: csrs_d.instret = csr_io.wdata;
                default: $warning("UNIMPLEMENTED CSR WRITE at @=%x, D=%x",
                    csr_io.waddr, csr_io.wdata);
            endcase
        end
    end

    // Asynchronous read ?
    always_comb begin
        csr_io.rdata = '0;
        if(csr_io.rvalid) begin
            case (csr_io.raddr)
                RV::CSR_CYCLE,
                RV::CSR_MCYCLE:  csr_io.rdata = csrs_q.cycle;
                RV::CSR_INSTRET,
                RV::CSR_MINSTRET: csr_io.rdata = csrs_q.instret;
                default: $warning("UNIMPLEMENTED CSR READ at @=%x",
                    csr_io.raddr);
            endcase
        end
    end


endmodule
