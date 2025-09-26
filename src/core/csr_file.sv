import C::*;

module csr_file #(
    parameter xlen_t MVENDORID = 0,
    parameter xlen_t MARCHID = 0,
    parameter xlen_t MIMPID = 0,
    parameter xlen_t MHARTID = 0,
    parameter xlen_t MCONFIGPTR = 0
)(
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
        RV::mstatus_rv_t mstatus;
        xlen_t mtvec;
    } all_csr_t;

    all_csr_t csrs_q, csrs_d;

    always_ff @(posedge clk) begin
        if(!rstn) begin
            csrs_q <= '0;
        end else begin
            csrs_q <= csrs_d;
        end
    end

    logic illegalw, illegalr;

    // Write logic
    always_comb begin
        csrs_d = csrs_q;
        /* Default updates */
        csrs_d.cycle = csrs_q.cycle + 1;
        csrs_d.instret += XLEN'(retire_entry_i_valid && retire_entry_i.is_uop_final);
        /* User updates */
        illegalw = '0;
        if (csr_io.wvalid) begin
            case (csr_io.waddr)
                RV::CSR_CYCLE,
                RV::CSR_MCYCLE:  csrs_d.cycle   = csr_io.wdata;
                RV::CSR_INSTRET,
                RV::CSR_MINSTRET: csrs_d.instret = csr_io.wdata;
                RV::CSR_MSTATUS: begin
                    csrs_d.mstatus = csr_io.wdata;
                    // Hardwired
                    csrs_d.mstatus.xs = RV::XS_OFF;
                    csrs_d.mstatus.fs = RV::XS_OFF; // TODO let user select
                    csrs_d.mstatus.vs = RV::XS_OFF;
                    csrs_d.mstatus.ube = '0; // LE
                    csrs_d.mstatus.mpp = csrs_q.mstatus.mpp;
                    csrs_d.mstatus.wpri3 = '0;
                    csrs_d.mstatus.wpri1 = '0;
                    csrs_d.mstatus.wpri2 = '0;
                    csrs_d.mstatus.wpri0 = '0;
                end
                RV::CSR_MTVEC:  csrs_d.mtvec = csr_io.wdata;
                default: illegalw = '1;
            endcase
        end
    end

    // Asynchronous read ?
    always_comb begin
        csr_io.rdata = '0;
        illegalr = '0;
        if(csr_io.rvalid) begin
            case (csr_io.raddr)
                RV::CSR_CYCLE,
                RV::CSR_MCYCLE:     csr_io.rdata = csrs_q.cycle;
                RV::CSR_INSTRET,
                RV::CSR_MINSTRET:   csr_io.rdata = csrs_q.instret;
                RV::CSR_MSTATUS:    csr_io.rdata = csrs_q.mstatus;
                RV::CSR_MTVEC:      csr_io.rdata = csrs_q.mtvec;
                RV::CSR_MVENDORID:  csr_io.rdata = MVENDORID;
                RV::CSR_MARCHID:    csr_io.rdata = MARCHID;
                RV::CSR_MIMPID:     csr_io.rdata = MIMPID;
                RV::CSR_MHARTID:    csr_io.rdata = MHARTID;
                RV::CSR_MCONFIGPTR: csr_io.rdata = MCONFIGPTR;
                default: illegalr = '1;
            endcase
        end
    end

    `ifndef SYNTHESIS
    always_ff @(posedge clk) begin
        if (csr_io.wvalid && illegalw) begin
            $error("UNIMPLEMENTED CSR WRITE at @=%x, D=%x",
                csr_io.waddr, csr_io.wdata);
        end
        if (csr_io.rvalid && illegalr) begin
            $error("UNIMPLEMENTED CSR READ at @=%x rvalid:%b",
                csr_io.raddr, csr_io.rvalid);
        end
    end
    `endif

endmodule
