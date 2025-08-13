import C::*;

module iew #() (
    input clk,
    input rstn,
    // From rename stage
    input di_t di_i,
    input logic di_i_valid,
    output logic di_i_ready,
    // To ex stage
    output fu_input_t fuinput_o,
    output logic fuinput_o_valid,
    input fu_bitvector_t fuinput_o_ready,
    // From ex stage
    input fu_output_t    bypass_fuoutput_i[NR_WB_PORTS],
    input wb_bitvector_t bypass_fuoutput_i_valid,
    input fu_output_t    fuoutput_i[NR_WB_PORTS],
    input wb_bitvector_t fuoutput_i_valid
);
    // TODO 0: Handle many write backs
    // TODO 1: Bancked PRF ?
    parameter int NREAD = 2;
    // Write ports
    logic [NR_WB_PORTS-1:0]                   prf_we;
    logic [NR_WB_PORTS-1:0][PREG_ID_BITS-1:0] prf_waddr;
    logic [NR_WB_PORTS-1:0][XLEN-1:0]         prf_wdata;
    // Read ports
    logic [NREAD-1:0][PREG_ID_BITS-1:0]  prf_raddr;
    logic [NREAD-1:0][XLEN-1:0]          prf_rdata;
    regfile #(
        .WIDTH(XLEN),
        .NREGS(PRFSIZE),
        .NREAD(NREAD),
        .NWRITE(NR_WB_PORTS)
    ) prf (
        .clk(clk),
        .rstn(rstn),
        .we(prf_we),
        .waddr(prf_waddr),
        .wdata(prf_wdata),
        .raddr(prf_raddr), 
        .rdata(prf_rdata)
    );


    // Write ports
    logic [NR_COMMIT_PORTS-1:0]                   arf_we;
    logic [NR_COMMIT_PORTS-1:0][AREG_ID_BITS-1:0] arf_waddr;
    logic [NR_COMMIT_PORTS-1:0][XLEN-1:0]         arf_wdata;
    // Read ports
    logic [NREAD-1:0][AREG_ID_BITS-1:0]  arf_raddr;
    logic [NREAD-1:0][XLEN-1:0]          arf_rdata;
    regfile #(
        .WIDTH(XLEN),
        .NREGS(ARFSIZE),
        .NREAD(NREAD),
        .NWRITE(NR_COMMIT_PORTS)
    ) arf (
        .clk(clk),
        .rstn(rstn),
        .we(arf_we),
        .waddr(arf_waddr),
        .wdata(arf_wdata),
        .raddr(arf_raddr), 
        .rdata(arf_rdata)
    );


    /* Scoreboard : decouple data and ctrl */
    // Write ports
    logic [NR_WB_PORTS-1:0]                   sb_we;
    logic [NR_WB_PORTS-1:0][PREG_ID_BITS-1:0] sb_waddr;
    logic [NR_WB_PORTS-1:0]                   sb_wdata;
    // Read ports
    logic [NREAD-1:0][PREG_ID_BITS-1:0]  sb_raddr;
    logic [NREAD-1:0]                    sb_rdata;
    regfile #(
        .WIDTH(1),
        .NREGS(PRFSIZE),
        .NREAD(NREAD),
        .NWRITE(NR_WB_PORTS)
    ) scoreboard (
        .clk(clk),
        .rstn(rstn),
        .we(sb_we),
        .waddr(sb_waddr),
        .wdata(sb_wdata),
        .raddr(sb_raddr), 
        .rdata(sb_rdata)
    );

    /* Read Scoreboard, PRF and ARF */
    assign sb_raddr[0] = di_i.prs1;
    assign sb_raddr[1] = di_i.prs2;
    assign prf_raddr[0] = di_i.prs1;
    assign prf_raddr[1] = di_i.prs2;
    assign arf_raddr[0] = di_i.si.rs1;
    assign arf_raddr[1] = di_i.si.rs2;

    logic [XLEN-1:0] rs1val, rs2val;
    logic rs1val_valid, rs2val_valid;

    always_comb begin : read_operands
        // rs1: default is valid
        rs1val = 0;
        rs1val_valid = 1'b1;
        if(di_i.si.fu == FU_ALU && di_i.si.op == AUIPC) begin 
            rs1val = di_i.si.pc;
            rs1val_valid = 1'b1;
        end else if (di_i.si.use_uimm) begin
            rs1val = XLEN'(di_i.si.rs1);
            rs1val_valid = 1'b1;
        end else if(di_i.si.rs1_valid) begin // RR
            if (di_i.prs1_renammed) begin // PRF if bypasss
                rs1val = prf_rdata[0];
                rs1val_valid = sb_rdata[0];
            end else begin // ARF otherwise
                rs1val = arf_rdata[0];
                rs1val_valid = 1'b1; // Always valid
            end
        end
        // rs2: default is valid
        rs2val = 0;
        rs2val_valid = 1'b1;
        // TODO : check synthesis
        // we can move AUIPC mux imm or rs2 in exe
        if(di_i.si.fu == FU_ALU && di_i.si.op == AUIPC) begin
            rs2val = di_i.si.imm;
            rs2val_valid = 1'b1;
        end else  if(di_i.si.rs2_valid) begin // RR
            if (di_i.prs2_renammed) begin // PRF if bypasss
                rs2val = prf_rdata[1];
                rs2val_valid = sb_rdata[1];
            end else begin // ARF otherwise
                rs2val = arf_rdata[1];
                rs2val_valid = 1'b1; // Always valid
            end
        end
    end

    logic ro_valid, serialisation_valid, fu_valid;

    assign ro_valid = rs1val_valid && rs2val_valid;
    assign serialisation_valid = 1'b1; // TODO

    assign fu_valid = fuinput_o_ready[di_i.si.fu];

    /* Final output */
    assign fuinput_o.pc         = di_i.si.pc;
    assign fuinput_o.id         = di_i.id;
    assign fuinput_o.prd        = di_i.prd;
    assign fuinput_o.rs1val     = rs1val;
    assign fuinput_o.rs2val     = rs2val;
    assign fuinput_o.imm        = di_i.si.imm;
    assign fuinput_o.fu         = di_i.si.fu;
    assign fuinput_o.op         = di_i.si.op;

    logic nostall;
    assign nostall = !di_i_valid ||
                     (di_i_valid &&
                     ro_valid &&
                     fu_valid &&
                     serialisation_valid);

    assign fuinput_o_valid      = di_i_valid && nostall;
    assign di_i_ready           = nostall;

    always_ff @(posedge clk) begin 
        if(di_i_valid && !nostall) begin
            if(!ro_valid) begin
                $display("IRO invalid for inst id %d", di_i.id);
            end else if (!fu_valid) begin
                $display("No FU valid for inst id %d", di_i.id);
            end else if (!serialisation_valid) begin
                $display("Issue in serialisation mode");
            end
        end
        if(di_i_valid && fuinput_o_valid) begin
            $display("Issue: inst pc %x (sn=%d) rs1val=%d rs2val=%d fu:%d op:%d",
                fuinput_o.pc, fuinput_o.id,
                fuinput_o.rs1val, fuinput_o.rs2val,
                fuinput_o.fu, fuinput_o.op);
        end
    end
    /* Backward path : update from execute */
    assign prf_we = 1'b0; // TODO
    assign prf_waddr = 0;
    assign prf_wdata = 0;
    assign sb_we = 1'b0; // TODO
    assign sb_waddr = 0;
    assign sb_wdata = 0;

    /* Backward path : update from commit */
    assign arf_we = 1'b0;
    assign arf_waddr = 0;
    assign arf_wdata = 0;
                                  


endmodule

