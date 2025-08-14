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
    input wb_bitvector_t fuoutput_i_valid,
    // To pipeline
    output rob_entry_t   commit_entry_o
);
    // TODO 0: Handle many write backs
    // TODO 1: Bancked PRF ?
    parameter PRF_READ_PORTS = NR_ISSUE_PRF_READ_PORTS + NR_COMMIT_PORTS;
    parameter int NREAD = 2;
    // Write ports
    logic [NR_WB_PORTS-1:0]                   prf_we;
    logic [NR_WB_PORTS-1:0][PREG_ID_BITS-1:0] prf_waddr;
    logic [NR_WB_PORTS-1:0][XLEN-1:0]         prf_wdata;
    // Read ports
    logic [PRF_READ_PORTS-1:0][PREG_ID_BITS-1:0]  prf_raddr;
    logic [PRF_READ_PORTS-1:0][XLEN-1:0]          prf_rdata;
    regfile #(
        .WIDTH(XLEN),
        .NREGS(PRFSIZE),
        .NREAD(PRF_READ_PORTS),
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

    logic [NREAD-1:0] is_renammed = {di_i.prs2_renammed,
                                     di_i.prs1_renammed};
    /* Read regs with bypass */
    logic [NREAD-1:0][XLEN-1:0] prf_rdata_forward;
    logic [NREAD-1:0]           prf_rdata_forward_valid;
    always_comb begin : read_regs_with_bypass
        for (int i = 0; i < NREAD; i++) begin
            if(is_renammed[i]) begin
                /* Default : read prf */
                prf_rdata_forward[i]       =  prf_rdata[i];
                prf_rdata_forward_valid[i] = sb_rdata[i];
                /* Read bypass is sb fail */
                for (int j = 0; j < NR_WB_PORTS; j++) begin
                    if (bypass_fuoutput_i_valid[j] &&
                        bypass_fuoutput_i[j].prd == prf_raddr[i]) begin
                        /* Hit bypass */
                        prf_rdata_forward[i] = bypass_fuoutput_i[i].rdval;
                        prf_rdata_forward_valid[i] = 1'b1;
                    end
                end
            end else begin
                /* Read ARF */
                prf_rdata_forward[i]       = arf_rdata[i];
                prf_rdata_forward_valid[i] = 1'b1; // Always valid
            end
        end
    end

    always_comb begin : read_operands
        // rs1: default is valid
        rs1val = 0;
        rs1val_valid = 1'b1;
        if (di_i.si.fu == FU_ALU && di_i.si.op == AUIPC) begin 
            rs1val = di_i.si.pc;
            rs1val_valid = 1'b1;
        end else if (di_i.si.use_uimm) begin
            rs1val = XLEN'(di_i.si.rs1);
            rs1val_valid = 1'b1;
        end else if(di_i.si.rs1_valid) begin // RR
            rs1val = prf_rdata_forward[0];
            rs1val_valid = prf_rdata_forward_valid[0];
        end
        // rs2: default is valid
        rs2val = 0;
        rs2val_valid = 1'b1;
        // TODO : check synthesis
        // we can move AUIPC mux imm or rs2 in exe
        if (di_i.si.fu == FU_ALU && di_i.si.op == AUIPC) begin
            rs2val = di_i.si.imm;
            rs2val_valid = 1'b1;
        end else  if (di_i.si.rs2_valid) begin // RR
            rs1val = prf_rdata_forward[1];
            rs1val_valid = prf_rdata_forward_valid[1];
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
    assign fuinput_o.size       = di_i.si.size;

    logic nostall;
    assign nostall = !di_i_valid ||
                     (di_i_valid &&
                     ro_valid &&
                     fu_valid &&
                     serialisation_valid);

    assign fuinput_o_valid      = di_i_valid && nostall;
    assign di_i_ready           = nostall;

    string cause;
    always_comb begin
        cause = "";
        if(di_i_valid) begin
            if(!nostall) begin
                if(!ro_valid) begin
                    cause = "FAIL IRO";
                end else if (!fu_valid) begin
                    cause = "FAIL FU ";
                end else if (!serialisation_valid) begin
                    cause = "FAIL SER";
                end
            end else begin
                cause = "SUCCESS ";
            end
        end
    end
    always_ff @(posedge clk) begin
        if(di_i_valid) begin
            $display("Issue: (port0) %s: pc %x (sn=%d) rs1:%d=%d(%d) rs2:%d=%d(%d) fu:%d(%d) op:%d",
                cause,
                fuinput_o.pc, fuinput_o.id,
                di_i.si.rs1, fuinput_o.rs1val, rs1val_valid,
                di_i.si.rs2, fuinput_o.rs2val, rs2val_valid,
                fuinput_o.fu, fu_valid,
                fuinput_o.op
            );
        end else begin
            $display("Issue: (port0) no ready inputs");
        end
    end


    /* Backward path : update from execute */
    always_comb begin
        for(int i = 0; i < NR_WB_PORTS; i++) begin
            prf_we[i]       = fuoutput_i_valid[i];
            prf_waddr[i]    = fuoutput_i[i].prd;
            prf_wdata[i]    = fuoutput_i[i].rdval;
            sb_we[i]        = fuoutput_i_valid[i];
            sb_waddr[i]     = fuoutput_i[i].prd;
            sb_wdata[i]     = 1'b1; // Data is valid
        end
    end
    always_ff @(posedge clk) begin
        for(int i = 0; i < NR_WB_PORTS; i++) begin
            if(fuoutput_i_valid[i]) begin
                $display("Wr-Ba: (port%1d) pc %x (sn=%d) prd:%d <- %x",
                    i,
                    fuoutput_i[i].pc, fuoutput_i[i].id,
                    fuoutput_i[i].prd,
                    fuoutput_i[i].rdval
                );
            end else begin
                // $display("Wr-Ba: (port%d) no wb", i);
            end
        end
    end


    /* Broadcast valids from ex to rob */
    rob_entry_t [NR_ROB_ENTRIES-1:0] rob;
    logic       [NR_ROB_ENTRIES-1:0] rob_allocated;

    // ROB Inputs push
    logic       rob_push_i_valid; // Input
    logic       rob_push_i_ready; // Output
    rob_entry_t rob_push_data_i;
    assign      rob_push_i_ready = !rob_allocated[rob_issue_id_q];
    // ROB Inputs WB
    wb_bitvector_t  rob_wb_id_i_valid;
    rob_id_t        rob_wb_id_i [NR_WB_PORTS];
    // ROB Output Commit
    rob_entry_t rob_pop_data_o;
    logic       rob_pop_i;
    // ROB pointers
    rob_id_t    rob_issue_id_q, rob_issue_id_d;
    assign      rob_issue_id_d = rob_issue_id_q + 1;
    rob_id_t    rob_commit_id_q, rob_commit_id_d;    
    assign      rob_commit_id_d = rob_commit_id_q + 1;
    always_ff @(posedge clk) begin
        if(!rstn) begin
            rob_issue_id_q <= '0;
            rob_commit_id_q <= '0;
            for (int i = 0; i < NR_ROB_ENTRIES; i++) begin
                rob[i].completed <= '0;
            end
            rob_allocated <= '0;
        end else begin
            // Issue ports
            if(rob_push_i_valid) begin
                $asserton(!rob_allocated[rob_issue_id_q]);
                rob[rob_issue_id_q] <= rob_push_data_i;
                rob_allocated[rob_issue_id_q] <= 1'b1;
                rob_issue_id_q <= rob_issue_id_d;
            end
            // Write Back ports
            for (int i = 0; i < NR_WB_PORTS; i++) begin
                if(rob_wb_id_i_valid[i]) begin
                    rob[rob_wb_id_i[i]].completed <= '1;
                end
            end
            if (rob_pop_i) begin
                $asserton(rob_allocated[rob_commit_id_d]);
                rob_allocated[rob_commit_id_d] <= 1'b1;
                rob_commit_id_q <= rob_commit_id_d;
            end
        end
    end
    // Commit ports read
    assign rob_pop_data_o = rob[rob_commit_id_q];

    /* ROB: Insert in rob at issue for now */
    assign rob_push_i_valid = fuinput_o_valid;
    assign rob_push_data_i.id = di_i.id; 
    assign rob_push_data_i.pc = di_i.si.pc;
    assign rob_push_data_i.prd = di_i.prd;
    assign rob_push_data_i.ard = di_i.si.rd;
    assign rob_push_data_i.needprf2arf = di_i.si.rd_valid;
    assign rob_push_data_i.completed = '0;

    /* ROB: Mark WB */
    always_comb begin
        for(int i = 0; i < NR_WB_PORTS; i++) begin
            rob_wb_id_i_valid[i] = fuoutput_i_valid[i];
            rob_wb_id_i[i]       = rob_id_t'(fuoutput_i[i].id);
        end
    end

    // TODO retrieve PRF value at WB or at COMMIT1 -> COMMIT2 ?
    /* ROB: Commit */
    rob_entry_t commit_entry_q, commit_entry_d;
    xlen_t      commit_rdval_q, commit_rdval_d;

    assign commit_entry_d   = rob_pop_data_o;
    assign rob_pop_i        = rob_pop_data_o.completed;
    assign prf_raddr[2]     = rob_pop_data_o.prd; // PRF -> ARF port
    assign commit_rdval_d   = prf_rdata[2];
    always_ff @(posedge clk) begin
        if(!rstn) begin 
            commit_entry_q <= '0;
            commit_rdval_q <= '0;
        end else begin 
            commit_entry_q <= commit_entry_d;
            commit_rdval_q <= commit_rdval_d;
        end
    end

    /* Commit stage */
    assign commit_entry_o = commit_entry_q;

    logic commit_isrd_valid = commit_entry_q.completed &&
                              commit_entry_q.needprf2arf;
    /* Free register : in rename stage ? */
    // logic     commit_free_prd_valid;
    // preg_id_t commit_free_prd;
    // assign commit_free_prd_valid = commit_isrd_valid;
    // assign commit_free_prd       = commit_entry_q.prd;
    /* Update the architecural state */
    assign arf_we[0]    = commit_isrd_valid;
    assign arf_waddr[0] = commit_entry_q.ard;
    assign arf_wdata[0] = commit_rdval_q;





endmodule

