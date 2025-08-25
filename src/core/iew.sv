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
    input completion_port_t completion_ports_i[NR_COMPL_PORTS],
    // To pipeline
    output rob_entry_t   retire_entry_o,
    output logic         retire_entry_o_valid,

    // To BQ
    bq_pop_if.commit bq_pop_io
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
    logic [NR_WB_PORTS-1:0]                   sb_wbs_we;
    logic [NR_WB_PORTS-1:0][PREG_ID_BITS-1:0] sb_wbs_waddr;

    logic [NR_ISSUE_PORTS-1:0]                   sb_iss_we;
    logic [NR_ISSUE_PORTS-1:0][PREG_ID_BITS-1:0] sb_iss_waddr;
    // Read ports
    logic [NREAD-1:0][PREG_ID_BITS-1:0]  sb_raddr;
    logic [NREAD-1:0]                    sb_rdata;

    logic [PRFSIZE-1:0] sb_q, sb_d;
    always_comb begin : sb_update
        sb_d = sb_q;
        // Set valid on WB
        for (int i = 0; i < NR_WB_PORTS; i++) begin
            if (sb_wbs_we[i]) begin
                sb_d[sb_wbs_waddr[i]] = 1'b1;
            end
        end
        // Clear valid on issue
        for(int i = 0; i < NR_ISSUE_PORTS; i++) begin
            if (sb_iss_we[i]) begin
                sb_d[sb_iss_waddr[i]] = 1'b0;
            end
        end
        // Asynchronous read ports (with bypass)
        for (int i = 0; i < NREAD; i++) begin
            sb_rdata[i] = sb_q[sb_raddr[i]];
            // If any writeback this cycle matches this read address -> mark busy
            for (int w = 0; w < NR_WB_PORTS; w++) begin
                if (sb_wbs_we[w] && sb_wbs_waddr[w] == sb_raddr[i]) begin
                    sb_rdata[i] = 1'b1;
                end
            end
            // TODO handler RaW in the same cycle !
            // // If any issue this cycle matches this read address -> mark free
            // for (int w = NR_WB_PORTS; w < NR_WB_PORTS+NR_ISSUE_PORTS; w++) begin
            //     if (sb_we[w] && sb_waddr[w] == sb_raddr[i])
            //         sb_rdata[i] = 1'b0;
            // end
        end
    end
    always_ff @(posedge clk) begin
        if(!rstn) begin
            sb_q <= '0;
        end else begin
            sb_q <= sb_d;
        end
    end

    // regfile #(
    //     .WIDTH(1),
    //     .NREGS(PRFSIZE),
    //     .NREAD(NREAD),
    //     .NWRITE(NR_WB_PORTS+NR_ISSUE_PORTS)
    // ) scoreboard (
    //     .clk(clk),
    //     .rstn(rstn),
    //     .we(sb_we),
    //     .waddr(sb_waddr),
    //     .wdata(sb_wdata),
    //     .raddr(sb_raddr), 
    //     .rdata(sb_rdata)
    // );

    /* Read Scoreboard, PRF and ARF */
    assign sb_raddr[0] = di_i.prs1;
    assign sb_raddr[1] = di_i.prs2;
    assign prf_raddr[0] = di_i.prs1;
    assign prf_raddr[1] = di_i.prs2;
    assign arf_raddr[0] = di_i.si.rs1;
    assign arf_raddr[1] = di_i.si.rs2;

    /* Read regs with bypass */
    logic [NREAD-1:0] is_renammed;
    assign is_renammed[0] = di_i.prs1_renammed;
    assign is_renammed[1] = di_i.prs2_renammed;
    xlen_t [NREAD-1:0] prf_rdata_forward;
    logic [NREAD-1:0]  prf_rdata_forward_valid;

    logic [NREAD-1:0]  fw0_match;
    xlen_t [NREAD-1:0] fw0_data;

    always_comb begin : read_regs_with_bypass
        for (int i = 0; i < NREAD; i++) begin
            // Read bypass network (FW0)
            fw0_match[i] = '0;
            fw0_data[i] = 'x;
            for (int j = 0; j < NR_WB_PORTS; j++) begin   
                if (bypass_fuoutput_i_valid[j] &&
                    bypass_fuoutput_i[j].prd == prf_raddr[i]) begin
                    fw0_match[i] = '1;
                    fw0_data[i]  = bypass_fuoutput_i[j].rdval;
                end
            end
            prf_rdata_forward_valid[i] = '1;
            if (is_renammed[i]) begin
                /* Default : read prf */
                prf_rdata_forward[i]       = prf_rdata[i];
                prf_rdata_forward_valid[i] = sb_rdata[i];
                /* Read bypass is sb fail */
                if (fw0_match[i]) begin /* Hit bypass */
                    // assert (!sb_rdata[i]) else $error("Cannot Sb and FW0");
                    prf_rdata_forward[i]       = fw0_data[i];
                    prf_rdata_forward_valid[i] = 1'b1;
                end
            end else begin
                /* Read ARF */
                prf_rdata_forward[i]       = arf_rdata[i];
                prf_rdata_forward_valid[i] = 1'b1; // Always valid
            end
        end
    end

    /* Setup operands rs1 and rs2 */
    logic [XLEN-1:0] rs1val, rs2val;
    logic rs1val_valid, rs2val_valid;

    always_comb begin : read_operands
        // rs1: default is valid
        rs1val = '0;
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
        rs2val = '0;
        rs2val_valid = 1'b1;
        // TODO : check synthesis
        // we can move AUIPC mux imm or rs2 in exe
        if (!di_i.si.rs2_valid) begin
            rs2val = di_i.si.imm;
            rs2val_valid = 1'b1;
        end else  if (di_i.si.rs2_valid) begin // RR
            rs2val = prf_rdata_forward[1];
            rs2val_valid = prf_rdata_forward_valid[1];
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
    assign fuinput_o.bqid       = di_i.bqid;

    logic nostall;
    assign nostall = !di_i_valid ||
                     (di_i_valid &&
                     ro_valid &&
                     fu_valid &&
                     serialisation_valid);

    assign fuinput_o_valid      = di_i_valid && nostall;
    assign di_i_ready           = nostall;

    /* mark the register as buzy */
    always_comb begin
        for (int i = 0; i < NR_ISSUE_PORTS; i++) begin
            sb_iss_waddr[i] = fuinput_o.prd;
            sb_iss_we[i]    = fuinput_o_valid && di_i.si.rd_valid;
        end
    end
    string cause;
    always_comb begin
        cause = "";
        if(di_i_valid) begin
            if(!nostall) begin
                if(!ro_valid) begin
                    cause = "FAIL IRO ";
                end else if (!fu_valid) begin
                    cause = "FAIL FU  ";
                end else if (!serialisation_valid) begin
                    cause = "FAIL SER ";
                end
            end else begin
                cause = "SUCCESS  ";
            end
        end
    end
    always_ff @(posedge clk) begin
        if(di_i_valid) begin
            $display("Issue: (port0) %s: pc %x (sn=%x) %s <- %s%s fu:%x(%s) op:%x",
                cause,
                fuinput_o.pc, fuinput_o.id,
                di_i.si.rd_valid ?
                    dumpAPReg(di_i.si.rd, di_i.prd, 1'b1) : " ",
                di_i.si.rs1_valid ?
                    $sformatf(" %s:%s %s",
                        dumpAPReg(di_i.si.rs1, di_i.prs1, di_i.prs1_renammed),
                        rs1val_valid ?
                            $sformatf("%x",fuinput_o.rs1val) :
                            "RaW",
                        fw0_match[0] ?
                            $sformatf(" (FromFW0:%x)", fw0_data[0]):
                            "",
                    ) : " ",
                
                di_i.si.rs2_valid ?
                    $sformatf(" %s:%s %s",
                        dumpAPReg(di_i.si.rs2, di_i.prs2, di_i.prs2_renammed),
                        rs2val_valid ?
                            $sformatf("%x", fuinput_o.rs2val) :
                            "RaW",
                        fw0_match[1] ?
                            $sformatf(" (FromFW0:%x)", fw0_data[1]):
                            "",
                    ) : " ",

                fuinput_o.fu, fu_valid ? "READY": "BUZY",
                fuinput_o.op
            );
        end else begin
            $display("Issue: (port0) no ready inputs");
        end
    end


    /* Backward path : write back ! */
    always_comb begin
        for(int i = 0; i < NR_WB_PORTS; i++) begin
            prf_we[i]       = fuoutput_i_valid[i];
            prf_waddr[i]    = fuoutput_i[i].prd;
            prf_wdata[i]    = fuoutput_i[i].rdval;
            sb_wbs_we[i]        = fuoutput_i_valid[i];
            sb_wbs_waddr[i]     = fuoutput_i[i].prd;
        end
    end

    fu_output_t wbfw0 [NR_WB_PORTS];
    logic [NR_WB_PORTS-1:0] wbfw0_valid;
    assign wbfw0 = bypass_fuoutput_i;
    assign wbfw0_valid = bypass_fuoutput_i_valid;
    always_ff @(posedge clk) begin
        for(int i = 0; i < NR_WB_PORTS; i++) begin
            if(wbfw0_valid[i]) begin
                $display("WBFW0: (port%s) SUCCESS : pc %x (sn=%x) prd:%x <- %x",
                    $sformatf("%1d", i),
                    wbfw0[i].pc, wbfw0[i].id,
                    wbfw0[i].prd,
                    wbfw0[i].rdval
                );
            end else begin
                $display("WBFW0: (port%s) empty", $sformatf("%1d", i),);
            end
        end
    end

    /* Completion path */
    rob_entry_t [NR_ROB_ENTRIES-1:0] rob;
    logic       [NR_ROB_ENTRIES-1:0] rob_allocated;
    // ROB Inputs push
    logic       rob_push_i_valid; // Input
    logic       rob_push_i_ready; // Output
    rob_entry_t rob_push_data_i;
    assign      rob_push_i_ready = !rob_allocated[rob_issue_id_q];
    // ROB Inputs completion
    logic [NR_COMPL_PORTS-1:0] rob_cmpl_id_i_valid;
    rob_id_t                   rob_cmpl_id_i [NR_COMPL_PORTS];
    // ROB Output Commit
    rob_entry_t rob_pop_data_o;
    logic       rob_pop_data_o_valid; // Instruction is here
    logic       rob_pop_i;
    // ROB pointers
    rob_id_t    rob_issue_id_q, rob_issue_id_d;
    assign      rob_issue_id_d = rob_issue_id_q + 1;
    rob_id_t    rob_retire_id_q, rob_retire_id_d;    
    assign      rob_retire_id_d = rob_retire_id_q + 1;
    always_ff @(posedge clk) begin
        if(!rstn) begin
            rob_issue_id_q <= '0;
            rob_retire_id_q <= '0;
            for (int i = 0; i < NR_ROB_ENTRIES; i++) begin
                rob[i].completed <= '0;
            end
            rob_allocated <= '0;
        end else begin
            // Issue ports
            if(rob_push_i_valid) begin
                assert (!rob_allocated[rob_issue_id_q]) else 
                    $error("Overallocate rob entry");
                rob[rob_issue_id_q] <= rob_push_data_i;
                rob_allocated[rob_issue_id_q] <= 1'b1;
                rob_issue_id_q <= rob_issue_id_d;
            end
            // Write Back ports
            for (int i = 0; i < NR_COMPL_PORTS; i++) begin
                if(rob_cmpl_id_i_valid[i]) begin
                    rob[rob_cmpl_id_i[i]].completed <= '1;
                end
            end
            if (rob_pop_i) begin
                assert (rob_allocated[rob_retire_id_q]) else
                    $error("Pop Unallocated entry");
                assert (rob[rob_retire_id_q].completed) else 
                    $error("Pop Uncompleted entry");
                rob_allocated[rob_retire_id_q] <= 1'b0;
                rob_retire_id_q <= rob_retire_id_d;
            end
        end
    end
    // Commit ports read
    assign rob_pop_data_o = rob[rob_retire_id_q];
    assign rob_pop_data_o_valid = rob_allocated[rob_retire_id_q] &&
                                  rob_pop_data_o.completed;

    /* ROB: Insert in rob at issue for now */
    assign rob_push_i_valid     = fuinput_o_valid;
    assign rob_push_data_i.id   = di_i.id; 
    assign rob_push_data_i.pc   = di_i.si.pc;
    assign rob_push_data_i.prd  = di_i.prd;
    assign rob_push_data_i.ard  = di_i.si.rd;
    assign rob_push_data_i.needprf2arf = di_i.si.rd_valid;
    assign rob_push_data_i.needSQfree = di_i.si.fu == FU_LSU &&
                                        di_i.si.op == S; // TODO AMO
    assign rob_push_data_i.fu   = di_i.si.fu;
    // assign rob_push_data_i.needBQfree = di_i.si.fu == FU_CTRL;
    // assign rob_push_data_i.needCSRfree = di_i.si.fu == FU_CSR &&
    //     di_i.si.op inside { CSR_WRITE, CSR_SET, CSR_CLEAR };
    assign rob_push_data_i.completed = '0;

    /* ROB: Mark completion  */
    always_comb begin
        for(int i = 0; i < NR_COMPL_PORTS; i++) begin
            rob_cmpl_id_i_valid[i] = completion_ports_i[i].valid;
            rob_cmpl_id_i[i]       = rob_id_t'(completion_ports_i[i].id);
        end
    end

    // TODO retrieve PRF value at WB or at COMMIT1 -> COMMIT2 ?
    /* ROB: Commit */

    //
    // PC -> FETCH -> DECODE -> RENAME -> 
    // Add FW0+FW1 bypass:
    // 
    //    ISSUE    || EXECUTE ||  RETIRE    || COMMIT
    //             ||         ||            ||
    //        _____________________________>||_  Data
    //       /       Req Read Commit PRF    || \
    //       |     ||         ||  ________  || |
    //       |     ||         || / ROB WB   || |
    //       |     ||         || |          || |
    //   PRF>M->M->|| **FUS** ||_/   W-BACK ||++->ARF 
    //  ^    ^  ^  ||       | || \          || \ 
    //  |    |  |  ||       | || |          || |
    //  |    |  \___________/ || | WB       || |
    //  |    |      FW0 (W)   || |          || |
    //  \____\___________________/          || |
    //  |           FW1 (W)      |          || |
    //  \________________________/          || |
    //     Req Read Commit prd              || |
    //  <______________________________________/
    //       Free Reg
    //
    // HAZARD: PRF must do bypass with WB for commit read port

    // TODO: implement FW1 bypass
    // Bypass network
    //                           ____ PRF WRITE
    //                         / 
    // ADDI t1, t0, 1: [*IS*]|[*EX*]|[*WB*]|
    //        \              | ____/|\_______  
    //         \             |/ FW0 |  FW1 | \
    // ADDI t2, t1, 1:       |[*IS*]|[*EX*]|`|
    //          |                   |      |_/
    //          |                   |      /
    // ADDI t3, t1, 1;              |[*IS*]|
    //
    // FW0: Bypass 0 cycle after execute
    // FW1: Bypass 1 cycle after execute
    //  \====> Mandatory because data is still
    //         not in the PRF.
    //
    // Can the address in FW0 collide with the address in FW1?
    
    // Retire stage
    rob_entry_t retire_entry_q, retire_entry_d;
    logic       retire_entry_q_valid, retire_entry_d_valid;
    xlen_t      retire_rdval_q, retire_rdval_d;

    assign retire_entry_d       = rob_pop_data_o; // Wires
    assign retire_entry_d_valid = rob_pop_data_o_valid;
    // Bypass needed here ?
    assign rob_pop_i            = rob_pop_data_o_valid;
    assign prf_raddr[2]         = rob_pop_data_o.prd; // PRF -> ARF port
    assign retire_rdval_d       = prf_rdata[2];
    always_ff @(posedge clk) begin
        if(!rstn) begin 
            retire_entry_q <= '0;
            retire_rdval_q <= '0;
            retire_entry_q_valid <= '0;
        end else begin 
            retire_entry_q <= retire_entry_d;
            retire_rdval_q <= retire_rdval_d;
            retire_entry_q_valid <= retire_entry_d_valid;
        end
    end

    // Output retired inst
    assign retire_entry_o = retire_entry_q;
    assign retire_entry_o_valid = retire_entry_q_valid;

    always_ff @(posedge clk) begin
        if(rob_allocated[rob_retire_id_q]) begin
            $display("Retire: (port0) %s: pc %x (sn=%x) %s",
                rob_pop_data_o.completed ? "SUCCESS " : "FAILURE",
                rob_pop_data_o.pc, rob_pop_data_o.id,
                rob_pop_data_o.needprf2arf ?
                    $sformatf("Writeback : %s:%x",
                        dumpAPReg(rob_pop_data_o.ard, rob_pop_data_o.prd, 1'b1),
                        retire_rdval_q) :
                    "Nothing to wb"
            );
        end else begin 
            $display("Retire: (port0) empty");
        end
    end

    /* Commit stage */
    rob_entry_t commit_entry_i;         // The instruction to commit
    logic       commit_entry_i_valid;   // Is there an instruction to commit
    xlen_t      commit_retire_rdval_i;  // instruction rdVal
    logic       commit_entry_needarfw_i;// Need a writeback ?
    logic       commit_isrd_valid_i;    
    // bq_pop_if.commit bq_pop_io

    assign commit_entry_i        = retire_entry_q;
    assign commit_entry_i_valid  = retire_entry_q_valid;
    assign commit_retire_rdval_i = retire_rdval_q;
    assign commit_entry_needarfw_i = commit_entry_i.needprf2arf;
    assign commit_isrd_valid_i  = commit_entry_i_valid &&
                                  commit_entry_needarfw_i;
    /* Update the architecural register file */
    assign arf_we[0]    = commit_isrd_valid_i;
    assign arf_waddr[0] = commit_entry_i.ard;
    assign arf_wdata[0] = commit_retire_rdval_i;
    /* Branch logic */
    logic is_branch;
    assign is_branch = commit_entry_i.fu == FU_CTRL;
    assign bq_pop_io.pop = commit_entry_i_valid && is_branch;
    always_ff @(posedge clk) begin
        if(commit_entry_i_valid && is_branch) begin
            if (bq_pop_io.missprediction) begin
                $error("Missprediction PC=%x (sn=%x) must jump to: %x (%x)",
                    commit_entry_i.pc,
                    commit_entry_i.id,
                    bq_pop_io.bp.pcnext,
                    bq_pop_io.bp.taken);
            end
        end
    end

    always_ff @(posedge clk) begin
        if(commit_entry_i_valid) begin
            $display("Commit: (port0) %s: pc %x (sn=%x) rd:%x=%x (wb?%d) v:%x",
                commit_entry_i.completed ? "SUCCESS " : "FAILURE",
                commit_entry_i.pc, commit_entry_i.id,
                commit_entry_i.ard, commit_entry_i.prd,
                commit_isrd_valid_i, commit_retire_rdval_i
            );
            $display("TRACE:", handler_pkg::dpi_inst_get_dump(
                32'(commit_entry_i.id),  commit_entry_i.pc));
        end else begin 
            $display("Retire: (port0) empty");
        end
    end



endmodule

