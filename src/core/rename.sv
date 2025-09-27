import C::*;

module rename #() (
    input clk,
    input rstn,
    input di_t di_i,        // Instruction to process
    input logic di_i_valid,  // Instruction to process is here
    output logic di_i_ready, // Ready to decode new one
    
    output di_t di_o,        // The renammed instruction 
    output logic di_o_valid, // The instruction is renammed
    input logic di_o_ready,   // The next stage is ready

    input rob_entry_t retire_entry_i,
    input logic retire_entry_i_valid,
    // Squash intf
    squash_if.slave  squash_io
);

    /* Rename Map Table */ 
    areg_id_t rmt_read_id[2];       // input
    preg_id_t rmt_reads[2];         // output
    logic     rmt_reads_valid[2];   // output
    preg_id_t rmt_write;            // input
    areg_id_t rmt_write_areg;       // input
    logic     rmt_write_valid;      // input
    // OUTDATED
    logic     rmt_clear_i;          // input Clear
    areg_id_t rmt_clear_id_i;       // input Clear Areg
    preg_id_t rmt_clear_preg_i;     // input Clear Preg

    // the internal rmt
    preg_id_t rmt [ARFSIZE];
    id_t rmt_id [ARFSIZE];
    logic [ARFSIZE-1:0] rmt_valid;

    // areg_id_t reverse_rmt[PRFSIZE];
    // logic [PRFSIZE-1:0] reverse_rmt_valid;

    // t0->r10->t0
    // t1->r11->t1
    // t2->r12->t2
    // free r10 but still mapped to t0
    // free r11 ...
    // t4->r10-::->t0<=AR // We must invalidate t0->r10 // r10 must have committed
    // t1->r11-::->t1<=AR// We also must invalidate t1->r11, but rewrite the same
    // There is write precedence

    // Asynchronous Read ports
    assign rmt_reads[0] = rmt[rmt_read_id[0]];
    assign rmt_reads[1] = rmt[rmt_read_id[1]];
    assign rmt_reads_valid[0] = rmt_valid[rmt_read_id[0]];
    assign rmt_reads_valid[1] = rmt_valid[rmt_read_id[1]];
    areg_id_t old_areg;
    preg_id_t old_preg;
    // areg_id_t areg;
    // write port
    always_ff @(posedge clk) begin
        if(!rstn) begin
            rmt_valid <= 0;
            // No need to initialise reverse rmt
            // reverse_rmt <= '0;
        end else begin
            if(squash_io.valid) begin
                rmt_valid <= 0; // Clear RMT
            end else begin
                if(rmt_write_valid) begin
                    // First invalidate old entry if needed
                    // old_areg <= reverse_rmt[rmt_write]; // Asynchronous read
                    // old_preg <= rmt[old_areg];
                    // TODO no broadcast
                    for(int i = 0; i < ARFSIZE; i++) begin
                        // areg = areg_id_t'(i);
                        if (rmt[i] == rmt_write) begin
                            rmt_valid[i] <= '0;
                        end
                    end
                    // if (reverse_rmt_valid[old_preg]) begin
                    //     reverse_rmt_valid[old_preg] <= 0;
                    //     rmt_valid[old_areg] <= '0;
                    // end
                
                    // Then update the entry or anothe with new mapping
                    rmt[rmt_write_areg]       <= rmt_write;
                    rmt_valid[rmt_write_areg] <= 1'b1;
                    rmt_id[rmt_write_areg]    <= di_i.id;
                    // Also update the reverse rmt
                    // reverse_rmt[rmt_write]  <= rmt_write_areg;
                    // reverse_rmt_valid[rmt_write] <= '1;
                end
            end
        end
    end

    `ifndef SYNTHESIS
    string str;
    always_comb begin
        str = "Rename RMT: [";
        for (int i = 0; i < ARFSIZE; i++) begin
            if (rmt_valid[i]) begin
                str = {str, $sformatf("%s, ",
                    dumpAPReg(areg_id_t'(i), rmt[i], rmt_valid[i]))};
            end
        end
        str = {str, "]"};
    end
    always_ff @(negedge clk) begin
        `LOG(REN, str);
        if (rmt_write_valid) begin
            `LOG(REN, "(RMTW: %s<-%s)",
                dumpAReg(rmt_write_areg),
                dumpPReg(rmt_write, 1'b1));
        end
        // $write("Rename Reverse RMT: [");
        // for(int i = 0; i < PRFSIZE; i++) begin
        //     preg_id_t preg = preg_id_t'(i);
        //     $write("%s->%s, ",
        //         dumpPReg(preg, reverse_rmt_valid[preg]),
        //         dumpAReg(reverse_rmt[preg]));
        // end
        // $write("]");
    end
    `endif

    /* Allocator (for now use a counter) */
    logic allocate;             // input
    logic       free_valid;     // input
    preg_id_t   free_prd;       
    logic can_allocate;         // output
    preg_id_t allocated_preg;   // output
    preg_id_t counter_q, counter_d;
    logic[PRFSIZE-1+1:0] inflights_q, inflights_d;
    assign can_allocate = !inflights_q[PREG_ID_BITS];
    assign allocated_preg = counter_q;
    always_comb begin : allocator
        // Default value
        counter_d = counter_q;
        inflights_d = inflights_q;
        // Allocate
        if(allocate && can_allocate) begin
            counter_d = counter_q + 1;
            inflights_d = inflights_d + 1;
        end
        // Release
        // TODO 0 cycle release->alloc
        if(free_valid) begin
            // TODO check free ID
            `ifndef SYNTHESIS
            $asserton(free_prd == (counter_q + inflights_q));
            `endif
            inflights_d = inflights_d - 1;
        end
    end
    always_ff @(posedge clk) begin
        if(!rstn) begin 
            counter_q <= '0;
            inflights_q <= '0;
        end else begin
            if(squash_io.valid) begin
                counter_q <= '0; // Symply reset the allocator :)
                inflights_q <= '0;
            end else begin
                counter_q <= counter_d;
                inflights_q <= inflights_d;
            end
        end
    end


    /* Rename */
    /* Commit -> Free */
    logic free_reg_i;
    areg_id_t free_areg_id_i;
    preg_id_t free_preg_id_i;
    assign free_reg_i = retire_entry_i_valid &&
                        retire_entry_i.needprf2arf;
    assign free_areg_id_i = retire_entry_i.ard;
    assign free_preg_id_i = retire_entry_i.prd;
    // Give back id to allocator 
    assign free_valid = free_reg_i;
    assign free_prd   = free_preg_id_i;
    // Clear old rmt mapping
    assign rmt_clear_i = free_reg_i;
    assign rmt_clear_id_i = free_areg_id_i;
    assign rmt_clear_preg_i = free_preg_id_i;
    
    /* Rename -> Allocator */
    assign allocate = di_i_valid &&
                      di_o_ready && // Both R/V ok
                      can_allocate &&
                      di_i.si.rd_valid;

    /* Allocator -> RMT */
    assign rmt_write = allocated_preg;
    assign rmt_write_areg = di_i.si.rd;
    assign rmt_write_valid = allocate;

    /* RMT <-> Rename */ // TODO care rs1 valid ?
    assign rmt_read_id[0] = di_i.si.rs1;
    assign rmt_read_id[1] = di_i.si.rs2;

    /* Save mechanish for uop */
    preg_id_t last_rs1_q;
    logic last_rs1_valid_q;
    always_ff @(posedge clk) begin
        if(di_i_valid && di_i.is_uop && !di_i.is_uop_last) begin
            last_rs1_q <= rmt_reads[0];
            last_rs1_valid_q <= rmt_reads_valid[0];
        end
    end
    /* Final output */
    always_comb begin : output_inst
        di_o                 = di_i; // Copy everytging !
        di_o.prs1            = rmt_reads[0];
        di_o.prs1_renammed   = rmt_reads_valid[0];
        di_o.prs2            = rmt_reads[1];
        di_o.prs2_renammed   = rmt_reads_valid[1];
        di_o.prd             = allocated_preg;
         if(di_i.is_uop && di_i.is_uop_last) begin // Take saved one
            di_o.prs1           = last_rs1_q;
            di_o.prs1_renammed  = last_rs1_valid_q;
        end
    end
    logic stall;
    assign stall = di_i_valid && di_i.si.rd_valid && !can_allocate;
    /* Ready valid */
    assign di_i_ready = di_o_ready && !stall;
    assign di_o_valid = di_i_valid && !stall; // TODO clked

    `ifndef SYNTHESIS
    string cause;
    always_comb begin
        cause = "";
        if(di_i_valid) begin
            if(stall) begin
                cause = "OUT OR PR";
            end else begin
                cause = "SUCCESS  ";
            end
        end
    end
    always_ff @(posedge clk) begin
        if(!di_i_ready) begin
            `LOG(REN, "Rename: (port0) output is not ready");
        end else if (!di_i_valid) begin
            `LOG(REN, "Rename: (port0) no valids inputs");
        end else if (stall) begin
            `LOG(REN, "Rename: (port0) out of pregs");
        end else begin 
            `LOG(REN, "Rename: (port0) %s: pc %x (sn=%x) %s <- %s %s (allocate?%x)",
                "SUCCESS  ",
                di_o.si.pc, di_o.id,
                di_o.si.rd_valid ?
                    dumpAPReg(di_o.si.rd, di_o.prd, 1'b1) : " ",
                di_o.si.rs1_valid ?
                    dumpAPReg(di_o.si.rs1, di_o.prs1, di_o.prs1_renammed) : " ",
                di_o.si.rs2_valid ?
                    dumpAPReg(di_o.si.rs2, di_o.prs2, di_o.prs2_renammed) : " ",
                allocate
            );
        end
    end
    `endif
endmodule

