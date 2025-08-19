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
    input logic retire_entry_i_valid

);

    /* Rename Map Table */ 
    areg_id_t rmt_read_id[2];       // input
    preg_id_t rmt_reads[2];         // output
    logic     rmt_reads_valid[2];   // output
    preg_id_t rmt_write;            // input
    areg_id_t rmt_write_id;         // input
    logic rmt_write_valid;          // input
    // the internal rmt
    preg_id_t rmt [ARFSIZE-1:0];
    logic [ARFSIZE-1:0] rmt_valid;
    // Read ports
    assign rmt_reads[0] = rmt[rmt_read_id[0]];
    assign rmt_reads[1] = rmt[rmt_read_id[1]];
    assign rmt_reads_valid[0] = rmt_valid[rmt_read_id[0]];
    assign rmt_reads_valid[1] = rmt_valid[rmt_read_id[1]];
    // write port
    always_ff @(posedge clk) begin
        if(!rstn) begin
            rmt_valid <= 0;
        end else begin
            if(rmt_write_valid) begin
                rmt[rmt_write_id]       <= rmt_write;
                rmt_valid[rmt_write_id] <= 1'b1;
            end
        end
    end

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
            $asserton(free_prd == (counter_q + inflights_q));
            inflights_d = inflights_d - 1;
        end
    end
    always_ff @(posedge clk) begin
        if(!rstn) begin 
            counter_q <= 0;
            inflights_q <= 0;
        end else begin
            counter_q <= counter_d;
            inflights_q <= inflights_d;
        end
    end


    /* Rename */
    /* Commit -> Free */
    assign free_valid = retire_entry_i_valid &&
                        retire_entry_i.needprf2arf;
    assign free_prd   = retire_entry_i.prd;

    /* Rename -> Allocator */
    assign allocate = di_i_valid && can_allocate && di_i.si.rd_valid;

    /* Allocator -> RMT */
    assign rmt_write = allocated_preg;
    assign rmt_write_id = di_i.si.rd;
    assign rmt_write_valid = allocate;

    /* RMT <-> Rename */ // TODO care rs1 valid ?
    assign rmt_read_id[0] = di_i.si.rs1;
    assign rmt_read_id[1] = di_i.si.rs2;
    
    /* Final output */
    assign di_o.si              = di_i.si;
    assign di_o.id              = di_i.id;
    assign di_o.fault           = di_i.fault;
    assign di_o.valid           = di_i.valid;
    assign di_o.prs1            = rmt_reads[0];
    assign di_o.prs1_renammed   = rmt_reads_valid[0];
    assign di_o.prs2            = rmt_reads[1];
    assign di_o.prs2_renammed   = rmt_reads_valid[1];
    assign di_o.prd             = allocated_preg;

    logic stall;
    assign stall = di_i_valid && di_i.si.rd_valid && !can_allocate;
    /* Ready valid */
    assign di_i_ready = di_o_ready && !stall;
    assign di_o_valid = di_i_valid && !stall; // TODO clked


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
            $display("Rename: (port0) output is not ready");
        end else if (!di_i_valid) begin
            $display("Rename: (port0) no valids inputs");
        end else begin 
            $display("Rename: (port0) %s: pc %x (sn=%d) rd:%d:%d prs1:%d:%d(%d) prs2:%d:%d(%d)",
                cause,
                di_o.si.pc, di_o.id,
                di_o.si.rd,  di_o.prd,
                di_o.si.rs1, di_o.prs1, di_o.prs1_renammed,
                di_o.si.rs2, di_o.prs2, di_o.prs2_renammed
            );
        end
    end

endmodule

