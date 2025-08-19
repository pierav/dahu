
module fu_lsu #() (
    input logic clk,
    input logic rstn,
    input fu_input_t fuinput_i,
    input logic      fuinput_i_valid,
    output logic      fuinput_i_ready,
    output fu_output_t fuoutput_o,
    output logic       fuoutput_o_valid,
    // Core   
    input rob_entry_t   retire_entry_i,
    input logic         retire_entry_i_valid,
    // Store do not use the fu_output_t port
    output completion_port_t store_completion_o,
    // To dcache
    dcache_ports_if dcache_ports_io
); 

    typedef struct packed {
        logic nc;
    } req_flags_t;

    typedef struct packed {
        id_t id;            // Debug only ?
        xlen_t pc;          // Debug only ?
        xlen_t paddr;       // the paddr
        inst_size_t size;   // DW, W, H or Byte
        xlen_t data;

        logic valid;        // Entry used
        logic commited;     // Entry used
        logic completed;
    } sq_entry_t;

    sq_entry_t [NR_SQ_ENTRIES-1:0] sq;

    // SQ Inputs
    logic       sq_push_i_valid; // Input
    logic       sq_push_i_ready; // Output
    sq_entry_t  sq_push_data_i;
    // COmmit port
    logic       sq_commit_i_valid;
    sq_id_t     sq_commit_id_i;
    // Pop port
    /*output*/ sq_entry_t  sq_pop_entry_o;
    /*input */ logic       sq_pop_i;


    // SQ pointers
    sq_id_t     sq_issue_id_q, sq_issue_id_d;
    assign      sq_issue_id_d = sq_issue_id_q + 1;
    sq_id_t     sq_commit_id_q, sq_commit_id_d;    
    assign      sq_commit_id_d = sq_commit_id_q + 1;
    sq_id_t     sq_pop_id_q,  sq_pop_id_d;    
    assign      sq_pop_id_d = sq_pop_id_q + 1;
    // Write ports
    always_ff @(posedge clk) begin : write_ports
        if(!rstn) begin
            sq_issue_id_q <= '0;
            sq_commit_id_q <= '0;
            sq_pop_id_q <= '0;
            for (int i = 0; i < NR_SQ_ENTRIES; i++) begin
                sq[i].valid <= '0;
                sq[i].commited <= '0;
                sq[i].completed <= '0;
            end
        end else begin
            // 1 write port
            if (sq_push_i_valid) begin
                sq[sq_issue_id_q] <= sq_push_data_i;
                sq_issue_id_q <= sq_issue_id_d;
            end
            // 1 commit port
            if (sq_commit_i_valid) begin
                sq[sq_commit_id_q].commited <= '1;
                sq_commit_id_q <= sq_commit_id_d;
            end
            // 1 pop port
            if (sq_pop_i) begin
                sq[sq_pop_id_q].valid <= '0;
                sq_pop_id_q <= sq_pop_id_d;
            end
        end
    end
    // Read ports
    assign sq_pop_entry_o = sq[sq_pop_id_q];
    assign sq_push_i_ready = !sq[sq_issue_id_q].valid; // TODO cpy ?

    typedef struct packed {
        fu_output_t result;
    } lq_entry_t;

    /*** Retrieve inputs ***/
    logic[XLEN-1:0] base_address_virt, store_value;
    logic[XLEN-1:0] imm;
    logic is_store;

    assign is_store = fuinput_i.op inside { S };
    assign base_address_virt = fuinput_i.rs1val;
    assign store_value = fuinput_i.rs2val;
    assign imm = fuinput_i.imm;
    
    /*** Address computation ****/
    logic [XLEN-1:0] address_virt;
    assign address_virt = base_address_virt + imm;
    logic translation_done = fuinput_i_valid; // TODO buffer while translation

    /* Address translation */
    // TODO mmu
    // TODO faults pmp, pma, unaligned access, something else ?
    logic [XLEN-1:0] address_phys;
    assign address_phys = address_virt; 

    /* Insert in LQ/SQ */
    assign sq_push_i_valid          = is_store && translation_done;
    assign sq_push_data_i.pc        = fuinput_i.pc;
    assign sq_push_data_i.id        = fuinput_i.id;
    assign sq_push_data_i.paddr     = address_phys;
    assign sq_push_data_i.size      = fuinput_i.size;
    assign sq_push_data_i.data      = store_value;
    assign sq_push_data_i.valid     = 1'b1;
    assign sq_push_data_i.commited  = 1'b0;
    assign sq_push_data_i.completed = 1'b0;

    /* Mark completion (after decided if the store is a fault or not) */
    assign store_completion_o.id    = fuinput_i.id;
    assign store_completion_o.valid = sq_push_i_valid; // complete when addr resolved

    // Assume VIPT cache ?

    /* Output (only for LQ and AMO) */
    // TODO
    assign fuoutput_o.pc    = '0;
    assign fuoutput_o.id    = '0;
    assign fuoutput_o.prd   = '0;
    assign fuoutput_o.rdval = '0;
    assign fuoutput_o_valid = '0;

    /* */
    assign fuinput_i_ready  = sq_push_i_ready; // For now only SQ

    /* Commit path */
    assign sq_commit_i_valid = retire_entry_i_valid &&
                               retire_entry_i.needSQfree;

    /* Cache store port */
    logic complete_store;
    /* three condition to complete a store (complete_store):
     * 1) Cache must be ready
     * 2) The latest sq entry must be valid
     * 3) and no more speculative (<=> commited)
     *
     * When a store is sent to cache, it is also removed
     * from the store queue
     */
    assign complete_store = dcache_ports_io.wready &&
                            sq_pop_entry_o.valid &&
                            sq_pop_entry_o.commited;
    assign dcache_ports_io.waddr = sq_pop_entry_o.paddr;
    assign dcache_ports_io.wsize = sq_pop_entry_o.size;
    assign dcache_ports_io.wdata = sq_pop_entry_o.data;
    assign dcache_ports_io.wvalid = complete_store;
    
    assign sq_pop_i = complete_store;

endmodule
