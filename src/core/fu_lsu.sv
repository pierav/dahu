

module forward_from_sq(
    input sq_entry_t [NR_SQ_ENTRIES-1:0] sq_i,
    input sq_id_t sq_issue_id_i,
    input xlen_t load_addr_i,
    input inst_size_t size_i,
    input logic valid_i,
    output logic [8-1:0] fw_mask_o,
    output xlen_t        fw_data_o,
    output logic         stlf_fully_satisfied_o
);
    // 0) Order sq so simply indexing ?
    sq_entry_t [NR_SQ_ENTRIES-1:0] sq_ordered;
    sq_id_t idx;
    always_comb begin
        for (int i = 0; i < NR_SQ_ENTRIES; i++) begin
            idx = (sq_issue_id_i - sq_id_t'(1 - i + NR_SQ_ENTRIES));
            sq_ordered[i] = sq_i[idx];
        end
    end

    // CAM-based STLF (byte-granular merged forwarding)
    localparam int BYTES = XLEN/8;
    localparam int TAG_HI = XLEN-1;
    localparam int TAG_LO = $clog2(BYTES);

    // Format load addr/size
    logic [XLEN-1:TAG_LO] load_tag;
    logic [2:0]           load_bo;
    logic [XLEN/8-1:0]    load_mask;
    assign load_bo = load_addr_i[2:0];
    assign load_tag = load_addr_i[XLEN-1:TAG_LO];
    always_comb begin
        load_mask = '0;
        unique case (size_i)
            SIZE_B: load_mask = (8'b0000_0001 << load_bo);
            SIZE_H: load_mask = (8'b0000_0011 << load_bo);
            SIZE_W: load_mask = (8'b0000_1111 << load_bo);
            SIZE_D: load_mask = 8'hFF;
            default: load_mask = '0;
        endcase
    end

    // 1) Build match vector (CAM comparators)
    logic [NR_SQ_ENTRIES-1:0] match_vec_ord;
    always_comb begin
        if(valid_i) begin
            for (int i = 0; i < NR_SQ_ENTRIES; i++) begin
                // compare DW@
                match_vec_ord[i] = (sq_ordered[i].paddr[XLEN-1:TAG_LO] == load_tag) &&
                                    sq_ordered[i].valid;
                // TODO COMPARE ID !!!
            end
        end else begin
            match_vec_ord = '0;
        end
    end

    // 2) CAM priority merging (youngest -> oldest).
    logic [XLEN/8-1:0] fw_mask;
    xlen_t             fw_data;
    logic [BYTES-1:0] new_bytes;
    always_comb begin
        fw_mask = '0;
        fw_data = '0;
        new_bytes = '0;
        if(valid_i) begin
            // walk from youngest to oldest
            for (int idx = 0; idx < NR_SQ_ENTRIES; idx++) begin
                // only consider candidate entries
                if (match_vec_ord[idx]) begin
                    // pick only bytes that are part of the requested load and not yet forwarded
                    new_bytes = sq_ordered[idx].fmask & load_mask & ~fw_mask;
                    // copy bytes from st_shifted into fw_data
                    for (int b = 0; b < BYTES; b++) begin
                        if (new_bytes[b]) fw_data[8*b +: 8] = sq_ordered[idx].fdata[8*b +: 8];
                    end
                    fw_mask |= new_bytes;
                    // stop early if all bytes satisfied
                    if ((fw_mask & load_mask) == load_mask) begin
                        break;
                    end
                end
            end
        end
    end

    // Outputs results
    assign fw_mask_o = fw_mask;
    assign fw_data_o = fw_data;
    assign stlf_fully_satisfied_o = ((fw_mask & load_mask) == load_mask);

endmodule

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
    dcache_ports_if dcache_ports_io,
    // Squash intf
    squash_if.slave  squash_io
); 

    typedef struct packed {
        logic nc;
    } req_flags_t;

    sq_entry_t [NR_SQ_ENTRIES-1:0] sq;
    sq_entry_t [NR_SQ_ENTRIES-1:0] sq_d;

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
    sq_id_t     sq_commit_id_q, sq_commit_id_d;    
    sq_id_t     sq_pop_id_q,  sq_pop_id_d;    
    sq_id_t     valid_no_commit_cnt; // OK To overflow
    always_comb begin
        // Default assignement
        sq_d = sq;
        sq_commit_id_d = sq_commit_id_q;
        sq_pop_id_d = sq_pop_id_q;
        sq_issue_id_d = sq_issue_id_q;
        /* First commit insts */
        if (sq_commit_i_valid) begin
            sq_d[sq_commit_id_q].commited = '1;
            sq_commit_id_d = sq_commit_id_q + 1;
        end

        // 1 pop port
        if (sq_pop_i) begin
            sq_d[sq_pop_id_q].valid     = '0;
            sq_d[sq_pop_id_q].commited  = '0;
            sq_pop_id_d = sq_pop_id_q + 1;
        end

        valid_no_commit_cnt = 0;
        for (int i = 0; i < NR_SQ_ENTRIES; i++) begin
            valid_no_commit_cnt += sq_id_t'(sq[i].valid && !sq[i].commited);
        end
        /* After update non speculative perform squash if needed */
        if (squash_io.valid) begin
            sq_issue_id_d -= valid_no_commit_cnt; // modulo wrap if needed
            for(int i = 0; i < NR_SQ_ENTRIES; i++) begin
                if(sq[i].valid && !sq[i].commited) begin
                    sq_d[i].valid = '0;
                end
            end
        end else begin
            // Try to issue inst if no flush
            if (sq_push_i_valid) begin
                sq_d[sq_issue_id_q] = sq_push_data_i;
                sq_issue_id_d       = sq_issue_id_q + sq_id_t'(1);
            end
        end
    end

    always_ff @(posedge clk) begin : write_ports
        if (!rstn) begin
            sq_issue_id_q   <= '0;
            sq_commit_id_q  <= '0;
            sq_pop_id_q     <= '0;
            for (int i = 0; i < NR_SQ_ENTRIES; i++) begin
                sq[i].valid     <= '0;
                sq[i].commited  <= '0;
                sq[i].completed <= '0;
            end
        end else begin
            sq              <= sq_d;
            sq_issue_id_q   <= sq_issue_id_d;
            sq_commit_id_q  <= sq_commit_id_d;
            sq_pop_id_q     <= sq_pop_id_d;
        end
    end

    `ifndef SYNTHESIS
    sq_id_t idx;
    always_ff @(negedge clk) begin
        `LOG(LSU, "SQ issueptr=%x commitptr=%x popptr=%x",
            sq_issue_id_q, sq_commit_id_q, sq_pop_id_q);
        for(int i = 0; i < NR_SQ_ENTRIES; i++) begin
            idx = sq_pop_id_q + sq_id_t'(i);
            if(sq[idx].valid) begin
                `LOG(LSU, "SQ[%x]: %s", idx, dump_sq_entry(sq[idx]));
            end
        end
    end
    `endif

    // aynchronous Read ports
    assign sq_pop_entry_o = sq[sq_pop_id_q];
    assign sq_push_i_ready = !sq[sq_issue_id_q].valid; // TODO cpt !

    typedef struct packed {
        fu_output_t result;
    } lq_entry_t;

    /*** Retrieve inputs ***/
    logic[XLEN-1:0] base_address_virt, store_value;
    logic[XLEN-1:0] imm;
    logic is_store;
    logic is_load;
    inst_size_t size;
    assign is_store = fuinput_i.op inside { S };
    assign is_load = fuinput_i.op inside { L, LU };
    assign base_address_virt = fuinput_i.rs1val;
    assign store_value = fuinput_i.rs2val;
    assign imm = fuinput_i.imm;
    assign size = fuinput_i.size;

    /*** Address computation ****/
    logic [XLEN-1:0] address_virt;
    logic translation_done;
    assign address_virt = base_address_virt + imm;
    assign translation_done = fuinput_i_valid; // TODO buffer while translation

    /* Address translation */
    // TODO mmu
    // TODO faults pmp, pma, unaligned access, something else ?
    logic [XLEN-1:0] address_phys;
    assign address_phys = address_virt; 

    // Mask store data for stores
    xlen_t store_wdata;
    logic[8-1:0] store_wmask;
    logic [2:0] bo;
    assign bo = address_phys[2:0];
    always_comb begin
        case (size)
            SIZE_B: begin
                store_wdata = {store_value} << (8*bo);
                store_wmask = 8'b0000_0001 << bo;
            end
            SIZE_H: begin
                store_wdata = {store_value} << (8*bo);
                store_wmask = 8'b0000_0011 << bo;
            end
            SIZE_W: begin
                store_wdata = {store_value} << (8*bo);
                store_wmask = 8'b0000_1111 << bo;
            end
            SIZE_D: begin
                store_wdata = store_value;
                store_wmask = 8'hFF;
            end
        endcase
    end

    /* Insert in LQ/SQ */
    assign sq_push_i_valid          = is_store && translation_done;
    assign sq_push_data_i.pc        = fuinput_i.pc;
    assign sq_push_data_i.id        = fuinput_i.id;
    assign sq_push_data_i.paddr     = address_phys;
    // assign sq_push_data_i.size      = size;
    // assign sq_push_data_i.data      = store_value;
    assign sq_push_data_i.fmask     = store_wmask;
    assign sq_push_data_i.fdata     = store_wdata;
    assign sq_push_data_i.valid     = 1'b1;
    assign sq_push_data_i.commited  = 1'b0;
    assign sq_push_data_i.completed = 1'b0;

    /* Mark completion (after decided if the store is a fault or not) */
    assign store_completion_o.id    = fuinput_i.id;
    assign store_completion_o.valid = sq_push_i_valid; // complete when addr resolved

    // Assume VIPT cache ?

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
    // assign dcache_ports_io.wsize = sq_pop_entry_o.size;
    assign dcache_ports_io.wdata = sq_pop_entry_o.fdata;
    assign dcache_ports_io.wmask = sq_pop_entry_o.fmask;
    assign dcache_ports_io.wvalid = complete_store;
    
    assign sq_pop_i = complete_store;

    /********** LOAD PATH ************/
    // Do not use LQ, but only MSHRs withs pregs id */
    
    // fully associative for now
    typedef logic[$clog2(CACHELINE_SIZE)-1:0] cacheline_bo_t;
    typedef logic[64-$clog2(CACHELINE_SIZE)-1:0] cacheline_addr_t;    
    typedef struct packed {
        cacheline_bo_t bo;
        inst_size_t size;
        logic sext;
    } mshr_wb_entry;

    typedef struct packed {
        cacheline_addr_t paddr;
        mshr_wb_entry [$clog2(NR_WB_PER_MSHR)-1:0] wb_entries;
        logic [$clog2(NR_WB_PER_MSHR)-1:0] allocated_count;
        logic [$clog2(NR_WB_PER_MSHR)-1:0] wb_count;
        logic allocated; // Is in use
        logic completed; // Cache responded
    } mshr_t;

    mshr_t mshr_array [NR_MSHR_ENTRIES];

    // Lookup cache:  Fow now direct memory access stateless
    logic emmit_load_req;
    assign emmit_load_req = is_load && translation_done;
    assign dcache_ports_io.load_a_addr = address_phys;
    assign dcache_ports_io.load_a_valid = emmit_load_req;

    // Lookup store queue
    logic [XLEN/8-1:0] fw_mask;
    xlen_t             fw_data;
    logic stlf_fully_satisfied; // TODO handle 1 cycle load when bypass
    forward_from_sq forward_from_sq(
        .sq_i(sq),
        .sq_issue_id_i(sq_issue_id_q),
        .load_addr_i(address_phys),
        .size_i(fuinput_i.size),
        .valid_i(emmit_load_req),
        .fw_mask_o(fw_mask),
        .fw_data_o(fw_data),
        .stlf_fully_satisfied_o(stlf_fully_satisfied)
    );

    typedef struct packed {
        pc_t pc;
        id_t id;
        preg_id_t prd;
        mshr_wb_entry mshre;
        // From sq
        logic [XLEN/8-1:0] fw_mask;
        xlen_t             fw_data;
    } wait_load_t;

    wait_load_t wait_load_d, wait_load_q;
    assign wait_load_d.pc = fuinput_i.pc;
    assign wait_load_d.id = fuinput_i.id;
    assign wait_load_d.prd = fuinput_i.prd;
    assign wait_load_d.mshre.bo = address_phys[2:0];
    assign wait_load_d.mshre.size = fuinput_i.size;
    assign wait_load_d.mshre.sext = fuinput_i.op != LU;
    assign wait_load_d.fw_mask = fw_mask;
    assign wait_load_d.fw_data = fw_data;

    always_ff @(posedge clk) begin
        if(emmit_load_req) begin // No need to reset or flush
            wait_load_q <= wait_load_d;
        end
    end

    // Merge data from SQ and Cache
    xlen_t load_data_merged;
    always_comb begin
        for (int b = 0; b < XLEN/8; b++) begin
            load_data_merged[8*b +: 8] = wait_load_q.fw_mask[b] ? 
                    wait_load_q.fw_data[8*b +: 8] :
                    dcache_ports_io.load_d_data[8*b +: 8];
        end
    end

    // Load extract + sign/zero extension
    xlen_t load_data_sext;
    xlen_t shifted;
    always_comb begin
        shifted = load_data_merged >> (8*wait_load_q.mshre.bo);
        unique case (wait_load_q.mshre.size)
            SIZE_B: load_data_sext = wait_load_q.mshre.sext ? 
                {{XLEN-8{shifted[7]}},  shifted[7:0]} : {{XLEN-8{1'b0}}, shifted[7:0]};
            SIZE_H: load_data_sext = wait_load_q.mshre.sext ?
                {{XLEN-16{shifted[15]}}, shifted[15:0]} : {{XLEN-16{1'b0}}, shifted[15:0]};
            SIZE_W: load_data_sext = wait_load_q.mshre.sext ?
                {{XLEN-32{shifted[31]}}, shifted[31:0]} : {{XLEN-32{1'b0}}, shifted[31:0]};
            SIZE_D: load_data_sext = shifted; // full 64-bit load
        endcase
    end
    
    `ifndef SYNTHESIS
    always_ff @(negedge clk) begin
        if(dcache_ports_io.load_d_valid) begin
            `LOG(LSU, "LOAD COMPLETE PC:%x (sn=%x), D=%x, fw_mask=%x, fw_data=%x (merged:%x)",
                 wait_load_q.pc, wait_load_q.id, load_data_sext,
                    wait_load_q.fw_mask, wait_load_q.fw_data, load_data_merged);
        end
    end
    `endif

    /* Output (only for LQ and AMO) */
    assign fuoutput_o.pc    = wait_load_q.pc;
    assign fuoutput_o.id    = wait_load_q.id;
    assign fuoutput_o.prd   = wait_load_q.prd;
    assign fuoutput_o.rdval = load_data_sext;
    assign fuoutput_o_valid = dcache_ports_io.load_d_valid;

    /* Fu ready: Both store and load must be ready now */
    assign fuinput_i_ready  = sq_push_i_ready && // Store ready
                              dcache_ports_io.load_a_ready; // Load port ready
    
    // 4 sources of hit by priority
    // - STLF (1 cycle latency)
    // - already completed MSHR (2c) (use MSHR as a cache)
    // - 


    // @V0 -> $@P0,  @V1 -> $@P1 
    // 4 cases:
    // @V0 == @V1 && @P0 == @P1 : Ideal Case
    // @V0 != @V1 && @P0 == @P1 : We must always match PTAG !
    // @V0 == @V1 && @P0 != @P1 : MultiProcessus: match TAG !
    // @V0 != @V1 && @P0 != @P1 : Don't care

endmodule







