
module fu_lsu #() (
    input logic clk,
    input logic rstn,
    input fu_input_t fuinput_i,
    input logic      fuinput_i_valid,
    output logic      fuinput_i_ready,
    output fu_output_t fuoutput_o,
    output logic       fuoutput_o_valid
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
    assign      sq_push_i_ready = !sq[sq_issue_id_q].valid;

    // SQ pointers
    sq_id_t     sq_issue_id_q, sq_issue_id_d;
    assign      sq_issue_id_d = sq_issue_id_q + 1;
    sq_id_t     sq_commit_id_q, sq_commit_id_d;    
    assign      sq_commit_id_d = sq_commit_id_q + 1;
    always_ff @(posedge clk) begin
        if(!rstn) begin
            sq_issue_id_q <= '0;
            sq_commit_id_q <= '0;
            for (int i = 0; i < NR_SQ_ENTRIES; i++) begin
                sq[i].valid <= '0;
                sq[i].commited <= '0;
                sq[i].completed <= '0;
            end
        end else begin
            // 1 write port
            if(sq_push_i_valid) begin
                sq[sq_issue_id_q] <= sq_push_data_i;
                sq_issue_id_q <= sq_issue_id_d;
            end
            // 1 commit port

        end
    end


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

    /* Address translation */
    // TODO mmu
    // TODO faults pmp, pma, unaligned access, something else ?
    logic [XLEN-1:0] address_phys;
    assign address_phys = address_virt; 

    /* Insert in LQ/SQ */
    assign sq_push_i_valid          = is_store && fuinput_i_valid;
    assign sq_push_data_i.pc        = fuinput_i.pc;
    assign sq_push_data_i.id        = fuinput_i.id;
    assign sq_push_data_i.paddr     = address_phys;
    assign sq_push_data_i.size      = fuinput_i.size;
    assign sq_push_data_i.data      = store_value;
    assign sq_push_data_i.valid     = 1'b1;
    assign sq_push_data_i.commited  = 1'b0;
    assign sq_push_data_i.completed = 1'b0;
   

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

endmodule
