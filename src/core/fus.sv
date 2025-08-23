import C::*;

module fus #() (
    input logic clk,
    input logic rstn,
    // From issue stage
    input fu_input_t fuinput_i,
    input logic fuinput_i_valid,
    output fu_bitvector_t fuinput_i_ready,
    // Write back
    output fu_output_t    fuoutput_o[NR_WB_PORTS],
    output wb_bitvector_t fuoutput_o_valid,
    // Completion ports
    output completion_port_t completion_ports_o[NR_COMPL_PORTS],
    // Core   
    input rob_entry_t   retire_entry_i,
    input logic         retire_entry_i_valid,
    csr_if.master csr_io,

    // From/To BP
    input bp_t bp_i,
    input logic bp_i_valid,
    output logic bp_i_ready,

    // Caches
    dcache_ports_if dcache_ports_io

);

    fu_input_t      fu_inputs[NB_FU];
    fu_bitvector_t  fu_inputs_readys;
    fu_bitvector_t  fu_inputs_valids;

    fu_output_t     fu_outputs[NB_FU];
    fu_bitvector_t  fu_outputs_valids;

    completion_port_t store_completion;
    completion_port_t branch_completion;

    // assign the instruction to the corresponding FU
    // TODO chandle mulitple ALU and multiple ISSUE
    // TODO perform port allocation at issue ?
    always_comb begin
        for (int fu_idx = 0; fu_idx < NB_FU; fu_idx++) begin
            if(fuinput_i.fu == fu_t'(fu_idx)) begin
                fu_inputs[fu_idx] = fuinput_i;
                fu_inputs_valids[fu_idx] = fuinput_i_valid;
            end else begin
                fu_inputs[fu_idx] = '0;
                fu_inputs_valids[fu_idx] = '0;
            end
        end
    end

    /* ALU */
    fu_alu #() fu_alu (
        .clk(clk),
        .rstn(rstn),
        .fuinput_i(fu_inputs[FU_ALU]),
        .fuoutput_o(fu_outputs[FU_ALU])
    );
    assign fu_inputs_readys[FU_ALU] = '1; // Always ready
    assign fu_outputs_valids[FU_ALU] = fu_inputs_valids[FU_ALU];

    /* LSU */
    fu_lsu #() fu_lsu (
        .clk(clk),
        .rstn(rstn),
        .fuinput_i(fu_inputs[FU_LSU]),
        .fuinput_i_valid(fu_inputs_valids[FU_LSU]),
        .fuinput_i_ready(fu_inputs_readys[FU_LSU]),
        .fuoutput_o(fu_outputs[FU_LSU]),
        .fuoutput_o_valid(fu_outputs_valids[FU_LSU]),
        .retire_entry_i(retire_entry_i),
        .retire_entry_i_valid(retire_entry_i_valid),
        .store_completion_o(store_completion),
        .dcache_ports_io(dcache_ports_io)
    );

    /* MISC */
    logic fu_none_completion_o_valid;
    fu_csr #() fu_csr (
        .clk(clk),
        .rstn(rstn),
        .fuinput_i(fu_inputs[FU_NONE]),
        .fuinput_i_valid(fu_inputs_valids[FU_NONE]),
        .fuinput_i_ready(fu_inputs_readys[FU_NONE]),
        .fuoutput_o(fu_outputs[FU_NONE]),
        .fuoutput_o_valid(fu_outputs_valids[FU_NONE]),
        .completion_o_valid(fu_none_completion_o_valid),
        .retire_entry_i(retire_entry_i),
        .retire_entry_i_valid(retire_entry_i_valid),
        .csr_io(csr_io)
    );

    /* Branch */
    fu_branch fu_branch (
        .clk(clk),
        .rstn(rstn),
        .fuinput_i(fu_inputs[FU_CTRL]),
        .fuinput_i_valid(fu_inputs_valids[FU_CTRL]),
        .fuinput_i_ready(fu_inputs_readys[FU_CTRL]),
        .branch_completion_o(branch_completion),
        .bp_i(bp_i),
        .bp_i_valid(bp_i_valid),
        .bp_i_ready(bp_i_ready),
        .retire_entry_i(retire_entry_i),
        .retire_entry_i_valid(retire_entry_i_valid)
    );
    // Nothing to write back
    assign fu_outputs_valids[FU_CTRL] = '0;
    assign fu_outputs[FU_CTRL] = '0;
    
    /* TODO IMPLEMENT */
    /* FU STUBS */
    always_comb begin
        for (int fu_idx = 0; fu_idx < NB_FU; fu_idx++) begin
            if(!(fu_t'(fu_idx) inside {FU_ALU, FU_LSU, FU_NONE})) begin
                fu_inputs_readys[fu_idx] = '0; // Not ready
                fu_outputs_valids[fu_idx] = '0; // No results
                fu_outputs[fu_idx] = '0;
            end
        end
    end
    /* Write back */
    // How do we handle multiple write-backs? (FU)
    // -1) 1 port per group (reduce drasticly the performance)
    // 0) 1wb per fu (cannot scale)
    // 1) Completion buffers (costly)
    // 2) Do we need to buffer ("can") the result for instructions with latency > 1?
    // Does the FU already have this buffer?
    // Do we simply repeat iteration n in a loop?
    // We can stall the port for FUs with latency 1.
    // 3) Systolic buffer ?

    // For now 1 FU -> 1WB port
    assign fuoutput_o[0] = fu_outputs[FU_ALU];
    assign fuoutput_o_valid[0] = fu_outputs_valids[FU_ALU];
    assign completion_ports_o[0].id = fuoutput_o[0].id;
    assign completion_ports_o[0].valid = fuoutput_o_valid[0];

    assign fuoutput_o[2]       = fu_outputs[FU_LSU];
    assign fuoutput_o_valid[2] = fu_outputs_valids[FU_LSU];
    assign completion_ports_o[2].id = fuoutput_o[2].id;
    assign completion_ports_o[2].valid = fuoutput_o_valid[2];
    // TODO multiplex FU_NONE !
    assign fuoutput_o[1] = fu_outputs[FU_NONE];
    assign fuoutput_o_valid[1] = fu_outputs_valids[FU_NONE];
    assign completion_ports_o[1].id = fuoutput_o[1].id;
    assign completion_ports_o[1].valid = fu_none_completion_o_valid;

     // The others are for stores and branch
    assign completion_ports_o[0 + NR_WB_PORTS] = store_completion;
    assign completion_ports_o[1 + NR_WB_PORTS] = branch_completion;
    
    // Send issue reayd funcs units
    assign fuinput_i_ready = fu_inputs_readys;

    /* Output Completion */
    // always_comb begin
    //     // The firsts completion ports are for WB ports
    //     for (int wb_i = 0; wb_i < NR_WB_PORTS; wb_i++) begin
    //         completion_ports_o[wb_i].id = fuoutput_o[wb_i].id;
    //         completion_ports_o[wb_i].valid = fuoutput_o_valid[wb_i];
    //     end
    // end

endmodule

