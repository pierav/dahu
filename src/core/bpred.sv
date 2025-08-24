import C::*;

module bpred #()(
    input  logic clk,
    input  logic rstn,
    // From fetch
    input   logic valid,
    input   logic ready,
    input   pc_t pc,
    // To fetch 
    // Asynchronous 0 cycle latency prediction
    output bp_t  prediction_0
);
    // TODO: BTB, IPRED, TAGE, RAS
    // Can we achieve high accuracy, 1 cycle latency ?
    // Minimum to fit : BTB, Extended-GSHARE, RAS
    // Full BTB ? Do we have to predict if is_branch ?

    assign prediction_0.pcnext = pc + 4; // Use naive pc+4
    assign prediction_0.taken  = '0; // No taken
endmodule

