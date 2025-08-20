
module regfile #(
    parameter int WIDTH   = 64,   // Data width
    parameter int NREGS   = 32,   // Number of registers
    parameter int NREAD   = 2,    // Number of read ports
    parameter int NWRITE  = 1     // Number of write ports
) (
    input  logic clk,
    input  logic rstn,

    // Write ports
    input  logic [NWRITE-1:0]                    we,      // Write enables
    input  logic [NWRITE-1:0][$clog2(NREGS)-1:0] waddr,   // Write addresses
    input  logic [NWRITE-1:0][WIDTH-1:0]         wdata,   // Write data

    // Read ports
    input  logic [NREAD-1:0][$clog2(NREGS)-1:0]  raddr,   // Read addresses
    output logic [NREAD-1:0][WIDTH-1:0]          rdata    // Read data
);

    // Register array
    logic [WIDTH-1:0] regs [0:NREGS-1];

    //  Reset initialization ?
    always_ff @(posedge clk) begin
        if (!rstn) begin
            for (int i = 0; i < NREGS; i++) begin
                regs[i] <= '0;
            end
        end else begin
            // Handle multiple write ports — priority order: port 0 highest
            for (int w = 0; w < NWRITE; w++) begin
                if (we[w]) begin
                    regs[waddr[w]] <= wdata[w];
                end
            end
        end
    end

    // Combinational reads with write-bypass
    for (genvar r = 0; r < NREAD; r++) begin : READ_PORTS
        always_comb begin
            rdata[r] = regs[raddr[r]]; // Default from register array
            for (int w = 0; w < NWRITE; w++) begin
                if (we[w] && (waddr[w] == raddr[r])) begin
                    rdata[r] = wdata[w];
                end
            end
        end
    end

endmodule
