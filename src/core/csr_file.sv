import C::*;

module csr_file #()(
  input  logic clk,
  input  logic rstn,
  csr_if.slave csr_io
);
    // Stub CSR hardwired to 0 TODO
    assign csr_io.rdata = '0;

    always_ff @(posedge clk) begin
        if (csr_io.wvalid) begin
            $warning("UNIMPLEMENTED CSR WRITE at @=%x, D=%x",
                csr_io.waddr, csr_io.wdata);
        end
    end
endmodule
