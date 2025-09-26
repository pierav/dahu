module uart8250 (
    input  logic          clk,
    input  logic          rstn,
    // Read port
    input logic           rvalid,
    input logic[2:0]      raddr,
    output logic[8-1:0]   rdata,
    // Write port
    input logic           wvalid,
    input logic[2:0]      waddr,
    input logic[8-1:0]    wdata
);

    // https://en.wikibooks.org/wiki/Serial_Programming/8250_UART_Programming
    // https://github.com/riscv-software-src/riscv-isa-sim/blob/master/riscv/ns16550.cc#L91
    parameter logic[3-1:0] RBR = 0; /* In:  Recieve Buffer Register */
    parameter logic[3-1:0] THR = 0; /* Out: Transmitter Holding Register */
    parameter logic[3-1:0] DLL = 0; /* Out: Divisor Latch Low */
    parameter logic[3-1:0] IER = 1; /* I/O: Interrupt Enable Register */
    parameter logic[3-1:0] DLM = 1; /* Out: Divisor Latch High */
    parameter logic[3-1:0] FCR = 2; /* Out: FIFO Control Register */
    parameter logic[3-1:0] IIR = 2; /* I/O: Interrupt Identification Register */
    parameter logic[3-1:0] LCR = 3; /* Out: Line Control Register */
    parameter logic[3-1:0] MCR = 4; /* Out: Modem Control Register */
    parameter logic[3-1:0] LSR = 5; /* In:  Line Status Register */
    parameter logic[3-1:0] MSR = 6; /* In:  Modem Status Register */
    parameter logic[3-1:0] SCR = 7; /* I/O: Scratch Register */

    typedef struct packed {
        logic [7:7] dlab;   /* 0x80: Divisor Latch Access Bit  */
        logic [6:6] sbe;    /* Set Break Enable */
        logic [5:3] ps;     /* Parity Select */
        logic [2:2] sb;     /* Stop bit */
        logic [1:0] wl;     /* World length */
    } reg_lcr_t;

    typedef struct packed {
        logic [7:6] tl;     /* Trigger level */
        logic [5:5] enable64Bfifo;
        logic [4:4] reserved;
        logic [3:3] dmams;  /* DMA Mode Select */
        logic [2:2] ctfifo; /* Clear Transmit FIFO  */
        logic [1:1] crfifo; /* Clear Receive FIFO  */
        logic [0:0] efifos; /* Enable FIFOs  */
    } reg_fcr_t;

    // Line Status Register (LSR)
     typedef struct packed {
        logic [7:7] fofoe;  /* Fifo error */
        logic [6:6] temt;   /* Transmitter empty */
        logic [5:5] thre;   /* Transmit-hold-register empty */
        logic [4:4] bi;     /* Break Interrupt */
        logic [3:3] fe;     /* Framing Error  */
        logic [2:2] pe;     /* Parity Error */
        logic [1:1] oe;     /* Overrun Error */
        logic [0:0] dr;     /* Data Ready  */
     } reg_lsr_t;

    /* In:  Modem Status Register */
    typedef struct packed {
        logic [7:7] dcd;  /* Data Carrier Detect */
        logic [6:6] ri;   /* Ring Indicator */
        logic [5:5] dsr;  /* Data Set Ready */
        logic [4:4] cts;  /* Clear to Send */
        logic [3:3] ddcd; /* Delta DCD */
        logic [2:2] teri; /* Trailing edge ring indicator */
        logic [1:1] ddsr; /* Delta DSR */
        logic [0:0] dcts; /* Delta CTS */
     } reg_msr_t;

    reg_lcr_t lcr;
    logic[8-1:0] dlm;
    logic[8-1:0] dll;
    logic[8-1:0] mcr;
    reg_lsr_t lsr;
    logic[8-1:0] ier;
    reg_msr_t msr;
    logic[8-1:0] scr;
    logic[8-1:0] iir;
    reg_fcr_t fcr;

    // File descriptor for logging
    integer uart_tx_fd;
    // TODO uart_rx_fd

    `ifndef SYNTHESIS
    // Function to send char to file
    initial begin
        uart_tx_fd = $fopen("uart_output.log", "w");
        if (uart_tx_fd == 0) begin
            $fatal("Failed to open uart_output.log");
        end
    end

    function void uart_send_char(input logic[8-1:0] ch);
        $fwrite(uart_tx_fd, "%c", ch);
    endfunction
    `endif

    always_ff @(posedge clk) begin
        if (!rstn) begin
            lcr <= '0;
            dlm <= '0;
            dll <= 8'h0C;
            mcr <= 8'h08;
            lsr <= '{ temt: '1, thre : '1, default: '0 };
            ier <= '0;
            msr <= '{ dcd: '1, dsr: '1, cts: '1, default: '0 };
            scr <= '0;
            fcr <= '0;
            iir <= '0;
        end else begin
            if(wvalid) begin
                case (waddr)
                    THR /*, DLL*/: begin
                        if (lcr.dlab) begin
                            dll <= wdata;
                        end else begin
                            `ifndef SYNTHESIS
                            uart_send_char(wdata);
                            `endif
                        end
                    end
                    IER /*, DLM*/: begin
                        if (lcr.dlab)  begin
                            dlm <= wdata;
                        end else begin
                            ier <= wdata;
                        end
                    end
                    FCR: fcr <= wdata;
                    LCR: lcr <= wdata;
                    MCR: mcr <= wdata;
                    SCR: scr <= wdata;
                    LSR:; /* Factory test */
                    MSR:; /* Not used */    
                    default: 
                    `ifndef SYNTHESIS
                        $error("Unhandled REG %x", waddr)
                    `endif
                    ;
                endcase
            end
            if(rvalid) begin
                case (raddr)
                    RBR: rdata <= '0; // TODO uart_read_char
                    IER: rdata <= ier;
                    LSR: rdata <= lsr;
                    MSR: rdata <= msr;
                    SCR: rdata <= scr;
                    default:
                    `ifndef SYNTHESIS
                        $error("Unhandled REG %x", raddr)
                    `endif
                    ;
                endcase
            end
        end
    end

endmodule

