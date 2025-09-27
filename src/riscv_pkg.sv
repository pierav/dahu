/* RISC-V isa description */

package RV;
    localparam RVXLEN = 64;
    typedef logic [RVXLEN-1:0] xlen_t;

    /*** Instructions ***/

    // Chapter 35. RV32/64G Instruction Set Listings
    typedef struct packed {
        logic [31:25] funct7;
        logic [24:20] rs2;
        logic [19:15] rs1;
        logic [14:12] funct3;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } rtype_t;

    typedef struct packed {
        logic [31:20] imm11_0;
        logic [19:15] rs1;
        logic [14:12] funct3;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } itype_t;

    typedef struct packed {
        logic [31:25] imm11_5;
        logic [24:20] rs2;
        logic [19:15] rs1;
        logic [14:12] funct3;
        logic [11:7]  imm4_0;
        logic [6:0]   opcode;
    } stype_t;

    typedef struct packed {
        logic [31:12] imm31_12;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } utype_t;

    typedef struct packed {
        logic         imm20;
        logic [30:21] imm10_1;
        logic         imm11;
        logic [19:12] imm19_12;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } jtype_t;

    typedef struct packed {
        logic [31:27] funct5;
        logic         aq;
        logic         rl;
        logic [24:20] rs2;
        logic [19:15] rs1;
        logic [14:12] funct3;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } atype_t;

    typedef union packed {
        logic [31:0]   instr;
        rtype_t        rtype;
        itype_t        itype;
        stype_t        stype;
        utype_t        utype;
        jtype_t        jtype;
        atype_t        atype;
    } instruction_t;

    // 2.2. CSR Listing
    typedef enum logic [11:0] {
        // Table 4. Currently allocated RISC-V unprivileged CSR addresses.
        // Unprivileged Floating-Point CSRs
        CSR_FFLAGS          = 12'h001, // Floating-Point Accrued Exceptions.
        CSR_FRM             = 12'h002, // Floating-Point Dynamic Rounding Mode.
        CSR_FCSR            = 12'h003, // Floating-Point Control and Status Register (frm +fflags).
        // Unprivileged Vector CSRs
        CSR_VSTART          = 12'h008, // Vector start position.
        CSR_VXSAT           = 12'h009, // Fixed-point accrued saturation flag.
        CSR_VXRM            = 12'h00A, // Fixed-point rounding mode.
        CSR_VCSR            = 12'h00F, // Vector control and status register.
        CSR_VL              = 12'hC20, // Vector length.
        CSR_VTYPE           = 12'hC21, // Vector data type register.
        CSR_VLENB           = 12'hC22, // Vector register length in bytes.
        // Unprivileged Zicfiss extension CSR
        // Unprivileged Entropy Source Extension CSR
        // Unprivileged Zcmt Extension CSR
        // Unprivileged Counter/Timers
        CSR_CYCLE           = 12'hC00, // Cycle counter for RDCYCLE instruction.
        CSR_TIME            = 12'hC01, // Timer for RDTIME instruction.
        CSR_INSTRET         = 12'hC02, // Instructions-retired counter for RDINSTRET instruction.
        CSR_HPMCOUNTER3     = 12'hC03, // Performance-monitoring counter.
        CSR_HPMCOUNTER4     = 12'hC04,
        CSR_HPMCOUNTER5     = 12'hC05,
        CSR_HPMCOUNTER6     = 12'hC06,
        CSR_HPMCOUNTER7     = 12'hC07,
        CSR_HPMCOUNTER8     = 12'hC08,
        CSR_HPMCOUNTER9     = 12'hC09,
        CSR_HPMCOUNTER10    = 12'hC0A,
        CSR_HPMCOUNTER11    = 12'hC0B,
        CSR_HPMCOUNTER12    = 12'hC0C,
        CSR_HPMCOUNTER13    = 12'hC0D,
        CSR_HPMCOUNTER14    = 12'hC0E,
        CSR_HPMCOUNTER15    = 12'hC0F,

        // Table 5. Currently allocated RISC-V supervisor-level CSR addresses.
        // Supervisor Trap Setup
        CSR_SSTATUS         = 12'h100, // Supervisor status register.
        CSR_SIE             = 12'h104, // Supervisor interrupt-enable register.
        CSR_STVEC           = 12'h105, // Supervisor trap handler base address.
        CSR_SCOUNTEREN      = 12'h106, // Supervisor counter enable.
        // Supervisor Configuration
        CSR_SENVCFG         = 12'h10A, // Supervisor environment configuration register.
        // Supervisor Counter Setup
        CSR_SCOUNTINHIBIT   = 12'h120, // Supervisor counter-inhibit register.
        // Supervisor Trap Handling
        CSR_SSCRATCH        = 12'h140, // Supervisor scratch register.
        CSR_SEPC            = 12'h141, // Supervisor exception program counter.
        CSR_SCAUSE          = 12'h142, // Supervisor trap cause.
        CSR_STVAL           = 12'h143, // Supervisor trap value.
        CSR_SIP             = 12'h144, // Supervisor interrupt pending.
        CSR_SCOUNTOFV       = 12'hDA0, // Supervisor count overflow.
        // Supervisor Protection and Translation
        CSR_SATP           = 12'h180, // Supervisor address translation and protection.
        // Debug/Trace Registers
        CSR_SCONTEXT        = 12'h5A8, // Supervisor-mode context register
        // Supervisor State Enable Registers

        // Table 6. Currently allocated RISC-V hypervisor and VS CSR addresses.
        // Ignore

        // Table 7. Currently allocated RISC-V machine-level CSR addresses.
        // Machine Information Registers
        CSR_MVENDORID       = 12'hF11, // Vendor ID.
        CSR_MARCHID         = 12'hF12, // Architecture ID.
        CSR_MIMPID          = 12'hF13, // Implementation ID.
        CSR_MHARTID         = 12'hF14, // Hardware thread ID.
        CSR_MCONFIGPTR      = 12'hF15, // Pointer to configuration data structure.
        // Machine Trap Setup
        CSR_MSTATUS         = 12'h300, // Machine status register.
        CSR_MISA            = 12'h301, // ISA and extensions
        CSR_MEDELEG         = 12'h302, // Machine exception delegation register.
        CSR_MIDELEG         = 12'h303, // Machine interrupt delegation register.
        CSR_MIE             = 12'h304, // Machine interrupt-enable register.
        CSR_MTVEC           = 12'h305, // Machine trap-handler base address.
        CSR_MCOUNTEREN      = 12'h306, // Machine counter enable.
        // Machine Trap Handling
        CSR_MSCRATCH        = 12'h340, // Machine scratch register.
        CSR_MEPC            = 12'h341, // Machine exception program counter.
        CSR_MCAUSE          = 12'h342, // Machine trap cause.
        CSR_MTVAL           = 12'h343, // Machine trap value.
        CSR_MIP             = 12'h344, // Machine interrupt pending.
        CSR_MTINST          = 12'h34A, // Machine trap instruction (transformed).
        CSR_MTVAL2          = 12'h34B, // Machine second trap value.
        // Machine Configuration
        CSR_MENVCFG         = 12'h30A, // Machine environment configuration register.
        CSR_MSECCFG         = 12'h747, // Machine security configuration register.
        // Machine Memory Protection
        CSR_PMPCFG0         = 12'h3A0, // Physical memory protection configuration.
        CSR_PMPCFG1         = 12'h3A1,
        CSR_PMPCFG2         = 12'h3A2,
        CSR_PMPCFG3         = 12'h3A3,
        // ...
        CSR_PMPADDR0        = 12'h3B0, // Physical memory protection address register.
        CSR_PMPADDR1        = 12'h3B1,
        CSR_PMPADDR2        = 12'h3B2,
        CSR_PMPADDR3        = 12'h3B3,
        CSR_PMPADDR4        = 12'h3B4,
        CSR_PMPADDR5        = 12'h3B5,
        CSR_PMPADDR6        = 12'h3B6,
        CSR_PMPADDR7        = 12'h3B7,
        CSR_PMPADDR8        = 12'h3B8,
        CSR_PMPADDR9        = 12'h3B9,
        CSR_PMPADDR10       = 12'h3BA,
        CSR_PMPADDR11       = 12'h3BB,
        CSR_PMPADDR12       = 12'h3BC,
        CSR_PMPADDR13       = 12'h3BD,
        CSR_PMPADDR14       = 12'h3BE,
        CSR_PMPADDR15       = 12'h3BF,
        // ...
        // Machine State Enable Registers

        // Table 8. Currently allocated RISC-V machine-level CSR addresses.
        // Machine Non-Maskable Interrupt Handling
        // Machine Counter/Timers
        CSR_MCYCLE          = 12'hB00, // Machine cycle counter.
        CSR_MINSTRET        = 12'hB02, // Machine instructions-retired counter.
        CSR_MHPMCOUNTER3    = 12'hB03, // Machine performance-monitoring counter.
        CSR_MHPMCOUNTER4    = 12'hB04,
        CSR_MHPMCOUNTER5    = 12'hB05,
        CSR_MHPMCOUNTER6    = 12'hB06,
        CSR_MHPMCOUNTER7    = 12'hB07,
        CSR_MHPMCOUNTER8    = 12'hB08,
        CSR_MHPMCOUNTER9    = 12'hB09,
        CSR_MHPMCOUNTER10   = 12'hB0A,
        CSR_MHPMCOUNTER11   = 12'hB0B,
        CSR_MHPMCOUNTER12   = 12'hB0C,
        CSR_MHPMCOUNTER13   = 12'hB0D,
        CSR_MHPMCOUNTER14   = 12'hB0E,
        CSR_MHPMCOUNTER15   = 12'hB0F,
        // ...
        // Machine Counter Setup
        CSR_MCOUNTINHIBIT   = 12'h320, // Machine counter-inhibit register.
        CSR_MHPMEVENT3      = 12'h323, // Machine performance-monitoring event selector.
        CSR_MHPMEVENT4      = 12'h324,
        CSR_MHPMEVENT5      = 12'h325,
        CSR_MHPMEVENT6      = 12'h326,
        CSR_MHPMEVENT7      = 12'h327,
        CSR_MHPMEVENT8      = 12'h328,
        CSR_MHPMEVENT9      = 12'h329,
        CSR_MHPMEVENT10     = 12'h32A,
        CSR_MHPMEVENT11     = 12'h32B,
        CSR_MHPMEVENT12     = 12'h32C,
        CSR_MHPMEVENT13     = 12'h32D,
        CSR_MHPMEVENT14     = 12'h32E,
        CSR_MHPMEVENT15     = 12'h32F,
        // Debug/Trace Registers (shared with Debug Mode)
        CSR_TSELECT         = 12'h7A0, // Debug/Trace trigger register select.
        CSR_TDATA1          = 12'h7A1, // First Debug/Trace trigger data register.
        CSR_TDATA2          = 12'h7A2, // Second Debug/Trace trigger data register.
        CSR_TDATA3          = 12'h7A3, // Third Debug/Trace trigger data register.
        CSR_TINFO           = 12'h7A4, // Machine-mode context register.
        // Debug Mode Registers
        CSR_DCSR            = 12'h7b0, // Debug control and status register.
        CSR_DPC             = 12'h7b1, // Debug program counter.
        CSR_DSCRATCH0       = 12'h7b2, // Debug scratch register 0.
        CSR_DSCRATCH1       = 12'h7b3  // Debug scratch register 1.        
    } csr_reg_t;
    
    // Value of mstatus/mstatush fields MPV and MPP after a trap into M-mode.
    typedef enum logic[1:0] {
      PRIV_LVL_M = 3,
      PRIV_LVL_S = 1,
      PRIV_LVL_U = 0
    } priv_lvl_t;
    
    // decoded CSR address
    typedef struct packed {
        logic [1:0]  rw;
        priv_lvl_t   priv_lvl;
        logic  [7:0] address;
    } csr_addr_t;

    typedef union packed {
        csr_reg_t   address;
        csr_addr_t  csr_decode;
    } csr_t;

    /*** CSR content ***/

    // Encoding of satp MODE field.
    typedef enum logic [3:0] {
       Bare = 0,  // No translation or protection.
       Sv39 = 8,  // Page-based 39-bit virtual addressing (see Section 12.4).
       Sv48 = 9,  // Page-based 48-bit virtual addressing (see Section 12.5).
       Sv57 = 10, // Page-based 57-bit virtual addressing (see Section 12.6).
       Sv64 = 11 // Reserved for page-based 64-bit virtual addressing.
    } satp_mode_t;

    // Encoding of MXL field in misa
    typedef enum logic [1:0] {
        RVXLEN_32  = 2'b01,
        RVXLEN_64  = 2'b10
    } xl_t;

    // Encoding of FS[1:0], VS[1:0], and XS[1:0] status fields
    typedef enum logic [1:0] {
        XS_OFF     = 2'b00, // All off
        XS_INITIAL = 2'b01, // None dirty or clean, some on
        XS_CLEAN   = 2'b10, // None dirty, some clean
        XS_DIRTY   = 2'b11  // Some dirty
    } xs_t;

    typedef struct packed {
        logic         sd;     // Signal Dirty
        logic [62:34] wpri6;  // Writes Preserve Reads Ignore
        xl_t          uxl;    // User RVXLEN
        logic [12:0]  wpri5;  //
        logic         mxr;    // Make eXecutable Readable
        logic         sum;    // permit Supervisor User Memory access
        logic         wpri4;  //
        xs_t          xs;     // Xproc Status
        xs_t          fs;     // Fpu Status
        logic [1:0]   wpri3;  //
        xs_t          vs;     // Vector status
        logic         spp;    // Supervisor Previous Privilege
        logic         wpri2;  //
        logic         ube;    // User Bytes Endianess
        logic         spie;   // Supervisor Prior Interrupts Enable
        logic [1:0]   wpri1;  //
        logic         sie;    // Supervisor Interrupts Enable
        logic         wpri0;  //
    } sstatus_rv_t;
    
    typedef struct packed {
        logic         sd;     // Signal Dirty
        logic [62:36] wpri4;  //
        xl_t          sxl;    // Supervisor RVXLEN
        xl_t          uxl;    // User RVXLEN
        logic [8:0]   wpri3;  //
        logic         tsr;    // Trap SRet
        logic         tw;     // Time Wait
        logic         tvm;    // Trap Virtual Memory
        logic         mxr;    // Make eXecutable Readable
        logic         sum;    // permit Supervisor User Memory access
        logic         mprv;   // Modify PRiVilege (for ld/st only)
        xs_t          xs;     // Xproc Status
        xs_t          fs;     // Fpu Status
        priv_lvl_t    mpp;    // Machine Previous Privilege
        xs_t          vs;     // vector extension register
        logic         spp;    // Supervisor Previous Privilege
        logic         mpie;   // Machine Prior Interrupts Enable
        logic         ube;    // User Bytes Endianess
        logic         spie;   // Supervisor Prior Interrupts Enable
        logic         wpri2;  //
        logic         mie;    // Machine Interrupts Enable
        logic         wpri1;  // 
        logic         sie;    // Supervisor Interrupts Enable
        logic         wpri0;  //
    } mstatus_rv_t;

    // Supervisor address translation and protection (satp) register when SRVXLEN=64,
    // for MODE values Bare, Sv39, Sv48, and Sv57.
    typedef struct packed {
        satp_mode_t    mode;
        logic [16-1:0] asid;
        logic [44-1:0] ppn;
    } satp_t;

    // Floating-Point control and status register (32-bit!)
    typedef struct packed {
        logic [31:15] reserved;  // reserved for L extension, return 0 otherwise
        logic [6:0]   fprec;     // div/sqrt precision control
        logic [2:0]   frm;       // float rounding mode
        logic [4:0]   fflags;    // float exception flags
    } fcsr_t;

    // PMP
    typedef enum logic [1:0] {
        OFF   = 2'b00,
        TOR   = 2'b01,
        NA4   = 2'b10,
        NAPOT = 2'b11
    } pmp_addr_mode_t;

    // PMP Access Type
    typedef enum logic [2:0] {
        ACCESS_NONE  = 3'b000,
        ACCESS_READ  = 3'b001,
        ACCESS_WRITE = 3'b010,
        ACCESS_EXEC  = 3'b100
    } pmp_access_t;

    typedef struct packed {
        logic           x;
        logic           w;
        logic           r;
    } pmpcfg_access_t;

    // PMP configuration register (8bit)
    typedef struct packed {
        logic           locked;
        logic [1:0]     reserved;
        pmp_addr_mode_t addr_mode;
        pmpcfg_access_t access_type;
    } pmpcfg_t;

    // Machine cause (mcause) register values after trap
    localparam logic [RVXLEN-1:0] INSTR_ADDR_MISALIGNED = 0;
    localparam logic [RVXLEN-1:0] INSTR_ACCESS_FAULT    = 1;
    localparam logic [RVXLEN-1:0] ILLEGAL_INSTR         = 2;
    localparam logic [RVXLEN-1:0] BREAKPOINT            = 3;
    localparam logic [RVXLEN-1:0] LD_ADDR_MISALIGNED    = 4;
    localparam logic [RVXLEN-1:0] LD_ACCESS_FAULT       = 5;
    localparam logic [RVXLEN-1:0] ST_ADDR_MISALIGNED    = 6;
    localparam logic [RVXLEN-1:0] ST_ACCESS_FAULT       = 7;
    localparam logic [RVXLEN-1:0] ENV_CALL_UMODE        = 8;
    localparam logic [RVXLEN-1:0] ENV_CALL_SMODE        = 9;
    localparam logic [RVXLEN-1:0] ENV_CALL_MMODE        = 11;
    localparam logic [RVXLEN-1:0] INSTR_PAGE_FAULT      = 12;
    localparam logic [RVXLEN-1:0] LOAD_PAGE_FAULT       = 13;
    localparam logic [RVXLEN-1:0] STORE_PAGE_FAULT      = 15;
    localparam logic [RVXLEN-1:0] DOUBLE_TRAP           = 16;
    localparam logic [RVXLEN-1:0] SOFTWARE_CHECK        = 18;
    localparam logic [RVXLEN-1:0] HARDWARE_ERROR        = 19;
    
    // Debug control and status register
    typedef struct packed {
        logic [31:28]     xdebugver;
        logic [27:16]     zero2;
        logic             ebreakm;
        logic             zero1;
        logic             ebreaks;
        logic             ebreaku;
        logic             stepie;
        logic             stopcount;
        logic             stoptime;
        logic [8:6]       cause;
        logic             zero0;
        logic             mprven;
        logic             nmip;
        logic             step;
        priv_lvl_t        prv;
    } dcsr_t;


endpackage
