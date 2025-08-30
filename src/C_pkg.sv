/* Config file */

package C;

    // I spent too mush time debugging gem5 traces :D
    // Sources (bitmask)
    localparam int LOG_IF      = 1 << 1;
    localparam int LOG_DEC     = 1 << 2;
    localparam int LOG_REN     = 1 << 3;
    localparam int LOG_IEW     = 1 << 4;
    localparam int LOG_LSU     = 1 << 5;
    localparam int LOG_EX      = 1 << 6;
    localparam int LOG_COMMIT  = 1 << 7;
    localparam int LOG_PIPE    = 1 << 8;
    

    localparam int LOG_MEM     = 1 << 20;
    localparam int LOG_UART    = 1 << 21;

    // Runtime-configurable log settings
    int log_mask = 0; // disable all by default

    function bit contains(string haystack, string needle);
        for (int i = 0; i <= haystack.len() - needle.len(); i++) begin
            if (haystack.substr(i, i + needle.len() - 1) == needle) begin
                return 1;
            end
        end
        return 0;
    endfunction

    // Init task: parse +args
    task automatic log_init();
        string mask;
        if ($value$plusargs("debug-flags=%s", mask)) begin
            log_mask = 0;
            if (contains(mask, "-IF") ) log_mask |= LOG_IF;
            if (contains(mask, "-DEC")) log_mask |= LOG_DEC;
            if (contains(mask, "-REN")) log_mask |= LOG_REN;
            if (contains(mask, "-IEW")) log_mask |= LOG_IEW;
            if (contains(mask, "-LSU")) log_mask |= LOG_LSU;
            if (contains(mask, "-EX") ) log_mask |= LOG_EX;
            if (contains(mask, "-COMMIT")) log_mask |= LOG_COMMIT;
            // Counpound flags
            if (contains(mask, "-CORE")) 
                log_mask |= LOG_IF
                        | LOG_DEC | LOG_REN
                        | LOG_IEW
                        | LOG_LSU
                        | LOG_EX
                        | LOG_COMMIT | LOG_PIPE;
            if (contains(mask, "-MEM")) log_mask |= LOG_MEM;
            if (contains(mask, "-UART")) log_mask |= LOG_UART;
            if (contains(mask, "-SYS")) 
                log_mask |= LOG_MEM
                        | LOG_UART
                        | LOG_PIPE;
            // if (contains(mask, "-ALL")) log_mask = -1; // All one
        end
        $display("Selected flags: %b", log_mask);
    endtask

    `define _LOG_BASE(src, str) \
        if ((log_mask & LOG_``src) != 0) \
            $display(str)

    // Some fun
    `define DELIM
    `define LOG(src, p0, p1=ELIM, p2=ELIM, p3=ELIM, p4=ELIM, p5=ELIM,
                p6=ELIM, p7=ELIM, p8=ELIM, p9=ELIM, p10=ELIM) \
    `ifdef D``p1 \
    `_LOG_BASE(src, $sformatf(p0)); \
    `else \
    `ifdef D``p2 \
    `_LOG_BASE(src, $sformatf(p0, p1)); \
    `else \
    `ifdef D``p3 \
    `_LOG_BASE(src, $sformatf(p0, p1, p2)); \
    `else \
    `ifdef D``p4 \
    `_LOG_BASE(src, $sformatf(p0, p1, p2, p3)); \
    `else \
    `ifdef D``p5 \
    `_LOG_BASE(src, $sformatf(p0, p1, p2, p3, p4)); \
    `else \
    `ifdef D``p6 \
    `_LOG_BASE(src, $sformatf(p0, p1, p2, p3, p4, p5)); \
    `else \
    `ifdef D``p7 \
    `_LOG_BASE(src, $sformatf(p0, p1, p2, p3, p4, p5, p6)); \
    `else \
    `ifdef D``p8 \
    `_LOG_BASE(src, $sformatf(p0, p1, p2, p3, p4, p5, p6, p7)); \
    `else \
    `ifdef D``p9 \
    `_LOG_BASE(src, $sformatf(p0, p1, p2, p3, p4, p5, p6, p7, p8)); \
    `else \
    `ifdef D``p10 \
    `_LOG_BASE(src, $sformatf(p0, p1, p2, p3, p4, p5, p6, p7, p8, p9)); \
    `else \
    `_LOG_BASE(src, $sformatf(p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10)); \
    `endif \
    `endif \
    `endif \
    `endif \
    `endif \
    `endif \
    `endif \
    `endif \
    `endif \
    `endif
  
    // Usage exemple
    // initial begin
    //     log_init();
    //     `LOG(COMMIT, "Hello from logger %s", 42);
    //     `LOG(COMMIT, 42);
    //     `LOG(COMMIT, "Hello from logger without args");
    // end

    parameter int XLEN = 64;
    // Register related
    parameter int AREG_ID_BITS = 5; // RISC-V constant
    parameter int PREG_ID_BITS = 4; // User defined
    parameter int PRFSIZE = 1 << PREG_ID_BITS;
    parameter int ARFSIZE = 1 << AREG_ID_BITS;
    // Pipe width
    parameter int NR_ISSUE_PORTS = 1;
    parameter int NR_WB_PORTS = 5;
    parameter int NR_COMPL_PORTS = NR_WB_PORTS + 2; // Completion ports
    parameter int NR_COMMIT_PORTS = 1;
    parameter int NR_ISSUE_PRF_READ_PORTS = NR_ISSUE_PORTS * 2; // TODO FMA
    // Number of inflight instructions related
    parameter int ID_BITS = 20; // TDB accordingly with max inflights
    // TODO adjust to max inflights ?
    parameter int NR_SQ_ENTRIES = 16;
    parameter int NR_ROB_ENTRIES = 32;
    parameter int NR_BQ_ENTRIES = 16; // Branch Queue entries

    /* Memory subsystem */
    parameter int CACHELINE_SIZE = 8; // TODO 32;
    parameter int NR_WB_PER_MSHR = 4;
    parameter int NR_MSHR_ENTRIES = 16;

    /* Primitives types */
    typedef logic [ID_BITS-1:0]                id_t;
    typedef logic [XLEN-1:0]                   xlen_t;
    typedef xlen_t                             pc_t;
    typedef logic [AREG_ID_BITS-1:0]           areg_id_t;
    typedef logic [PREG_ID_BITS-1:0]           preg_id_t;
    typedef logic [$clog2(NR_SQ_ENTRIES)-1:0]  sq_id_t;
    typedef logic [$clog2(NR_ROB_ENTRIES)-1:0] rob_id_t;
    typedef logic [$clog2(NR_BQ_ENTRIES)-1:0]  bq_id_t;

    typedef enum { SIZE_D, SIZE_W, SIZE_H, SIZE_B } inst_size_t;
    // We use an intermediate representation so as not to
    // manipulate the RISC-V ISA directly.
    // Each functional unit is associated with a set of operations.

    // TODO use a width + sign bit in decoded instruction 
    // to avoid variant encoded in fu op set

    parameter NB_BITS_FU_OP = 5;
    typedef enum logic [NB_BITS_FU_OP-1:0] {
        MRET, SRET, DRET,
        ECALL, EBREAK,
        WFI,
        FENCE, FENCE_I, FENCE_VMA,
        CSR_WRITE, CSR_READ, CSR_SET, CSR_CLEAR
    } none_set_t;

    typedef enum logic [NB_BITS_FU_OP-1:0] {
        L, S, LU,
        AMO_LR, AMO_SC, AMO_SWAP,
        AMO_ADD, AMO_AND, AMO_OR, AMO_XOR,
        AMO_MAX, AMO_MAXU, AMO_MIN, AMO_MINU
    } lsu_set_t;

    typedef enum logic [NB_BITS_FU_OP-1:0] {
        ADD, SUB, XOR, OR, AND, 
        SRA, SRL, SLL,
        LUI, AUIPC,
        SLT, SLTU
    } alu_set_t;

    typedef enum logic [NB_BITS_FU_OP-1:0] {
        JAL,
        JALR,
        BLT, BLTU, BGE, BGEU, BEQ, BNE
    } ctrl_set_t;

    // Use MULW here to simplify multiplier
    typedef enum logic [NB_BITS_FU_OP-1:0] {
        MUL, MULH, MULHU, MULHSU, MULW
    } mul_set_t;

    typedef enum logic [NB_BITS_FU_OP-1:0] {
        DIV, DIVU, REM, REMU
    } div_set_t;

    typedef enum logic [NB_BITS_FU_OP-1:0] { 
        FADD, FSUB, FMUL, FDIV, FMIN_MAX, FSQRT, FMADD, FMSUB, FNMSUB, FNMADD,
        FCVT_F2I, FCVT_I2F, FCVT_F2F, FSGNJ, FMV_F2X, FMV_X2F,
        FCMP, FCLASS
    } fpu_set_t;

    typedef union packed {
        none_set_t none;
        lsu_set_t lsu;
        alu_set_t alu; 
        ctrl_set_t ctrl;
        mul_set_t mul;
        div_set_t div;
        fpu_set_t fpu;
    } fu_set_t;

    // All the functional units
    parameter int NB_FU = 8;

    typedef enum [$clog2(NB_FU)-1:0]{
        FU_NONE, FU_LSU, FU_ALU, FU_CTRL, 
        FU_MUL,  FU_DIV, FU_CSR, FU_FPU
    } fu_t;

    localparam string dump_fu_arr [NB_FU] = '{
        "FU_NONE", "FU_LSU", "FU_ALU",  "FU_CTRL",
        "FU_MUL", "FU_DIV", "FU_CSR",  "FU_FPU"
    };

    // Create bit vectors typedef to avoid unpacked bit array
    typedef logic[NB_FU-1:0] fu_bitvector_t;
    typedef logic[NR_WB_PORTS-1:0] wb_bitvector_t;

    // TODO create fmt for Ecall and Fence ? 

    typedef enum logic [4-1:0] {
        TYPE_R,
        TYPE_I,
        TYPE_S,
        TYPE_B,
        TYPE_U,
        TYPE_J, 
        TYPE_SHAMT,
        TYPE_I_AND_UIMM,
        TYPE_R_FOR_CSR
    } inst_fmt_t;

   typedef struct packed {
        fu_t fu;
        fu_set_t op;
        inst_size_t size;
        inst_fmt_t fmt;
    } fuop_t;

    /* No instruction */
    // parameter fuop_t I_NOP       = {FU_NONE, NOP, SIZE_D, TYPE_R};

    /* Chapter 25. RISC-V Privileged Instruction Set Listings */
    /* Trap-Return Instructions */    
    parameter fuop_t I_SRET       = {FU_NONE, SRET, SIZE_D,      TYPE_I};
    parameter fuop_t I_MRET       = {FU_NONE, MRET, SIZE_D,      TYPE_I};
    /* Interrupt-Management Instructions */
    parameter fuop_t I_WFI        = {FU_NONE, WFI,  SIZE_D,      TYPE_I}; // TODO
    /* Supervisor Memory-Management Instructions */
    parameter fuop_t I_SFENCE_VMA  = {FU_NONE, FENCE_VMA, SIZE_D, TYPE_R}; // TODO

    /* RV32I Base Instruction Set */
    parameter fuop_t I_LUI    = {FU_ALU,    LUI,    SIZE_D, TYPE_U};
    parameter fuop_t I_AUIPC  = {FU_ALU,    AUIPC,  SIZE_D, TYPE_U};
    parameter fuop_t I_JAL    = {FU_CTRL,   JAL,    SIZE_D, TYPE_J};
    parameter fuop_t I_JALR   = {FU_CTRL,   JALR,   SIZE_D, TYPE_I};
    parameter fuop_t I_BLT    = {FU_CTRL,   BLT,    SIZE_D, TYPE_B};
    parameter fuop_t I_BLTU   = {FU_CTRL,   BLTU,   SIZE_D, TYPE_B};
    parameter fuop_t I_BGE    = {FU_CTRL,   BGE,    SIZE_D, TYPE_B};
    parameter fuop_t I_BGEU   = {FU_CTRL,   BGEU,   SIZE_D, TYPE_B};
    parameter fuop_t I_BEQ    = {FU_CTRL,   BEQ,    SIZE_D, TYPE_B};
    parameter fuop_t I_BNE    = {FU_CTRL,   BNE,    SIZE_D, TYPE_B};
    parameter fuop_t I_LB     = {FU_LSU,    L,      SIZE_B, TYPE_I};
    parameter fuop_t I_LH     = {FU_LSU,    L,      SIZE_H, TYPE_I};
    parameter fuop_t I_LW     = {FU_LSU,    L,      SIZE_W, TYPE_I};
    parameter fuop_t I_LBU    = {FU_LSU,    LU,     SIZE_B, TYPE_I};
    parameter fuop_t I_LHU    = {FU_LSU,    LU,     SIZE_H, TYPE_I};
    parameter fuop_t I_SB     = {FU_LSU,    S,      SIZE_B, TYPE_S};
    parameter fuop_t I_SH     = {FU_LSU,    S,      SIZE_H, TYPE_S};
    parameter fuop_t I_SW     = {FU_LSU,    S,      SIZE_W, TYPE_S};
    parameter fuop_t I_ADDI   = {FU_ALU,    ADD,    SIZE_D, TYPE_I};
    parameter fuop_t I_SLTI   = {FU_ALU,    SLT,    SIZE_D, TYPE_I};
    parameter fuop_t I_SLTIU  = {FU_ALU,    SLT,    SIZE_D, TYPE_I};
    parameter fuop_t I_XORI   = {FU_ALU,    XOR,    SIZE_D, TYPE_I};
    parameter fuop_t I_ORI    = {FU_ALU,    OR,     SIZE_D, TYPE_I};
    parameter fuop_t I_ANDI   = {FU_ALU,    AND,    SIZE_D, TYPE_I};
    parameter fuop_t I_ADD    = {FU_ALU,    ADD,    SIZE_D, TYPE_R};
    parameter fuop_t I_SUB    = {FU_ALU,    SUB,    SIZE_D, TYPE_R};
    parameter fuop_t I_SLL    = {FU_ALU,    SLL,    SIZE_D, TYPE_R};
    parameter fuop_t I_SLT    = {FU_ALU,    SLT,    SIZE_D, TYPE_R};
    parameter fuop_t I_SLTU   = {FU_ALU,    SLT,    SIZE_D, TYPE_R};
    parameter fuop_t I_XOR    = {FU_ALU,    XOR,    SIZE_D, TYPE_R};
    parameter fuop_t I_SRL    = {FU_ALU,    SRL,    SIZE_D, TYPE_R};
    parameter fuop_t I_SRA    = {FU_ALU,    SRA,    SIZE_D, TYPE_R};
    parameter fuop_t I_OR     = {FU_ALU,    OR,     SIZE_D, TYPE_R};
    parameter fuop_t I_AND    = {FU_ALU,    AND,    SIZE_D, TYPE_R};
    parameter fuop_t I_FENCE  = {FU_NONE,   FENCE,  SIZE_D, TYPE_R};
    parameter fuop_t I_ECALL  = {FU_NONE,   ECALL,  SIZE_D, TYPE_R};
    parameter fuop_t I_EBREAK = {FU_NONE,   ECALL,  SIZE_D, TYPE_R};

    /* RV64I Base Instruction Set (in addition to RV32I) */
    parameter fuop_t I_LWU    = {FU_LSU,    LU,     SIZE_W, TYPE_I};
    parameter fuop_t I_LD     = {FU_LSU,    L,      SIZE_D, TYPE_I};
    parameter fuop_t I_SD     = {FU_LSU,    S,      SIZE_D, TYPE_S};
    parameter fuop_t I_SLLI   = {FU_ALU,    SLL,    SIZE_D, TYPE_SHAMT};
    parameter fuop_t I_SRLI   = {FU_ALU,    SRL,    SIZE_D, TYPE_SHAMT};
    parameter fuop_t I_SRAI   = {FU_ALU,    SRA,    SIZE_D, TYPE_SHAMT};
    parameter fuop_t I_ADDIW  = {FU_ALU,    ADD,    SIZE_W, TYPE_I};
    parameter fuop_t I_SLLIW  = {FU_ALU,    SLL,    SIZE_W, TYPE_SHAMT};
    parameter fuop_t I_SRLIW  = {FU_ALU,    SRL,    SIZE_W, TYPE_SHAMT};
    parameter fuop_t I_SRAIW  = {FU_ALU,    SRA,    SIZE_W, TYPE_SHAMT};
    parameter fuop_t I_ADDW   = {FU_ALU,    ADD,    SIZE_W, TYPE_R};
    parameter fuop_t I_SUBW   = {FU_ALU,    SUB,    SIZE_W, TYPE_R};
    parameter fuop_t I_SLLW   = {FU_ALU,    SLL,    SIZE_W, TYPE_R};
    parameter fuop_t I_SRLW   = {FU_ALU,    SRL,    SIZE_W, TYPE_R};
    parameter fuop_t I_SRAW   = {FU_ALU,    SRA,    SIZE_W, TYPE_R};

    /* RV32/RV64 Zifencei Standard Extension */
    parameter fuop_t I_FENCE_I = {FU_NONE,   FENCE_I,  SIZE_D,  TYPE_I};

    /* RV32/RV64 Zicsr Standard Extension */
    parameter fuop_t I_CSRRW  = {FU_NONE,    CSR_WRITE,  SIZE_D, TYPE_R_FOR_CSR};
    parameter fuop_t I_CSRRS  = {FU_NONE,    CSR_SET,    SIZE_D, TYPE_R_FOR_CSR};
    parameter fuop_t I_CSRRC  = {FU_NONE,    CSR_CLEAR,  SIZE_D, TYPE_R_FOR_CSR};
    parameter fuop_t I_CSRRWI = {FU_NONE,    CSR_WRITE,  SIZE_D, TYPE_I_AND_UIMM};
    parameter fuop_t I_CSRRSI = {FU_NONE,    CSR_SET,    SIZE_D, TYPE_I_AND_UIMM};
    parameter fuop_t I_CSRRCI = {FU_NONE,    CSR_CLEAR,  SIZE_D, TYPE_I_AND_UIMM};

    /* RV32/RV64 M Standard Extension */
    parameter fuop_t I_MUL    = {FU_MUL,     MUL,     SIZE_D, TYPE_R};
    parameter fuop_t I_MULH   = {FU_MUL,     MULH,    SIZE_D, TYPE_R};
    parameter fuop_t I_MULHSU = {FU_MUL,     MULHSU,  SIZE_D, TYPE_R};
    parameter fuop_t I_MULHU  = {FU_MUL,     MULHU,   SIZE_D, TYPE_R};
    parameter fuop_t I_DIV    = {FU_DIV,     DIV,     SIZE_D, TYPE_R};
    parameter fuop_t I_DIVU   = {FU_DIV,     DIVU,    SIZE_D, TYPE_R};
    parameter fuop_t I_REM    = {FU_DIV,     REM,     SIZE_D, TYPE_R};
    parameter fuop_t I_REMU   = {FU_DIV,     REMU,    SIZE_D, TYPE_R};
    parameter fuop_t I_MULW   = {FU_MUL,     MULW,    SIZE_D, TYPE_R};
    parameter fuop_t I_DIVW   = {FU_DIV,     DIV,     SIZE_W, TYPE_R};
    parameter fuop_t I_DIVUW  = {FU_DIV,     DIVU,    SIZE_W, TYPE_R};  
    parameter fuop_t I_REMW   = {FU_DIV,     REM,     SIZE_W, TYPE_R};
    parameter fuop_t I_REMUW  = {FU_DIV,     REMU,    SIZE_W, TYPE_R};

    /* RV32A Standard Extension */
    parameter fuop_t I_LR_W       = {FU_LSU, AMO_LR,   SIZE_W, TYPE_R};
    parameter fuop_t I_SC_W       = {FU_LSU, AMO_SC,   SIZE_W, TYPE_R};
    parameter fuop_t I_AMOSWAP_W  = {FU_LSU, AMO_SWAP, SIZE_W, TYPE_R};
    parameter fuop_t I_AMOADD_W   = {FU_LSU, AMO_ADD,  SIZE_W, TYPE_R};
    parameter fuop_t I_AMOAND_W   = {FU_LSU, AMO_AND,  SIZE_W, TYPE_R};
    parameter fuop_t I_AMOOR_W    = {FU_LSU, AMO_OR,   SIZE_W, TYPE_R};
    parameter fuop_t I_AMOXOR_W   = {FU_LSU, AMO_XOR,  SIZE_W, TYPE_R};
    parameter fuop_t I_AMOMAX_W   = {FU_LSU, AMO_MAX,  SIZE_W, TYPE_R};
    parameter fuop_t I_AMOMAXU_W  = {FU_LSU, AMO_MAXU, SIZE_W, TYPE_R};
    parameter fuop_t I_AMOMIN_W   = {FU_LSU, AMO_MIN,  SIZE_W, TYPE_R};
    parameter fuop_t I_AMOMINU_W  = {FU_LSU, AMO_MINU, SIZE_W, TYPE_R};

    /* RV64A Standard Extension (in addition to RV32A) */
    parameter fuop_t I_LR_D       = {FU_LSU, AMO_LR,   SIZE_D, TYPE_R};
    parameter fuop_t I_SC_D       = {FU_LSU, AMO_SC,   SIZE_D, TYPE_R};
    parameter fuop_t I_AMOSWAP_D  = {FU_LSU, AMO_SWAP, SIZE_D, TYPE_R};
    parameter fuop_t I_AMOADD_D   = {FU_LSU, AMO_ADD,  SIZE_D, TYPE_R};
    parameter fuop_t I_AMOXOR_D   = {FU_LSU, AMO_XOR,  SIZE_D, TYPE_R};
    parameter fuop_t I_AMOAND_D   = {FU_LSU, AMO_AND,  SIZE_D, TYPE_R};
    parameter fuop_t I_AMOOR_D    = {FU_LSU, AMO_OR,   SIZE_D, TYPE_R};
    parameter fuop_t I_AMOMIN_D   = {FU_LSU, AMO_MIN,  SIZE_D, TYPE_R};
    parameter fuop_t I_AMOMAX_D   = {FU_LSU, AMO_MAX,  SIZE_D, TYPE_R};
    parameter fuop_t I_AMOMINU_D  = {FU_LSU, AMO_MINU, SIZE_D, TYPE_R};
    parameter fuop_t I_AMOMAXU_D  = {FU_LSU, AMO_MAXU, SIZE_D, TYPE_R};

    /* RV32F Standard Extension */
    // parameter fuop_t FLD = {FU_LSU, FLD};
    // parameter fuop_t FLW = {FU_LSU, FLW};
    // parameter fuop_t FLH = {FU_LSU, FLH};
    // parameter fuop_t FLB = {FU_LSU, FLB};
    // parameter fuop_t FSD = {FU_LSU, FSD};
    // parameter fuop_t FSW = {FU_LSU, FSW};
    // parameter fuop_t FSH = {FU_LSU, FSH};
    // parameter fuop_t FSB = {FU_LSU, FSB};

    // Branch prediction
    typedef struct packed {
        xlen_t pcnext;
        logic taken;
    } bp_t;

    typedef struct {
        logic [XLEN-1:0] pc;    // PC of the instruction
        logic [32-1:0]   data;  // Assembly code
        bp_t             bp;    // Branch prediction
    } fetch_data_t;

    // unpacked to allow easy DPI
    typedef struct packed {
        logic [XLEN-1:0] pc;    // PC of the instruction
        logic [32-1:0]   tinst; // Assembly code
        fu_t             fu;    // functional unit to use
        fu_set_t         op;    // operation to perform
        areg_id_t        rs1;   // register source idx
        logic            rs1_valid;
        areg_id_t        rs2;   // register source idx
        logic            rs2_valid;
        areg_id_t        rd;    // register destination idx
        logic            rd_valid;
        logic [XLEN-1:0] imm;   // imm value
        logic            use_uimm; // Use rs1 as uimm value
        inst_size_t      size;  // DW, W, H, B
        logic            valid; // Not UNIMP
    } si_t; // StaticInst

    typedef struct packed {
        si_t si;
        logic[ID_BITS-1:0] id;
        logic fault;
        logic valid;  // is the result valid
        preg_id_t prs1;
        logic prs1_renammed;
        preg_id_t prs2;
        logic prs2_renammed;
        preg_id_t prd; // Always renammed 
        bq_id_t            bqid; // Branch Queue ID used by branchs
        logic            is_uop; // is micro operation
        logic            is_uop_last;
    } di_t; // DynamicInst

    /* Packed everything to make verilator happy */
    typedef struct packed {
        logic [XLEN-1:0]   pc;    // PC of the instruction
        logic[ID_BITS-1:0] id;    // Used to track ordering
        preg_id_t          prd;   // Where to wb inst
        logic[XLEN-1:0]    rs1val;
        logic[XLEN-1:0]    rs2val;
        logic[XLEN-1:0]    imm;
        fu_t               fu;    // functional unit to use
        fu_set_t           op;    // operation to perform
        inst_size_t        size;
        bq_id_t            bqid; // Branch Queue ID used by branchs
    } fu_input_t;

    // Write back port FU -> WB
    typedef struct packed {
        logic [XLEN-1:0]   pc;    // PC of the instruction (Debug only ?)
        logic[ID_BITS-1:0] id;    // Wakeup rob
        preg_id_t          prd;   // Where to wb inst
        logic[XLEN-1:0]    rdval;  // Final result
    } fu_output_t;

    // Completion port FU -> ROB
    typedef struct packed {
        id_t     id; // id_t or rob_id_t ? DO wee need to compare order ?
        logic    valid; // Insert the valid here to simplify intf
    } completion_port_t;

    typedef struct packed {
        id_t id; // Debug only ?
        pc_t pc; // Debug only ?
        preg_id_t prd; // To read PRF
        areg_id_t ard; // To write ARF
        logic needprf2arf;
        logic needSQfree;
        // logic needBQfree;
        // logic needCSRfree;
        fu_t fu; // used to trigger the valid fu on commit
        logic completed; // WB performed or completion
        logic is_uop_final; // Inst or last uop
    } rob_entry_t;


    typedef struct packed {
        id_t id;            // Debug only ?
        xlen_t pc;          // Debug only ?
        xlen_t paddr;       // the paddr

        // Naive:
        // inst_size_t size;   // DW, W, H or Byte
        // xlen_t data;
        // Formatted (to help STLF)
        logic [8-1:0] fmask;
        xlen_t        fdata;

        logic valid;        // Entry used
        logic commited;     // Entry used
        logic completed;
    } sq_entry_t;

    function automatic string dump_sq_entry (
        input sq_entry_t sqe
    );
        return $sformatf("PC: %x (sn=%x) P@:%x fmask:%x fdata:%x [commited:%d]",
                         sqe.pc, sqe.id, sqe.paddr, sqe.fmask, sqe.fdata,
                         sqe.commited);
    endfunction



    /* address ranges and attributes */
    parameter int MEM_ADDR_WIDTH = 20;
    parameter xlen_t RANGES_MEM_SIZE = 1 << MEM_ADDR_WIDTH;
    parameter xlen_t RANGES_MEM_BASE = 64'h8000_0000;
    parameter xlen_t RANGES_MEM_END = RANGES_MEM_BASE + RANGES_MEM_SIZE;

    parameter int    UART_ADDR_WIDTH = 5;
    parameter xlen_t RANGES_UART_BASE = 64'h1000_0000;
    parameter xlen_t RANGES_UART_SIZE = 1 << UART_ADDR_WIDTH;
    parameter xlen_t RANGES_UART_END = RANGES_UART_BASE + RANGES_UART_SIZE;


    function automatic logic is_inrange(
        xlen_t base, xlen_t size, xlen_t addr
    );
        return (addr >= base) && addr < (base + size);
    endfunction

    function automatic logic is_bufferable(xlen_t addr);
        return is_inrange(RANGES_MEM_BASE, RANGES_MEM_SIZE, addr);
    endfunction
    

    /********** A LOT OF DISLAYER *************/

    // Integer register names (RV64)
    localparam string IntRegNames [0:31] = '{
        "zero", "ra",   "sp",  "gp",
        "tp",   "t0",   "t1",  "t2",
        "s0",   "s1",   "a0",  "a1",
        "a2",   "a3",   "a4",  "a5",
        "a6",   "a7",   "s2",  "s3",
        "s4",   "s5",   "s6",  "s7",
        "s8",   "s9",   "s10", "s11",
        "t3",   "t4",   "t5",  "t6"
    };

    // Floating-point register names (RV64F/D)
    localparam string FloatRegNames [0:31] = '{
        "ft0", "ft1", "ft2",  "ft3",
        "ft4", "ft5", "ft6",  "ft7",
        "fs0", "fs1", "fa0",  "fa1",
        "fa2", "fa3", "fa4",  "fa5",
        "fa6", "fa7", "fs2",  "fs3",
        "fs4", "fs5", "fs6",  "fs7",
        "fs8", "fs9", "fs10", "fs11",
        "ft8", "ft9", "ft10", "ft11"
    };

    function automatic string dumpAReg (input areg_id_t areg);
        return IntRegNames[areg];
    endfunction

    function automatic string dumpPReg (
        input preg_id_t   preg,    // physical register id
        input bit         renamed  // 1 = show renamed mapping
    );
        string s;
        if (renamed) begin
            int color;
            color = ((int'(preg) + 17) * 97) % 256;
            // Build up the string
            s = $sformatf("\033[38;5;%0dm", color);
            s = { s, $sformatf(":%%%x", preg) };
            s = { s, "\033[0m" };
        end else begin
            s = "AR";
        end
        return s;
    endfunction 

    function automatic string dumpAPReg (
        input areg_id_t   areg,
        input preg_id_t   preg,    // physical register id
        input bit         renamed  // 1 = show renamed mapping
    );
        return $sformatf("%s:%s",
                          dumpAReg(areg), 
                          dumpPReg(preg, renamed));

    endfunction

    /* Utils */
    function automatic logic [64-1:0] sext32to64(logic [32-1:0] x);
        return {{32{x[31]}}, x};
    endfunction

    function automatic logic [64-1:0] zext32to64(logic [32-1:0] x);
        return {{32'b0}, x};
    endfunction

    function automatic logic [64-1:0] ext32to64(logic [32-1:0] x, logic s);
        if(s) begin
            return sext32to64(x);
        end else begin
            return zext32to64(x);
        end
    endfunction

endpackage

interface csr_if #();
    logic          rvalid;
    RV::csr_addr_t raddr; // Read port
    xlen_t         rdata;
    logic          wvalid;
    RV::csr_addr_t waddr; // Write port
    xlen_t         wdata;
    modport master (
        output rvalid,
        output raddr,
        input  rdata,
        output waddr,
        output wdata,
        output wvalid
    );
    modport slave (
        input  rvalid,
        input  raddr,
        output rdata,
        input  waddr,
        input  wdata,
        input  wvalid
    );
endinterface : csr_if

interface bq_push_if #();
    pc_t pc; // debug only ?
    id_t id; // debug only
    bp_t  bp;   // single prediction
    // Use intf to easyly extends this class (Ras state ...)
    logic valid;
    logic ready;
    bq_id_t bqid; // Index to write back branch OoO

    modport master (
        output pc,
        output id,
        output bp,
        output valid,
        input ready, bqid
    );
    modport slave (
        input pc, id,
        input bp,
        input valid,
        output ready, bqid
    );
endinterface


interface bq_pop_if #();
    bp_t bp;
    logic missprediction;
    logic pop;
    modport bq (
        output bp, missprediction,
        input  pop
    );
    modport commit (
        input  bp, missprediction,
        output pop
    );
endinterface

interface squash_if #();
    logic valid; // Do squash 
    id_t  id; // The ID from where to squash (Needed for flush at execute)
    pc_t resolved_pc;    // Resolved pc 
    modport master (
        output valid, id, resolved_pc
    );
    modport slave (
        input  valid, id, resolved_pc
    );
endinterface


interface dcache_ports_if #();
    
    // Load Address channel
    xlen_t      load_a_addr;
    logic       load_a_valid;
    logic       load_a_ready;
    // Load Data channel
    xlen_t      load_d_data;
    logic       load_d_valid;

    xlen_t      waddr;
    // inst_size_t wsize;
    xlen_t      wdata;
    logic [8-1:0] wmask;
    logic       wvalid;
    logic       wready;

    modport master (
        output load_a_addr,
        output load_a_valid,
        input  load_a_ready,
        input  load_d_data,
        input  load_d_valid,

        output waddr,
        // output wsize,
        output wdata,
        output wmask,
        output wvalid,
        input  wready
    );
    modport slave (
        input  load_a_addr,
        input  load_a_valid,
        output load_a_ready,
        output load_d_data,
        output load_d_valid,

        input  waddr,
        // input  wsize,
        input  wdata,
        input  wmask,
        input  wvalid,
        output wready
    );
endinterface : dcache_ports_if

