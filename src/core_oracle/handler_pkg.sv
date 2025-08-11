package handler_pkg;

    // ref to share by pointer

    
    // Decode event
    import "DPI-C" context function 
    void dpi_instr_decode(
        input int id,
        input longint unsigned pc,
        input int unsigned inst
    );

    import "DPI-C" context function
    void dpi_instr_renamed(
        input int id,
        input longint unsigned pc,
        input int prs1,
        input int prs1_renammed,
        input int prs2,
        input int prs2_renammed,
        input int prd
    );

    // Issue event
    import "DPI-C" context function void dpi_instr_issue(
        input int id,
        input longint unsigned pc,
        input longint unsigned rs1val,
        input longint unsigned rs2val
    );

    // Write-Back event
    import "DPI-C" context function void dpi_instr_writeback(
        input int id,
        input longint unsigned pc,
        input longint unsigned rdval
    );

    // Commit event
    import "DPI-C" context function void dpi_instr_commit(
        input int id,
        input longint unsigned pc
    );

endpackage
