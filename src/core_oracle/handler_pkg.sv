package handler_pkg;

    // Decode event
    import "DPI-C" context function void dpi_instr_decode(
        input int id,
        input longint unsigned pc,
        input int unsigned inst
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
