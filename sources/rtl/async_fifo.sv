// Minimal Asynchronous FIFO - SystemVerilog Implementation
// Features:
//   - Cross-clock domain operation (separate wr_clk and rd_clk)
//   - Gray code pointers for metastability-safe operation
//   - Extra bit technique for clean empty/full flag generation
//   - 2-stage synchronizers for pointer crossing

`timescale 1ns / 1ps

module async_fifo #(
    parameter WIDTH = 8,                          // Data width in bits
    parameter DEPTH = 16,                         // FIFO depth (must be power of 2)  
    parameter ADDR_WIDTH = $clog2(DEPTH),         // Address width
    parameter PTR_WIDTH = ADDR_WIDTH + 1          // Pointer width (extra bit)
)(
    // Write domain
    input  logic                    wr_clk,
    input  logic                    wr_rst_n,
    input  logic                    wr_en,
    input  logic [WIDTH-1:0]        wr_data,
    output logic                    full,
    
    // Read domain  
    input  logic                    rd_clk,
    input  logic                    rd_rst_n,
    input  logic                    rd_en,
    output logic [WIDTH-1:0]        rd_data,
    output logic                    empty
);

    // ========================================================================
    // Internal Signals
    // ========================================================================
    
    // Write domain pointers
    logic [PTR_WIDTH-1:0] wr_binary, wr_binary_next;
    logic [PTR_WIDTH-1:0] wr_gray, wr_gray_next;
    
    // Read domain pointers  
    logic [PTR_WIDTH-1:0] rd_binary, rd_binary_next;
    logic [PTR_WIDTH-1:0] rd_gray, rd_gray_next;
    
    // Synchronized pointers
    logic [PTR_WIDTH-1:0] wr_gray_sync;  // Write gray pointer synchronized to read domain
    logic [PTR_WIDTH-1:0] rd_gray_sync;  // Read gray pointer synchronized to write domain
    logic [PTR_WIDTH-1:0] rd_gray_sync_bin;  // Read gray pointer synchronized to write domain
    
    // Memory signals
    logic [ADDR_WIDTH-1:0] wr_addr, rd_addr;
    logic wr_en_internal, rd_en_internal;
    
    // ========================================================================
    // Gray Code Conversion Functions
    // ========================================================================
    
    // Binary to Gray Code conversion
    function automatic [PTR_WIDTH-1:0] bin_to_gray(input [PTR_WIDTH-1:0] binary);
        bin_to_gray[PTR_WIDTH-1] = binary[PTR_WIDTH-1];  // MSB unchanged
        for (int i = PTR_WIDTH-2; i >= 0; i--) begin
            bin_to_gray[i] = binary[i+1] ^ binary[i];    // XOR adjacent bits
        end
    endfunction
    
    // Gray Code to Binary conversion  
    function automatic [PTR_WIDTH-1:0] gray_to_bin(input [PTR_WIDTH-1:0] gray);
        gray_to_bin[PTR_WIDTH-1] = gray[PTR_WIDTH-1];   // MSB unchanged
        for (int i = PTR_WIDTH-2; i >= 0; i--) begin
            gray_to_bin[i] = gray_to_bin[i+1] ^ gray[i]; // XOR with previous converted bit
        end
    endfunction
    
    // ========================================================================
    // Address Generation
    // ========================================================================
    
    assign wr_addr = wr_binary[ADDR_WIDTH-1:0];  // Use lower bits for memory addressing
    assign rd_addr = rd_binary[ADDR_WIDTH-1:0];
    
    // ========================================================================
    // Write Domain Logic  
    // ========================================================================
    
    // Write pointer increment logic
    assign wr_binary_next = wr_binary + 1'b1;
    assign wr_gray_next = bin_to_gray(wr_binary_next);
    assign rd_gray_sync_bin = gray_to_bin(rd_gray_sync);
    
    // Write enable logic
    assign wr_en_internal = wr_en && !full;
    
    // Write domain sequential logic
    always_ff @(posedge wr_clk or negedge wr_rst_n) begin
        if (!wr_rst_n) begin
            wr_binary <= '0;
            wr_gray <= '0;
        end else if (wr_en_internal) begin
            wr_binary <= wr_binary_next;
            wr_gray <= wr_gray_next;
        end
    end
    
    // Full flag generation
    assign full = (wr_binary_next[PTR_WIDTH-2:0] == rd_gray_sync_bin[PTR_WIDTH-2:0]) && 
                  (wr_binary_next[PTR_WIDTH-1] != rd_gray_sync_bin[PTR_WIDTH-1]);
    
    // ========================================================================
    // Read Domain Logic
    // ========================================================================
    
    // Read pointer increment logic  
    assign rd_binary_next = rd_binary + 1'b1;
    assign rd_gray_next = bin_to_gray(rd_binary_next);
    
    // Read enable logic
    assign rd_en_internal = rd_en && !empty;
    
    // Read domain sequential logic
    always_ff @(posedge rd_clk or negedge rd_rst_n) begin
        if (!rd_rst_n) begin
            rd_binary <= '0;
            rd_gray <= '0; 
        end else if (rd_en_internal) begin
            rd_binary <= rd_binary_next;
            rd_gray <= rd_gray_next;
        end
    end
    
    // Empty flag generation
    assign empty = (rd_gray == wr_gray_sync);
    
    // ========================================================================
    // Pointer Synchronizers 
    // ========================================================================
    
    // Write gray pointer synchronized to read domain
    synchronizer #(.WIDTH(PTR_WIDTH)) wr_sync (
        .i_clk(rd_clk),
        .i_rst_n(rd_rst_n),
        .d_in(wr_gray),
        .d_out(wr_gray_sync)
    );
    
    // Read gray pointer synchronized to write domain  
    synchronizer #(.WIDTH(PTR_WIDTH)) rd_sync (
        .i_clk(wr_clk), 
        .i_rst_n(wr_rst_n),
        .d_in(rd_gray),
        .d_out(rd_gray_sync)
    );
    
    // ========================================================================
    // Memory Implementation - Block RAM (True Registered)
    // ========================================================================
    
    logic [WIDTH-1:0] memory [0:DEPTH-1];
    
    // Write operation
    always_ff @(posedge wr_clk) begin
        if (wr_en_internal) begin
            memory[wr_addr] <= wr_data;
        end
    end
    
    // Read operation (true registered - 1 cycle latency, gated by rd_en)
    always_ff @(posedge rd_clk) begin
        if (!rd_rst_n) begin
            rd_data <= '0;
        end else if (rd_en_internal) begin
            rd_data <= memory[rd_addr];  // Only read when rd_en is active
        end
        // rd_data holds previous value when not reading
    end


endmodule
