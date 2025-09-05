// First Word Fall Through (FWFT) FIFO - SystemVerilog Implementation
// Author: FPGA Design Portfolio
// Features:
//   - Zero read latency - data immediately available when not empty
//   - Show-ahead architecture - rd_data always shows next word
//   - Same interface as synchronous FIFO but FWFT timing behavior
//   - Parameterizable width and depth (depth must be power of 2)
//   - Full/empty flag generation with count output
//   - FPGA-optimized design with proper reset handling

`timescale 1ns / 1ps

module fwft_fifo #(
    parameter WIDTH = 8,            // Data width in bits  
    parameter DEPTH = 16,           // FIFO depth (must be power of 2)
    parameter ADDR_WIDTH = $clog2(DEPTH)  // Address width automatically calculated
)(
    // Clock and reset
    input  logic                    clk,
    input  logic                    rst_n,
    
    // Write interface
    input  logic                    wr_en,
    input  logic [WIDTH-1:0]        wr_data,
    output logic                    full,
    
    // Read interface (FWFT - zero latency)
    input  logic                    rd_en,
    output logic [WIDTH-1:0]        rd_data,
    output logic                    empty,
    
    // Status
    output logic [ADDR_WIDTH:0]     count        // Current number of entries
);

    // Internal memory array
    logic [WIDTH-1:0] memory [DEPTH];
    
    // Address pointers
    logic [ADDR_WIDTH-1:0] wr_ptr;
    logic [ADDR_WIDTH-1:0] rd_ptr;
    
    // Count register
    logic [ADDR_WIDTH:0] fifo_count;
    
    // Status flags  
    assign full  = (fifo_count == DEPTH);
    assign empty = (fifo_count == '0);
    assign count = fifo_count;
    
    // Write and read enable conditions
    logic wr_en_int, rd_en_int;
    assign wr_en_int = wr_en & ~full;
    assign rd_en_int = rd_en & ~empty;
    
    // FWFT read data logic - combinatorial read from memory
    //assign rd_data = empty ? '0 : memory[rd_ptr];
    assign rd_data = memory[rd_ptr];
    
    // Power-up initialization
    initial begin
        wr_ptr = '0;
        rd_ptr = '0;
        fifo_count = '0;
    end
    
    // Write operation
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            wr_ptr <= '0;
        end else if (wr_en_int) begin
            memory[wr_ptr] <= wr_data;
            wr_ptr <= wr_ptr + 1'b1;
        end
    end
    
    // Read pointer management
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            rd_ptr <= '0;
        end else if (rd_en_int) begin
            rd_ptr <= rd_ptr + 1'b1;
        end
    end
    
    // Count management
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            fifo_count <= '0;
        end else begin
             	case ({wr_en_int, rd_en_int})
                2'b00: fifo_count <= fifo_count;           // No operation
                2'b01: fifo_count <= fifo_count - 1'b1;    // Read only
                2'b10: fifo_count <= fifo_count + 1'b1;    // Write only
                2'b11: fifo_count <= fifo_count;           // Simultaneous read/write
                default: fifo_count <= fifo_count;         // Should never reach here
            endcase
        end
    end
    
    // Assertions for design verification
    `ifdef simulation
    // Synthesis-time parameter validation
    initial begin
        if (DEPTH == 0 || (DEPTH & (DEPTH-1)) != 0) begin
            $error("DEPTH must be a power of 2 and greater than 0. Current DEPTH = %0d", DEPTH);
            $finish;
        end
        if (WIDTH <= 0) begin
            $error("WIDTH must be greater than 0. Current WIDTH = %0d", WIDTH);
            $finish;  
        end
        $info("FWFT FIFO instantiated: WIDTH=%0d, DEPTH=%0d, ADDR_WIDTH=%0d", 
              WIDTH, DEPTH, ADDR_WIDTH);
    end
    `endif

endmodule
