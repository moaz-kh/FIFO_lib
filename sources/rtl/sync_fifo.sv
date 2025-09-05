// Synchronous FIFO - SystemVerilog Implementation
// Author: FPGA Design Portfolio
// Features:
//   - Parameterizable width and depth (depth must be power of 2)
//   - Full/empty flag generation
//   - Count output for occupancy monitoring
//   - Proper reset handling
//   - Industry-standard interface
//   - SystemVerilog enhanced syntax

`timescale 1ns / 1ps

module sync_fifo #(
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
    
    // Read interface  
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
    
    // Power-up initialization
    initial begin
        wr_ptr = '0;
        rd_ptr = '0;
        rd_data = '0;
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
    
    // Read operation
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            rd_ptr <= '0;
            rd_data <= '0;
        end else if (rd_en_int) begin
            rd_data <= memory[rd_ptr];
            rd_ptr <= rd_ptr + 1'b1;
        end
    end
    
    // Count management
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            fifo_count <= '0;
        end else begin
            unique case ({wr_en_int, rd_en_int})
                2'b00: fifo_count <= fifo_count;           // No operation
                2'b01: fifo_count <= fifo_count - 1'b1;    // Read only
                2'b10: fifo_count <= fifo_count + 1'b1;    // Write only
                2'b11: fifo_count <= fifo_count;           // Simultaneous read/write
                default: fifo_count <= fifo_count;         // Should never reach here
            endcase
        end
    end
    
    // Assertions for design verification
    `ifdef ASSERT_ON
        // Check that we never write when full
        property no_write_when_full;
            @(posedge clk) disable iff (!rst_n)
            full |-> !wr_en_int;
        endproperty
        assert_no_write_when_full: assert property (no_write_when_full)
            else $error("Write attempted when FIFO is full at time %0t", $time);
        
        // Check that we never read when empty
        property no_read_when_empty;
            @(posedge clk) disable iff (!rst_n)
            empty |-> !rd_en_int;
        endproperty
        assert_no_read_when_empty: assert property (no_read_when_empty)
            else $error("Read attempted when FIFO is empty at time %0t", $time);
        
        // Check count consistency
        property count_bounds;
            @(posedge clk) disable iff (!rst_n)
            (count <= DEPTH) && (count >= 0);
        endproperty
        assert_count_bounds: assert property (count_bounds)
            else $error("Count out of bounds: %0d at time %0t", count, $time);
    `endif
    
    // Assertions for design verification
    `ifdef simulation
    // Synthesis-time parameter validation
    initial begin
        if (DEPTH == 0 || (DEPTH & (DEPTH-1)) != 0) begin
            $error("DEPTH must be a power of 2 and greater than 0");
            $finish;
        end
        if (WIDTH == 0) begin
            $error("WIDTH must be greater than 0");
            $finish;
        end
        $info("Sync FIFO instantiated: WIDTH=%0d, DEPTH=%0d, ADDR_WIDTH=%0d", 
              WIDTH, DEPTH, ADDR_WIDTH);
    end
    `endif
endmodule
