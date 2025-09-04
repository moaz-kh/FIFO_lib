// Simplified Testbench for Synchronous FIFO
// Compatible with Icarus Verilog -g2009
// Author: FPGA Design Portfolio

`timescale 1ns / 1ps

module simple_sync_fifo_tb;

    // Test parameters
    parameter WIDTH = 32;
    parameter DEPTH = 16;
    parameter ADDR_WIDTH = $clog2(DEPTH);
    
    // Clock and reset
    logic clk;
    logic rst_n;
    
    // DUT interface
    logic                   wr_en;
    logic [WIDTH-1:0]       wr_data;
    logic                   full;
    logic                   rd_en;
    logic [WIDTH-1:0]       rd_data;
    logic                   empty;
    logic [ADDR_WIDTH:0]    count;
    
    // Testbench variables
    logic [WIDTH-1:0]       test_data;
    logic [WIDTH-1:0]       expected_data;
    int                     test_count;
    int                     pass_count;
    int                     fail_count;
    int                     i;
    
    // DUT instantiation
    sync_fifo #(
        .WIDTH(WIDTH),
        .DEPTH(DEPTH)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .wr_en(wr_en),
        .wr_data(wr_data),
        .full(full),
        .rd_en(rd_en),
        .rd_data(rd_data),
        .empty(empty),
        .count(count)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100MHz clock
    end
    
    // Waveform dump
    initial begin
        $dumpfile("sim/waves/simple_sync_fifo_tb.vcd");
        $dumpvars(0, simple_sync_fifo_tb);
    end
    
    // Main test sequence
    initial begin
        $display("=== Synchronous FIFO Testbench Started ===");
        $display("Configuration: WIDTH=%0d, DEPTH=%0d", WIDTH, DEPTH);
        
        // Initialize
        wr_en = 0;
        wr_data = 0;
        rd_en = 0;
        rst_n = 1;
        test_count = 0;
        pass_count = 0;
        fail_count = 0;
        
        // Reset sequence
        $display("[%0t] Applying reset...", $time);
        rst_n = 0;
        repeat(5) @(posedge clk);
        rst_n = 1;
        @(posedge clk);
        
        // Check reset state
        check_result(empty == 1, "FIFO should be empty after reset");
        check_result(full == 0, "FIFO should not be full after reset");
        check_result(count == 0, "Count should be zero after reset");
        
        // Test 1: Basic write/read
        $display("\n--- Test 1: Basic Write/Read ---");
        for (i = 0; i < 8; i = i + 1) begin
            test_data = 32'hDEADBEE0 + i;
            write_data(test_data);
        end
        
    	expected_data = 32'hDEADBEE0;
        for (i = 0; i < 8; i = i + 1) begin
            read_and_check(expected_data);
            expected_data = 32'hDEADBEE0 + i;
        end
        
        // Test 2: Fill FIFO completely
        $display("\n--- Test 2: Fill FIFO Completely ---");
        for (i = 0; i < DEPTH; i = i + 1) begin
            test_data = 32'hCAFE0000 + i;
            write_data(test_data);
        end
        check_result(full == 1, "FIFO should be full");
        check_result(count == DEPTH, "Count should equal DEPTH when full");
        
        // Test 3: Empty FIFO completely
        $display("\n--- Test 3: Empty FIFO Completely ---");
            expected_data = 32'hCAFE0000;
        for (i = 0; i < DEPTH; i = i + 1) begin
            read_and_check(expected_data);
            expected_data = 32'hCAFE0000 + i;
        end
        check_result(empty == 1, "FIFO should be empty");
        check_result(count == 0, "Count should be zero when empty");
        
        // Test 4: Simultaneous read/write
        $display("\n--- Test 4: Simultaneous Read/Write ---");
        // Pre-fill half
        for (i = 0; i < DEPTH/2; i = i + 1) begin
            test_data = 32'hABCD0000 + i;
            write_data(test_data);
        end
        
        // Simultaneous operations
        for (i = 0; i < 5; i = i + 1) begin
            @(posedge clk);
            wr_en = 1;
            rd_en = 1;
            wr_data = 32'hEF000000 + i;
            @(posedge clk);
            wr_en = 0;
            rd_en = 0;
            // Count should remain relatively stable
        end
        
        // Test 5: Random operations
        $display("\n--- Test 5: Random Operations ---");
        for (i = 0; i < 100; i = i + 1) begin
            if ($random % 2 && !full) begin
                test_data = $random;
                write_data(test_data);
            end else if (!empty) begin
                read_data();
            end
            
            // Basic sanity checks
            if (i % 20 == 0) begin
                check_result(count <= DEPTH, "Count should never exceed DEPTH");
                check_result((count == 0) == empty, "Empty flag consistency");
                check_result((count == DEPTH) == full, "Full flag consistency");
            end
        end
        
        // Final report
        $display("\n=== Final Test Report ===");
        $display("Total Tests: %0d", test_count);
        $display("Passed: %0d", pass_count);
        $display("Failed: %0d", fail_count);
        $display("Success Rate: %0.1f%%", (pass_count * 100.0) / test_count);
        
        if (fail_count == 0) begin
            $display("\n*** ALL TESTS PASSED! ***");
        end else begin
            $display("\n*** SOME TESTS FAILED! ***");
        end
        
        $finish;
    end
    
    // Helper tasks
    task write_data(input [WIDTH-1:0] data);
        @(posedge clk);
        wr_en = 1;
        wr_data = data;
        @(posedge clk);
        wr_en = 0;
    endtask
    
    task read_data();
        @(posedge clk);
        rd_en = 1;
        @(posedge clk);  // Data valid at this edge
        rd_en = 0;
    endtask
    
    task read_and_check(input [WIDTH-1:0] expected);
        @(posedge clk);
        rd_en = 1;
        @(posedge clk);  // Data becomes valid at this edge
        rd_en = 0;
        check_result(rd_data == expected, 
            $sformatf("Read data: Expected 0x%h, Got 0x%h", expected, rd_data));
        @(posedge clk);  // Data becomes valid at this edge
        @(posedge clk);  // Data becomes valid at this edge
    endtask
    
    task check_result(input condition, input string message);
        test_count = test_count + 1;
        if (condition) begin
            pass_count = pass_count + 1;
            $display("[PASS] %s", message);
        end else begin
            fail_count = fail_count + 1;
            $display("[FAIL] %s", message);
        end
    endtask

endmodule
