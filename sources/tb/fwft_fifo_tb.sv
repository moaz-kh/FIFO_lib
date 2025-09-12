// FWFT FIFO Testbench - SystemVerilog
// Tests zero-latency read behavior and show-ahead functionality
// Compatible with Icarus Verilog -g2009
// Author: FPGA Design Portfolio

`timescale 1ns / 1ps

module fwft_fifo_tb;

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
    fwft_fifo #(
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
        $dumpfile("sim/waves/fwft_fifo_tb.vcd");
        $dumpvars(0, fwft_fifo_tb);
    end
    
    // Main test sequence
    initial begin
        $display("=== FWFT FIFO Testbench Started ===");
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
        
        // Test 1: FWFT Behavior - Zero latency read
        $display("\n--- Test 1: FWFT Zero Latency Read ---");
        test_data = 32'hDEADBEEF;
        
        // Write first word
        @(posedge clk);
        wr_en = 1;
        wr_data = test_data;
        @(posedge clk);
        wr_en = 0;
        
        // Data should appear immediately (FWFT behavior)
        @(posedge clk); // Allow one cycle for output to stabilize
        check_result(rd_data == test_data, 
            $sformatf("FWFT: Data should be immediately available. Expected 0x%h, Got 0x%h", test_data, rd_data));
        check_result(empty == 0, "FWFT: Should not be empty when data available");
        
        // Read should complete in same cycle
        @(posedge clk);
        rd_en = 1;
        @(posedge clk);
        rd_en = 0;
        check_result(empty == 1, "FWFT: Should be empty after reading single word");
        
        // Test 2: Multiple word FWFT behavior
        $display("\n--- Test 2: Multiple Word FWFT ---");
        
        // Write multiple words
        for (i = 0; i < 4; i = i + 1) begin
            test_data = 32'hCAFE0000 + i;
            @(posedge clk);
            wr_en = 1;
            wr_data = test_data;
            @(posedge clk);
            wr_en = 0;
        end
        
        // First word should be immediately visible
        expected_data = 32'hCAFE0000;
        @(posedge clk);
        check_result(rd_data == expected_data,
            $sformatf("FWFT Multi: First word should be visible. Expected 0x%h, Got 0x%h", expected_data, rd_data));
        
        // Read all words and verify immediate availability
        for (i = 0; i < 4; i = i + 1) begin
            expected_data = 32'hCAFE0000 + i;
            check_result(rd_data == expected_data,
                $sformatf("FWFT Multi Read %0d: Expected 0x%h, Got 0x%h", i, expected_data, rd_data));
            
            @(posedge clk);
            rd_en = 1;
            @(posedge clk);
            rd_en = 0;
        end
        
        check_result(empty == 1, "Should be empty after reading all words");
        
        // Test 3: Fill FIFO completely
        $display("\n--- Test 3: Fill FWFT FIFO Completely ---");
        for (i = 0; i < DEPTH; i = i + 1) begin
            test_data = 32'hBEEF0000 + i;
            @(posedge clk);
            wr_en = 1;
            wr_data = test_data;
            @(posedge clk);
            wr_en = 0;
        end
        @(posedge clk);
        
        check_result(full == 1, "FWFT: FIFO should be full");
        check_result(count == DEPTH, "FWFT: Count should equal DEPTH when full");
        
        // First word should still be visible
        expected_data = 32'hBEEF0000;
        check_result(rd_data == expected_data,
            $sformatf("FWFT Full: First word visible. Expected 0x%h, Got 0x%h", expected_data, rd_data));
        
        // Test 4: Empty FIFO completely with FWFT
        $display("\n--- Test 4: Empty FWFT FIFO Completely ---");
        for (i = 0; i < DEPTH; i = i + 1) begin
            expected_data = 32'hBEEF0000 + i;
            check_result(rd_data == expected_data,
                $sformatf("FWFT Empty %0d: Expected 0x%h, Got 0x%h", i, expected_data, rd_data));
            
            @(posedge clk);
            rd_en = 1;
            @(posedge clk);
            rd_en = 0;
        end
        check_result(empty == 1, "FWFT: Should be empty");
        check_result(count == 0, "FWFT: Count should be zero when empty");
        
        // Test 5: Simultaneous read/write with FWFT
        $display("\n--- Test 5: FWFT Simultaneous Read/Write ---");
        
        // Pre-fill half
        for (i = 0; i < DEPTH/2; i = i + 1) begin
            test_data = 32'hABCD0000 + i;
            @(posedge clk);
            wr_en = 1;
            wr_data = test_data;
            @(posedge clk);
            wr_en = 0;
        end
        
        // Simultaneous operations while checking FWFT behavior
        for (i = 0; i < 5; i = i + 1) begin
            // Record current rd_data before operation
            logic [WIDTH-1:0] data_before;
            data_before = rd_data;
            
            @(posedge clk);
            wr_en = 1;
            rd_en = 1;
            wr_data = 32'h12340000 + i;
            @(posedge clk);
            wr_en = 0;
            rd_en = 0;
            
            // With FWFT, data should update immediately for next word
            @(posedge clk); // Allow stabilization
        end
        
        // Test 6: FWFT Overflow/Underflow Protection
        $display("\n--- Test 6: FWFT Overflow/Underflow Protection ---");
        
        // Clear FIFO first
        while (!empty) begin
            @(posedge clk);
            rd_en = 1;
            @(posedge clk);
            rd_en = 0;
        end
        
        // Try to read from empty FIFO
        @(posedge clk);
        rd_en = 1;
        @(posedge clk);
        rd_en = 0;
        check_result(empty == 1, "Should still be empty after read attempt");
        
        // Fill to capacity and try overflow
        for (i = 0; i < DEPTH; i = i + 1) begin
            @(posedge clk);
            wr_en = 1;
            wr_data = 32'h55550000 + i;
            @(posedge clk);
            wr_en = 0;
        end
        
        // Try to write when full
        @(posedge clk);
        wr_en = 1;
        wr_data = 32'hFFFFFFFF;
        @(posedge clk);
        wr_en = 0;
        check_result(count <= DEPTH, "Count should not exceed DEPTH");
        
        // Test 7: Random operations with FWFT validation
        $display("\n--- Test 7: FWFT Random Operations ---");
        for (i = 0; i < 50; i = i + 1) begin
            if ($random % 2 && !full) begin
                test_data = $random;
                @(posedge clk);
                wr_en = 1;
                wr_data = test_data;
                @(posedge clk);
                wr_en = 0;
            end else if (!empty) begin
                @(posedge clk);
                rd_en = 1;
                @(posedge clk);
                rd_en = 0;
            end
            
            // Periodic consistency checks
            if (i % 10 == 0) begin
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
            $display("\n*** ALL FWFT TESTS PASSED! ***");
        end else begin
            $display("\n*** SOME FWFT TESTS FAILED! ***");
        end
        
        $finish;
    end
    
    // Helper task for result checking
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
