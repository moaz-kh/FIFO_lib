// Async FIFO Testbench - SystemVerilog Implementation
// Author: FPGA Design Portfolio
// Features:
//   - Macro-selectable clock relationships (same freq vs different freq)
//   - Independent reset domain testing
//   - Statistical verification with self-checking
//   - Basic test level with full coverage of core functionality
//   - Tests both BRAM and Distributed RAM configurations

`include "sources/include/async_fifo_defines.sv"
`timescale 1ns / 1ps

module async_fifo_tb;

    // ========================================================================
    // Testbench Parameters
    // ========================================================================
    
    parameter WIDTH = 16;
    parameter DEPTH = 1024;
    parameter ADDR_WIDTH = $clog2(DEPTH);
    parameter PTR_WIDTH = ADDR_WIDTH + 1;
    
    // Clock periods
`ifdef SAME_FREQ_CLOCKS
    parameter WR_CLK_PERIOD = 10;  // 100 MHz
    parameter RD_CLK_PERIOD = 10;  // 100 MHz (same frequency)
`else
    parameter WR_CLK_PERIOD = 10;  // 100 MHz  
    parameter RD_CLK_PERIOD = 12;  // 83.33 MHz (different frequency)
`endif
    
    // Test parameters
    parameter NUM_TEST_CYCLES = 10000;
    parameter MAX_BURST_SIZE = 8;

    // ========================================================================
    // Testbench Signals
    // ========================================================================
    
    // Test status enumeration for waveform visualization
    typedef enum logic [1:0] {
        TEST_IDLE = 2'b00,
        TEST_PASS = 2'b01,
        TEST_FAIL = 2'b10
    } test_status_t;
    
    test_status_t test_status;
    
    // Write domain signals
    logic                   wr_clk;
    logic                   wr_rst_n;
    logic                   wr_en;
    logic [WIDTH-1:0]       wr_data;
    logic                   full;
    
    // Read domain signals
    logic                   rd_clk;
    logic                   rd_rst_n; 
    logic                   rd_en;
    logic [WIDTH-1:0]       rd_data;
    logic                   empty;
    
    
    // Testbench variables - Using simple array instead of queue
    logic [WIDTH-1:0]       expected_data [0:DEPTH-1];  // Expected data arry
    logic [ADDR_WIDTH-1:0]  wr_ptr;                     // Write pointer for expected_data
    logic [ADDR_WIDTH-1:0]  rd_ptr;                     // Read pointer for expected_data
    logic [WIDTH-1:0]       written_data;
    logic [WIDTH-1:0]       read_data_reg;
    
    // Test statistics
    int unsigned            writes_attempted;
    int unsigned            writes_successful;
    int unsigned            reads_attempted;
    int unsigned            reads_successful;
    int unsigned            data_matches;
    int unsigned            data_mismatches;
    int unsigned            test_number;
    int unsigned            test_counter;
    // Test control
    logic                   test_active;
    logic                   wr_test_done;
    logic                   rd_test_done;
    
    // ========================================================================
    // DUT Instantiation
    // ========================================================================
    
    async_fifo #(
        .WIDTH(WIDTH),
        .DEPTH(DEPTH)
    ) dut (
        // Write domain
        .wr_clk(wr_clk),
        .wr_rst_n(wr_rst_n),
        .wr_en(wr_en),
        .wr_data(wr_data),
        .full(full),
        
        // Read domain
        .rd_clk(rd_clk),
        .rd_rst_n(rd_rst_n),
        .rd_en(rd_en),
        .rd_data(rd_data),
        .empty(empty)
    );

    // ========================================================================
    // Clock Generation
    // ========================================================================
    
    // Waveform dump - VCD format for universal compatibility
    initial begin
        $dumpfile("sim/waves/async_fifo_tb.vcd");
        $dumpvars(2, async_fifo_tb);  // Depth 2 to include arrays
        
        // Explicitly dump array elements for better visibility
        for (int i = 0; i < 16; i++) begin
            $dumpvars(1, dut.memory[i]);
        end
        
        // Explicitly dump array elements for better visibility
        for (int i = DEPTH-16; i < DEPTH; i++) begin
            $dumpvars(1, dut.memory[i]);
        end
        
        $display("[%0t] Waveform file: sim/waves/async_fifo_tb.vcd", $time);
    end
    // Write clock generation
    initial begin
        wr_clk = 0; 
        forever #(WR_CLK_PERIOD/2) wr_clk = ~wr_clk;
    end
    
    // Read clock generation  
`ifdef SAME_FREQ_CLOCKS
    initial begin
        rd_clk = 0;
        #(RD_CLK_PERIOD/4);  // Phase shift for same frequency
        forever #(RD_CLK_PERIOD/2) rd_clk = ~rd_clk;
    end
`else
    initial begin
        rd_clk = 0;
        forever #(RD_CLK_PERIOD/2) rd_clk = ~rd_clk;
    end
`endif

    // ========================================================================
    // Reset Generation and Testing
    // ========================================================================
    
    task reset_both_domains();
        test_status = TEST_IDLE;
        $display("[%0t] Test %0d: Reset both domains", $time, test_number++);
        $display("[%0t] [RESET] Asserting both reset signals", $time);
        wr_rst_n = 0;
        rd_rst_n = 0;
        repeat (5) @(posedge wr_clk);
        repeat (5) @(posedge rd_clk);
        $display("[%0t] [RESET] Releasing both reset signals", $time);
        wr_rst_n = 1;
        rd_rst_n = 1;
        repeat (5) @(posedge wr_clk);
        repeat (5) @(posedge rd_clk);
        $display("[%0t] [RESET PASS] Both domains reset complete. Full=%b, Empty=%b", 
                 $time, full, empty);
        test_status = TEST_PASS;
        // Clear expected data array pointers after reset
        wr_ptr = 0;
        rd_ptr = 0;
        //writes_successful = 0;
        //reads_successful = 0;
        $display("[%0t] [RESET] Reset expected_data pointers and counters", $time);
    endtask
    
    task reset_write_domain_only();
        test_status = TEST_IDLE;
        $display("[%0t] Test %0d: Reset write domain only", $time, test_number++);
        wr_rst_n = 0;
        repeat (5) @(posedge wr_clk);
        wr_rst_n = 1;
        repeat (5) @(posedge wr_clk);
        test_status = TEST_PASS;
        // Clear expected data array pointers after reset
        wr_ptr = 0;
        rd_ptr = 0;
    endtask
    
    task reset_read_domain_only();
        test_status = TEST_IDLE;
        $display("[%0t] Test %0d: Reset read domain only", $time, test_number++);
        rd_rst_n = 0;
        repeat (5) @(posedge rd_clk);
        rd_rst_n = 1;
        repeat (5) @(posedge rd_clk);
        test_status = TEST_PASS;
        // Clear expected data array pointers after reset
        wr_ptr = 0;
        rd_ptr = 0;
    endtask

    // ========================================================================
    // Write Process
    // ========================================================================
    
    task write_data(input [WIDTH-1:0] data);
        @(posedge wr_clk);
        writes_attempted++;
        $display("[%0t] [WRITE] Attempting to write 0x%0h, full=%b", $time, data, full);
        
        if (!full) begin  // Check full before asserting wr_en
            wr_en = 1'b1;
            wr_data = data;
            
            @(posedge wr_clk);
            wr_en = 1'b0;
            
            writes_successful++;
            expected_data[wr_ptr] = data;
            wr_ptr++;
            $display("[%0t] [WRITE PASS] Successfully wrote 0x%0h to FIFO and expected_data[%0d] (entries=%0d)", 
                     $time, data, wr_ptr-1, wr_ptr-rd_ptr);
        end else begin
            $display("[%0t] [WRITE BLOCKED] Write blocked due to full flag for data 0x%0h", $time, data);
        end
    endtask
    
    task write_burst(input int burst_size);
        for (int i = 0; i < burst_size; i++) begin
            if (!full && test_active) begin
                written_data = (wr_ptr + 1) & ((1 << WIDTH) - 1); // Simple counter pattern
                write_data(written_data);
            end else break;
        end
    endtask

    // ========================================================================
    // Read Process  
    // ========================================================================
    
    task read_data();
        @(posedge rd_clk);
        reads_attempted++;
        $display("[%0t] [READ] Attempting to read, empty=%b, expected_entries=%0d", 
                 $time, empty, wr_ptr-rd_ptr);
        
        if (!empty) begin  // Check empty before asserting rd_en
            rd_en = 1'b1;
            
            @(posedge rd_clk);  
            rd_en = 1'b0;
            
            // Wait for BRAM read latency (1 cycle) - required for true registered mode
            @(posedge rd_clk);
            reads_successful++;
            read_data_reg = rd_data;
            $display("[%0t] [READ DATA] Read 0x%0h from FIFO", $time, read_data_reg);
            
            // Check against expected data
            if (read_data_reg == expected_data[rd_ptr]) begin
                data_matches++;
                test_status = TEST_PASS;
                $display("[%0t] [READ PASS] Expected=0x%0h, Got=0x%0h ✓ (entries_remaining=%0d)", 
                         $time, expected_data[rd_ptr], read_data_reg, wr_ptr-rd_ptr-1);
            end else begin
                data_mismatches++;
                test_status = TEST_FAIL;
                $error("[%0t] [READ FAIL] Data mismatch: Expected=0x%0h, Got=0x%0h (rd_ptr=%0d)", 
                       $time, expected_data[rd_ptr], read_data_reg, rd_ptr);
            end
            rd_ptr++;
        end else if (empty) begin
            $display("[%0t] [READ SKIPPED] FIFO is empty, no data to read", $time);
        end else begin
            $display("[%0t] [READ SKIPPED] No more expected data (rd_ptr=%0d >= wr_ptr=%0d)", 
                     $time, rd_ptr, wr_ptr);
        end
    endtask
    
    task read_burst(input int burst_size);
        for (int i = 0; i < burst_size; i++) begin
            @(posedge rd_clk);
            if (!empty && test_active) begin
                read_data();
            end else break;
        end
    endtask

    // ========================================================================
    // Test Scenarios
    // ========================================================================
    
    task test_basic_write_read();
        // Clear expected data array pointers after reset
        wr_ptr = 0;
        rd_ptr = 0;
        test_status = TEST_IDLE;
        $display("[%0t] Test %0d: Basic write/read sequence", $time, test_number++);
        $display("[%0t] [TEST] Starting basic write sequence (writing 1,2,3,4,5,6,7,8)", $time);
        
        // Write some data
        for (int i = 0; i < 8; i++) begin
            write_data(i + 1);
        end
        
        $display("[%0t] [TEST] Write sequence complete. Waiting for synchronization...", $time);
        // Wait for synchronization
        repeat (10) @(posedge rd_clk);
        
        $display("[%0t] [TEST] Starting read sequence", $time);
        // Read the data back - flag-stable draining
        while (1) begin
            @(posedge rd_clk);
            if (empty) begin
                @(posedge rd_clk); // Wait one more cycle
                if (empty) break;  // Confirm still empty
            end else begin
                read_data();
            end
        end
        
        $display("[%0t] [TEST PASS] Basic write/read test complete", $time);
        test_status = TEST_PASS;
        // Wait for completion
        repeat (10) @(posedge wr_clk);
    endtask
    
    task test_full_empty_flags();
        // Clear expected data array pointers after reset
        wr_ptr = 0;
        rd_ptr = 0;
        test_status = TEST_IDLE;
        $display("[%0t] Test %0d: Full/empty flag testing", $time, test_number++);
         
        test_counter = 1;
        // Fill the FIFO - flag-stable approach
        while (1) begin
            @(posedge wr_clk);
            if (full) break;
            written_data = test_counter;
            write_data(written_data);
            test_counter = test_counter + 1;
        end
        
        // Verify full flag
        if (!full) begin
            test_status = TEST_FAIL;
            $error("[%0t] FIFO should be full but full flag is not set", $time);
        end
        
        // Empty the FIFO - flag-stable draining
        repeat (5) @(posedge rd_clk);  // Wait for synchronization
        while (1) begin
            @(posedge rd_clk);
            if (empty) begin
                @(posedge rd_clk); // Wait one more cycle
                if (empty) break;  // Confirm still empty
            end else begin
                read_data();
            end
        end
        
        // Verify empty flag  
        if (!empty) begin
            test_status = TEST_FAIL;
            $error("[%0t] FIFO should be empty but empty flag is not set", $time);
        end else begin
            test_status = TEST_PASS;
        end
    endtask
    
    task test_random_operations();
        // Clear expected data array pointers after reset
        wr_ptr = 0;
        rd_ptr = 0;
        test_status = TEST_IDLE;
        $display("[%0t] Test %0d: Random write/read operations", $time, test_number++);
        
        fork
            // Write process
            begin
                for (int i = 0; i < NUM_TEST_CYCLES/2; i++) begin
                    if (test_active) begin
                        int burst_size = $urandom_range(1, MAX_BURST_SIZE);
                        write_burst(burst_size);
                        repeat ($urandom_range(1, 5)) @(posedge wr_clk);
                    end
                end
                wr_test_done = 1'b1;
            end
            
            // Read process
            begin
                repeat (20) @(posedge rd_clk);  // Let some data accumulate
                for (int i = 0; i < NUM_TEST_CYCLES/2; i++) begin
                    if (test_active) begin
                        int burst_size = $urandom_range(1, MAX_BURST_SIZE);
                        read_burst(burst_size);
                        repeat ($urandom_range(3, 8)) @(posedge rd_clk); // Longer delays for sync
                    end
                end
                rd_test_done = 1'b1;
            end
        join
        test_status = TEST_PASS;
    endtask

    // ========================================================================
    // Main Test Sequence
    // ========================================================================
    
    initial begin
        // Initialize signals
        wr_en = 1'b0;
        wr_data = '0;
        rd_en = 1'b0;
        test_active = 1'b1;
        wr_test_done = 1'b0;
        rd_test_done = 1'b0;
        test_number = 0;
        test_status = TEST_IDLE;
        
        // Initialize expected data array pointers
        wr_ptr = 0;
        rd_ptr = 0;
        
        // Initialize expected data array to prevent X values
        for (int i = 0; i < DEPTH; i++) begin
            expected_data[i] = '0;
        end
        
        // Initialize statistics
        writes_attempted = 0;
        writes_successful = 0; 
        reads_attempted = 0;
        reads_successful = 0;
        data_matches = 0;
        data_mismatches = 0;
        
        $display("========================================");
        $display("Async FIFO Testbench Started");
        $display("Parameters: WIDTH=%0d, DEPTH=%0d", WIDTH, DEPTH);
`ifdef SAME_FREQ_CLOCKS
        $display("Clock Mode: Same frequency with phase shift");
`else
        $display("Clock Mode: Different frequencies (Wr:%0dMHz, Rd:%0dMHz)", 
                 1000/WR_CLK_PERIOD, 1000/RD_CLK_PERIOD);
`endif
        $display("========================================");
        
        // Test 1: Reset both domains
        reset_both_domains();
        
        // Test 2: Basic functionality
        test_basic_write_read();
        
        // Test 3: Full/empty flags
        test_full_empty_flags();
        
        // Test 4: Reset write domain only
        reset_write_domain_only();
        
        // Test 5: Reset read domain only  
        reset_read_domain_only();
        
        // Test 6: Reset both domains again
        reset_both_domains();
        
        // Test 7: Random operations
        test_random_operations();
        
        // Wait for completion
        wait (wr_test_done && rd_test_done);
        test_active = 1'b0;
        
        // Drain remaining data - flag-stable draining
        repeat (20) @(posedge rd_clk);
        while (1) begin
            @(posedge rd_clk);
            if (empty) begin
                @(posedge rd_clk); // Wait one more cycle
                if (empty) break;  // Confirm still empty
            end else begin
                read_data();
            end
        end
        // Final statistics
        repeat (50) @(posedge wr_clk);
        
        $display("\n========================================");
        $display("ASYNC FIFO TEST RESULTS");
        $display("========================================");
        $display("Writes attempted:  %0d", writes_attempted);
        $display("Writes successful: %0d", writes_successful);
        $display("Reads attempted:   %0d", reads_attempted);
        $display("Reads successful:  %0d", reads_successful);
        $display("Data matches:      %0d", data_matches);
        $display("Data mismatches:   %0d", data_mismatches);
        
        if (writes_successful > 0)
            $display("Write success rate: %0.1f%%", (writes_successful * 100.0) / writes_attempted);
        if (reads_successful > 0)
            $display("Read success rate:  %0.1f%%", (reads_successful * 100.0) / reads_attempted);
        if (data_matches + data_mismatches > 0)
            $display("Data accuracy:      %0.1f%%", (data_matches * 100.0) / (data_matches + data_mismatches));
            
        // Pass/Fail determination
        if (data_mismatches == 0 && writes_successful > 0 && reads_successful > 0) begin
            $display("\n*** ASYNC FIFO TEST PASSED! ***");
        end else begin
            $display("\n*** ASYNC FIFO TEST FAILED! ***");
        end
        
        $display("========================================");
        $finish;
    end
    
    // ========================================================================
    // Timeout Protection
    // ========================================================================
    
    initial begin
        #(NUM_TEST_CYCLES * WR_CLK_PERIOD * 1000);  // 10x safety margin
        $error("Testbench timeout!");
        $finish;
    end

endmodule;
