// Async FIFO Defines - Simple Configuration
// Include this file in RTL and testbench files

`ifndef ASYNC_FIFO_DEFINES_SV
`define ASYNC_FIFO_DEFINES_SV

// Memory architecture selection
`define USE_BRAM  // Comment out to use distributed RAM

// Testbench configuration  
`define SAME_FREQ_CLOCKS  // Comment out for different frequency clocks

// Simulation features - Now controlled automatically by Makefile
// - 'make sim' targets: SIMULATION enabled via -D SIMULATION  
// - 'make synth' targets: SYNTHESIS defined via -D SYNTHESIS (disables sim features)
//`define SIMULATION  // Controlled by Makefile - do not enable manually

`endif // ASYNC_FIFO_DEFINES_SV
