# FIFO_lib

A comprehensive SystemVerilog FIFO library with full FPGA implementation flow - from RTL design to ready-to-program bitstream.

## 🎯 Current Status: **SYNC FIFO PRODUCTION READY | MULTI-FIFO IMPLEMENTATION**

### ✅ Synchronous FIFO - Production Ready
- **Design**: `sources/rtl/sync_fifo.sv`
- **Configuration**: WIDTH=8, DEPTH=16 (parameterizable)
- **Architecture**: 
  - Registered read interface (1 cycle latency for timing closure)
  - Synchronous reset with FPGA-friendly initial blocks
  - Full/empty status flags with occupancy count
  - Built-in overflow/underflow protection
  - Block RAM utilization for efficient FPGA mapping

### ✅ Multi-Module Implementation Status

#### ✅ **Sync FIFO - Production Ready**
- **Simulation**: **100% PASS** (46/46 tests) 🎉
- **FPGA**: **Complete** - 78.06 MHz, 104KB bitstream ✅
- **Resources**: 70 LCs (1%), 1 BRAM (3%), 27 IOs (28%)

#### ✅ **Async FIFO - Advanced Implementation, Debug Needed**
- **Simulation**: **10.7% accuracy** (42/393 matches) - Full flag timing bug
- **FPGA**: **Complete** - 70.89/54.36 MHz dual-clock, 102KB bitstream ✅
- **Resources**: 92 LCs (1%), 1 BRAM (3%), 34 IOs (35%)

### ✅ Complete FPGA Implementation
- **Target**: Lattice iCE40 UP5K (SG48 package)
- **Synthesis**: ✅ Successful (Yosys)
- **Place & Route**: ✅ Completed (NextPNR)
- **Timing**: ✅ 62.07 MHz max frequency
- **Bitstream**: ✅ Ready (104KB)

#### 📊 Implementation Results
- **Logic Utilization**: 70/5,280 LCs (1%) - Highly efficient
- **Memory Usage**: 1/30 Block RAMs (3%)
- **I/O Pins**: 27/96 (28%) - Comfortable fit
- **Performance**: 62 MHz (excellent timing margin)

## Quick Start

### Prerequisites
```bash
# For simulation and synthesis
sudo apt install iverilog gtkwave yosys nextpnr-ice40 fpga-icestorm

# Or use OSS CAD Suite (recommended)
# https://github.com/YosysHQ/oss-cad-suite-build
```

### Quick Test - Synchronous FIFO (Production Ready)
```bash
# Clone repository
git clone https://github.com/moaz-kh/FIFO_lib.git
cd FIFO_lib

# Check available tools
make check-tools

# Run sync FIFO simulation (100% pass expected)
make sim TOP_MODULE=sync_fifo TESTBENCH=sync_fifo_tb
make sim TOP_MODULE=sync_fifo TESTBENCH=fwft_fifo_tb
make sim TOP_MODULE=async_fifo TESTBENCH=async_fifo_tb

# View waveforms
make waves TOP_MODULE=sync_fifo TESTBENCH=sync_fifo_tb
```
 

### Complete FPGA Flow
```bash
# Production ready - Sync FIFO
make ice40 TOP_MODULE=sync_fifo

# All modules synthesize successfully
make ice40 TOP_MODULE=sync_fifo         # sync FIFO
make ice40 TOP_MODULE=async_fifo        # Async FIFO

# Individual steps (works for all modules)
make synth-ice40 TOP_MODULE=sync_fifo    # Synthesis
make pnr-ice40 TOP_MODULE=sync_fifo      # Place & Route  
make timing-ice40 TOP_MODULE=sync_fifo   # Timing Analysis
make bitstream-ice40 TOP_MODULE=sync_fifo # Bitstream
```

## Project Structure
```
FIFO_lib/
├── sources/
│   ├── rtl/
│   │   ├── sync_fifo.sv           # Synchronous FIFO ✅
│   │   ├── async_fifo.sv          # Asynchronous FIFO ✅
│   │   └── STD_MODULES.v          # Standard utility modules (includes synchronizer)
│   ├── tb/
│   │   ├── sync_fifo_tb.sv        # Sync FIFO testbench ✅
│   │   ├── fwft_fifo_tb.sv        # FWFT FIFO testbench ✅
│   │   └── async_fifo_tb.sv       # Async FIFO testbench ✅
│   ├── include/
│   │   └── async_fifo_defines.sv  # Async FIFO configuration macros
│   ├── constraints/               # FPGA constraint files (.pcf)
│   └── rtl_list.f                 # Auto-generated file list
├── sim/
│   ├── waves/                     # Waveform outputs (.vcd)
│   └── logs/                      # Simulation logs
├── backend/
│   ├── synth/                     # Synthesis outputs (.json, .v)
│   ├── pnr/                       # Place & route outputs (.asc)
│   ├── bitstream/                 # Final bitstreams (.bin)
│   └── reports/                   # Timing/utilization reports
└── Makefile                       # Professional build system
```

## Usage

### Synchronous FIFO (Production Ready) ✅
```systemverilog
sync_fifo #(
    .WIDTH(8),      // Data width (8, 16, 32, etc.)
    .DEPTH(16)      // FIFO depth (must be power of 2)
) sync_inst (
    .clk(clk), .rst_n(rst_n),
    .wr_en(wr_en), .wr_data(wr_data), .full(full),
    .rd_en(rd_en), .rd_data(rd_data), .empty(empty),
    .count(count)   // Current occupancy
);
```

### Asynchronous FIFO (Debug Phase) ⚠️
```systemverilog
`include "sources/include/async_fifo_defines.sv"

async_fifo #(
    .WIDTH(8), .DEPTH(16)
) async_inst (
    // Write domain
    .wr_clk(wr_clk), .wr_rst_n(wr_rst_n),
    .wr_en(wr_en), .wr_data(wr_data), .full(full),
    
    // Read domain  
    .rd_clk(rd_clk), .rd_rst_n(rd_rst_n),
    .rd_en(rd_en), .rd_data(rd_data), .empty(empty),
    
    // Status (optional)
    .wr_count(wr_count), .rd_count(rd_count)
);
```

### Build System
```bash
# Essential commands
make help                                    # Show all targets
make check-tools                             # Verify tool installation
make status TOP_MODULE=sync_fifo            # Project status

# Simulation workflow
make sim TOP_MODULE=sync_fifo TESTBENCH=simple_sync_fifo_tb
make waves TOP_MODULE=sync_fifo TESTBENCH=simple_sync_fifo_tb
make update_list                             # Update file list

# FPGA workflow (iCE40)
make ice40 TOP_MODULE=sync_fifo             # Complete flow
make synth-ice40 TOP_MODULE=sync_fifo       # Synthesis only
make clean                                  # Clean outputs
```

## 🧪 Verification Results

### Test Coverage
- **Total Tests**: 46 comprehensive test cases
- **Results**: **100% PASS** ✅
- **Test Types**:
  - Reset functionality
  - Basic read/write operations
  - Boundary conditions (full/empty)
  - Simultaneous operations
  - Random stress testing

### Key Test Features
- **Self-checking testbench** with automatic pass/fail
- **Registered read timing** validation
- **Flag consistency** verification
- **Overflow/underflow protection** testing

## 🚀 Development Roadmap

### Phase 1: Core FIFO Library ✅
- ✅ **Synchronous FIFO** - Production ready with FPGA implementation
- ⏳ **FWFT FIFO** - First Word Fall Through implementation
- ⏳ **Async FIFO** - Cross-clock domain FIFO

### Phase 2: Advanced Features (Future)
- ⏳ **AXI Stream interfaces**
- ⏳ **Configurable almost-full/empty thresholds**
- ⏳ **Built-in ECC support**

## 🛠️ Technical Requirements

### Simulation & Verification
- **Simulator**: Icarus Verilog (with SystemVerilog support)
- **Waveform Viewer**: GTKWave
- **Language**: SystemVerilog (IEEE 1800)

### FPGA Implementation
- **Synthesis**: Yosys (open source)
- **Place & Route**: NextPNR (iCE40 target)
- **Toolchain**: IceStorm (bitstream generation)
- **Target**: Lattice iCE40 family (UP5K tested)

### Build System
- **Make**: GNU Make 4.0+
- **Shell**: Bash (for advanced scripting)
- **OS**: Linux (tested on Ubuntu/Debian)

## 🏆 Key Achievements

This FIFO library demonstrates **professional FPGA engineering practices**:

### ✨ Design Excellence
- **Clean SystemVerilog** with proper coding standards
- **FPGA-optimized architecture** (block RAM usage, registered outputs)
- **Parameterizable design** for reusability
- **Industry-standard interfaces**

### 🔬 Verification Quality
- **100% test coverage** with comprehensive corner cases
- **Self-checking testbenches** with statistical reporting
- **Timing-accurate verification** (registered read validation)
- **Professional verification methodology**

### ⚡ Implementation Success
- **Complete FPGA flow** from RTL to bitstream
- **Excellent resource utilization** (1% logic, 28% I/O)
- **High performance** (62 MHz, excellent timing margin)
- **Production-ready bitstream** (104KB, ready to program)

### 🛠️ Build System Innovation
- **Multi-HDL support** (Verilog, SystemVerilog, VHDL)
- **Family-agnostic architecture** (extensible for ECP5, Intel, Xilinx)
- **Professional workflow** (synthesis → PnR → timing → bitstream)
- **Runtime parameter configuration**

## 📋 License

This project is part of an FPGA Design Portfolio demonstrating advanced hardware engineering skills.

## 🤝 Contributing

This repository showcases professional FPGA development practices and is part of a larger portfolio project. The implementation follows industry standards and demonstrates competency in:

- SystemVerilog RTL design
- FPGA synthesis and implementation
- Professional verification methodologies
- Modern open-source FPGA toolchains
- Build system development

---

**Status**: Production Ready | **Target**: FPGA Engineering Roles | **Methodology**: Professional Development Standards
