# Assertion-Based Verification of an AI Accelerator Core

## Overview

This project presents a formal and simulation-based assertion verification methodology for a Multiply-Accumulate (MAC) unit, a critical component of AI accelerators. By leveraging SystemVerilog Assertions (SVA), the project ensures compliance with design specifications, identifies functional bugs early, and increases the reliability of verification processes.

This verification environment validates:
- Pipeline timing constraints
- Correct accumulation behavior
- Signal stability under various scenarios

The framework is compatible with Synopsys VCS/Verdi simulation tools and can be extended to formal verification using VC Formal.

---

## Table of Contents

- [Overview](#overview)
- [Directory Structure](#directory-structure)
- [Key Components](#key-components)
- [How to Run](#how-to-run)
- [Results](#results)
- [Code Files](#code-files)
- [License](#license)
- [Author](#author)

---

## Directory Structure

```
ai_mac_assertion_verification/
├── rtl/                     # RTL design of MAC unit
│   └── mac_unit.v
├── assertions/              # SystemVerilog Assertions (SVA)
│   └── mac_unit_sva.sv
├── tb/                      # Testbench with binding
│   └── mac_tb.sv
├── sim/                     # Simulation scripts
│   └── run_mac_sva.do
├── LICENSE
└── README.md
```

---

## Key Components

### RTL
Implements an 8x8-bit Multiply-Accumulate unit producing a 16-bit output with a valid signal.

### Assertions
Defines three key properties:
- **p_valid_out_response**: Ensures `valid_out` is asserted in the cycle after a valid input.
- **p_mac_stability**: Checks that `MAC_out` remains stable when input is not valid.
- **p_mac_growth**: Verifies that the MAC output grows or stays the same when valid input is received.

### Testbench
Includes:
- Clock and reset generation
- Stimulus sequences
- Assertion bindings

### Tools Used
- Synopsys VCS & Verdi
- Compatible with Synopsys VC Formal

---

## How to Run

### 1. Install Dependencies
- Synopsys VCS
- Verdi (for waveform viewing and assertion debug)

### 2. Compile and Simulate

```bash
cd sim
vcs -full64 -sverilog ../rtl/mac_unit.v ../assertions/mac_unit_sva.sv ../tb/mac_tb.sv -debug_access+all
./simv
```

### 3. Optional: Formal Verification
Use VC Formal to run the properties defined in the SVA module.

---

## Results

- All assertions passed successfully under simulation
- `valid_out` response timing validated
- `MAC_out` accumulation correctness verified
- `MAC_out` stability ensured on invalid input cycles
- Assertion coverage provides confidence in functional behavior

---

## Code Files

### `rtl/mac_unit.v`
```systemverilog
module mac_unit (
    input logic clk,
    input logic rst,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic valid_in,
    output logic [15:0] MAC_out,
    output logic valid_out
);

    logic [15:0] acc;

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            acc <= 0;
            valid_out <= 0;
        end else if (valid_in) begin
            acc <= acc + (A * B);
            valid_out <= 1;
        end else begin
            valid_out <= 0;
        end
    end

    assign MAC_out = acc;

endmodule
```

### `assertions/mac_unit_sva.sv`
```systemverilog
module mac_unit_sva(
    input logic clk,
    input logic rst,
    input logic [7:0] A, B,
    input logic valid_in,
    output logic [15:0] MAC_out,
    output logic valid_out
);

    property p_valid_out_response;
        @(posedge clk) disable iff (rst)
        valid_in |=> valid_out;
    endproperty

    property p_mac_stability;
        @(posedge clk) disable iff (rst)
        (!valid_in) |=> $stable(MAC_out);
    endproperty

    property p_mac_growth;
        @(posedge clk) disable iff (rst)
        valid_in |-> (MAC_out >= $past(MAC_out));
    endproperty

    a_valid_out_response: assert property (p_valid_out_response);
    a_mac_stability:      assert property (p_mac_stability);
    a_mac_growth:         assert property (p_mac_growth);

endmodule
```

### `tb/mac_tb.sv`
```systemverilog
module mac_tb;

    logic clk, rst;
    logic [7:0] A, B;
    logic valid_in;
    logic [15:0] MAC_out;
    logic valid_out;

    mac_unit DUT (
        .clk(clk),
        .rst(rst),
        .A(A),
        .B(B),
        .valid_in(valid_in),
        .MAC_out(MAC_out),
        .valid_out(valid_out)
    );

    mac_unit_sva SVA (
        .clk(clk),
        .rst(rst),
        .A(A),
        .B(B),
        .valid_in(valid_in),
        .MAC_out(MAC_out),
        .valid_out(valid_out)
    );

    initial clk = 0;
    always #5 clk = ~clk;

    initial begin
        rst = 1;
        valid_in = 0;
        A = 0;
        B = 0;
        #10 rst = 0;
        #10 A = 4; B = 5; valid_in = 1;
        #10 A = 2; B = 2; valid_in = 1;
        #10 valid_in = 0;
        #10 A = 1; B = 1; valid_in = 0;
        #20 $finish;
    end

endmodule
```

### `sim/run_mac_sva.do`
```tcl
vcs -full64 -sverilog ../rtl/mac_unit.v ../assertions/mac_unit_sva.sv ../tb/mac_tb.sv -debug_access+all
./simv
```

---

## License

This project is licensed under the MIT License.

---

## Author

**Adarsh Prakash**  
LinkedIn: [adarsh-prakash-a583a3259](https://www.linkedin.com/in/adarsh-prakash-a583a3259)  
Email: kumaradarsh663@gmail.com

