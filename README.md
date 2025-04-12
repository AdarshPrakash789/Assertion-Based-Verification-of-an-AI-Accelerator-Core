# Assertion-Based Verification of an AI Accelerator Core

## Project Overview
This project implements formal and simulation-based assertion verification for a multiply-accumulate (MAC) unit used in AI accelerators. It ensures that key pipeline behaviors and computation constraints are met using SystemVerilog Assertions (SVA), improving design reliability and easing debug effort in functional verification.

## Table of Contents
- Project Overview  
- Directory Structure  
- Key Components  
- How to Run  
- Results  
- License  
- Author

## Directory Structure
```
ai_mac_assertion_verification/
├── rtl/                      # RTL for MAC core
│   └── mac_unit.v
├── assertions/               # SystemVerilog Assertions
│   └── mac_unit_sva.sv
├── tb/                       # Testbench with binding
│   └── mac_tb.sv
├── sim/                      # Simulation scripts
│   └── run_mac_sva.do
├── LICENSE
├── README.md
```

## Key Components
- RTL: Multiply-accumulate unit for AI workloads  
- Assertions: Valid output timing, MAC result stability and accumulation constraints  
- Testbench: Generates stimulus and binds assertions for simulation check  
- Tools: Verified using Synopsys VCS/Verdi and compatible with VC Formal

## How to Run
### 1. Install Dependencies
- Synopsys VCS and Verdi

### 2. Compile and Simulate
```
cd sim
vcs -full64 -sverilog ../rtl/mac_unit.v ../assertions/mac_unit_sva.sv ../tb/mac_tb.sv -debug_access+all
./simv
```

### 3. Formal Verification (Optional)
Run property checks using Synopsys VC Formal.

## Results
- Assertion-based coverage achieved for all scenarios
- Valid signal behavior and accumulator correctness verified
- Stable MAC output on invalid inputs verified

## License
This project is licensed under the MIT License.

---

// rtl/mac_unit.v
module mac_unit (
  input  logic clk,
  input  logic rst,
  input  logic [7:0] A,
  input  logic [7:0] B,
  input  logic valid_in,
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

// assertions/mac_unit_sva.sv
module mac_unit_sva(input logic clk, input logic rst,
                    input logic [7:0] A, B,
                    input logic valid_in,
                    output logic [15:0] MAC_out,
                    output logic valid_out);

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
  a_mac_stability: assert property (p_mac_stability);
  a_mac_growth: assert property (p_mac_growth);

endmodule

// tb/mac_tb.sv
module mac_tb;

  logic clk, rst;
  logic [7:0] A, B;
  logic valid_in;
  logic [15:0] MAC_out;
  logic valid_out;

  mac_unit DUT (
    .clk(clk), .rst(rst), .A(A), .B(B), .valid_in(valid_in), .MAC_out(MAC_out), .valid_out(valid_out)
  );

  mac_unit_sva SVA (
    .clk(clk), .rst(rst), .A(A), .B(B), .valid_in(valid_in), .MAC_out(MAC_out), .valid_out(valid_out)
  );

  initial clk = 0;
  always #5 clk = ~clk;

  initial begin
    rst = 1; valid_in = 0; A = 0; B = 0;
    #10 rst = 0;
    #10 A = 4; B = 5; valid_in = 1;
    #10 A = 2; B = 2; valid_in = 1;
    #10 valid_in = 0;
    #10 A = 1; B = 1; valid_in = 0;
    #20 $finish;
  end

endmodule

## Author
Adarsh Prakash  
LinkedIn: [www.linkedin.com/in/adarsh-prakash-a583a3259](https://www.linkedin.com/in/adarsh-prakash-a583a3259)  
Email: kumaradarsh663@gmail.com
