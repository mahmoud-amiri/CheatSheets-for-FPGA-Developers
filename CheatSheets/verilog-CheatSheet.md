---
title: verilog CheatSheet
description: The most commonly used verilog syntaxes are given here.
created: 2022-10-01
---

## Table of Contents

- [CheatSheet-Name CheatSheet for Developers](#cheatsheet-name-cheatsheet-for-developers)
  - [1st Section](#1st-section)
    - [1st Sub/Nested-Section](#1st-subnested-section)
      - [1st Double-Sub/Nested-Section](#1st-double-subnested-section)
  - [2nd Section](#2nd-section)
  - [nth Section](#nth-section)

# Verilog CheatSheet for Developers

## Modules

```verilog
// Module declaration with parameters
module EntityName #(
    parameter n = 16, // Default value 16
    parameter m = 32  // Default value 32
)(
    input FirstPort,                     // Single bit input
    output SecondPort,                   // Single bit output
    inout [n-1:0] ThirdPort              // Bi-directional bus with size defined by parameter 'n'
);

    // Signal declarations
    wire wire1;                         // Single wire signal
    wire [m-1:0] bus;                   // Bus signal with size defined by parameter 'm'

    // Continuous assignments
    assign wire1 = FirstPort;           // Assignment using wire
    assign SecondPort = wire1;
    assign bus = {m{1'b0}};             // Initialize bus to all zeros

endmodule

```
**[🔼Back to Top](#table-of-contents)**

## Module Instantiation

```verilog
// Definition of SubComponent
module SubComponent(
    input [7:0] InputA,
    input [7:0] InputB,
    output [7:0] OutputX
);
    // Module internals here
    // For example, a simple bitwise AND operation just as a placeholder
    assign OutputX = InputA & InputB;
endmodule

// Parent module where SubComponent is instantiated
module ParentEntity(
    input [7:0] ParentInput1,
    input [7:0] ParentInput2,
    output [7:0] InternalOutput
);
    // Instantiation of SubComponent
    SubComponent instance_name (
        .InputA(ParentInput1),       // Connect ParentInput1 to InputA of SubComponent
        .InputB(ParentInput2),       // Connect ParentInput2 to InputB of SubComponent
        .OutputX(InternalOutput)     // Connect InternalOutput to OutputX of SubComponent
    );
endmodule

```
**[🔼Back to Top](#table-of-contents)**

## Always block

```verilog
// Always block with synchronous reset
    always @(posedge clk) begin
        if (reset) begin
            data_out <= 8'b00000000;  // Reset data output to all zeros
        end else begin
            data_out <= data_in;     // Transfer input to output if not reset
        end
    end
```
**[🔼Back to Top](#table-of-contents)**

## Assignment

1. Continuous Assignment
```verilog
assign A = B;  // A will continuously take the value of B
```

2. Blocking Assignment
```verilog
always @(posedge clk) begin
    temp = 5;  // Immediate update
    temp = temp + 1;  // Also immediate, using the new value of temp
end
```
3. Non-blocking Assignment
```verilog
always @(posedge clk) begin
    A <= B;  // Schedule update for the end of the simulation cycle
    A <= A + 1;  // Schedule another update, does not immediately see the first assignment's effect
end

```

4. Conditional Assignment
```verilog
assign C = (SEL == 2'b00) ? A :
           (SEL == 2'b01) ? B : 1'b0;
```

5. Selected Signal Assignment
```verilog
always @(*) begin
    case (SEL)
        2'b00: D = A;
        2'b01: D = B;
        2'b10: D = C;
        default: D = 1'b0;
    endcase
end
```

6. Initial Assignment
```verilog
initial begin
    A = 0;  // Initialize A to 0 at the start of simulation
end
```
**[🔼Back to Top](#table-of-contents)**

## Data types

```verilog
// Enumerated Type
localparam Idle = 2'b00, Running = 2'b01, Stopped = 2'b10;
reg [1:0] state
```

```verilog
//Integer Type
integer counter; // Simply declared as integer
```

```verilog
//Floating Point Type
real real_number;  // Simulation only, not for synthesis
```

```verilog
//Physical Type
// Use delays directly in the timing specifications
#500ns;
```

```verilog
//Arrays
reg [7:0] data_byte; // Array of bits
```

```verilog
//Multidimensional Array
reg [31:0] my_matrix[1:3][1:3]; // Array of integers in SystemVerilog

```
**[🔼Back to Top](#table-of-contents)**

## Type Conversions

```verilog
//Integer to Vector:
reg [7:0] my_vector;
integer my_integer = 5;

always @(posedge clk) begin
    my_vector <= my_integer; // Automatically extends or truncates
end

```

```verilog
//Vector to Integer:
integer my_integer;
reg [7:0] my_vector = 8'b00000101;

always @(posedge clk) begin
    my_integer <= my_vector; // Interpret vector as integer
end
```
**[🔼Back to Top](#table-of-contents)**

## Operators

```verilog
//Logical Operators
assign C = A & B;  // Logical AND
assign C = A | B;  // Logical OR
assign C = A ~& B; // Logical NAND
assign C = A ~| B; // Logical NOR
assign C = A ^ B;  // Logical XOR
assign C = A ~^ B; // Logical XNOR
assign B = ~A;     // Logical NOT

```

```verilog
//Relational Operators
Equal to: ==
Not equal to: !=
Less than: <
Less than or equal to: <=
Greater than: >
Greater than or equal to: >=
```

```verilog
//Arithmetic Operators
assign C = A + B;  // Addition
assign C = A - B;  // Subtraction
assign C = A * B;  // Multiplication
assign C = A / B;  // Division
assign C = A % B;  // Modulus

```

```verilog
//Shift Operators
assign C = A << 1;  // Shift left
assign C = A >> 1;  // Shift right
assign C = A >>> 1; // Arithmetic shift right
assign C = A <<< 1; // Arithmetic shift left
```

```verilog
//Concatenation
assign C = {A, B};  // Concatenates A and B

```

```verilog
//Conditional (Ternary) Operator
assign C = (A > B) ? A : B;  // If A > B, C = A; otherwise, C = B

```
**[🔼Back to Top](#table-of-contents)**

## conditionals 

```verilog
//If Statement
always @(posedge clk) begin
    if (reset) begin
        // Synchronous reset condition
        counter <= 0;
    end else if (enable) begin
        // Enable condition
        counter <= counter + 1;
    end else begin
        // Default condition: maintain the counter value
        counter <= counter;
    end
end

```

```verilog
//Case Statement
always @(*) begin
    case (state)
        IDLE: led <= 0;     // IDLE state actions
        RUNNING: led <= 1;  // RUNNING state actions
        ERROR: led <= 0;    // ERROR state actions
        default: led <= 1'bx;  // Default actions, equivalent to VHDL's 'others'
    endcase
end

```

```verilog
//Conditional Signal Assignment
assign led = (switch == 1) ? 1 : 0;

```

```verilog
//Selected Signal Assignment
always @(*) begin
    case (state)
        RUNNING: led <= 1;
        IDLE: led <= 0;
        ERROR: led <= 0;
        default: led <= 1'bx;
    endcase
end

```

```verilog
//With-Select-When
always @(*) begin
    case (operation)
        2'b00: result <= a + b;
        2'b01: result <= a - b;
        2'b10: result <= a * b;
        default: result <= a / b; // Using default for 'others'
    endcase
end

```
**[🔼Back to Top](#table-of-contents)**

## Testbench Template

```verilog
// Include timescale directive for simulation time units
`timescale 1ns / 1ps

module tb_MyDesign;

    // Testbench does not have ports

    // DUT Port Signals
    reg clk;
    reg reset;
    reg [7:0] input_sig;
    wire [7:0] output_sig;

    // Clock period definition
    parameter clk_period = 10; // Clock period in nanoseconds

    // Instantiate the Design Under Test (DUT)
    MyDesign uut (
        .clk(clk),
        .reset(reset),
        .input_sig(input_sig),
        .output_sig(output_sig)
    );

    // Clock process
    always begin
        clk = 0;
        # (clk_period / 2) clk = 1;
        # (clk_period / 2);
    end

    // Test stimulus process
    initial begin
        // Initialize Inputs
        reset = 1;
        input_sig = 8'b00000000;

        // Wait for 100 ns for global reset to finish
        #100;

        // Apply stimulus to the DUT
        reset = 0; // Release reset
        # (clk_period * 10);

        input_sig = 8'b00000001;
        # (clk_period * 10);

        input_sig = 8'b00000010;
        # (clk_period * 10);

        // Additional stimulus can be added here

        // Finish the test
        $display("End of test");
        $finish; // Terminate simulation
    end

endmodule

```
**[🔼Back to Top](#table-of-contents)**

## Reading from a File and Writing to a File

```verilog
`timescale 1ns / 1ps

module ReadFileTB;

    // Declare an integer for the file descriptor
    integer file_in;
    // Error variable for file operations
    integer status;
    // Variable to store the read values
    reg [7:0] value_read;

    // Path to the input file
    initial begin
        // Open the file in read mode
        file_in = $fopen("input_file.txt", "r");
        if (file_in == 0) begin
            $display("Failed to open file.");
            $finish;
        end

        // Read until the end of the file
        while (!$feof(file_in)) begin
            status = $fscanf(file_in, "%b\n", value_read);
            // Now value_read contains the data from the file for further processing
            $display("Read value: %b", value_read);
        end

        // Close the file
        $fclose(file_in);
        $finish;
    end

endmodule

```

```verilog
`timescale 1ns / 1ps

module WriteFileTB;

    // Declare an integer for the file descriptor
    integer file_out;
    // Variable to write to the file
    reg [7:0] value_write;

    initial begin
        // Open the file in write mode
        file_out = $fopen("output_file.txt", "w");
        if (file_out == 0) begin
            $display("Failed to open file.");
            $finish;
        end

        // Write 10 lines to the file
        for (int i = 1; i <= 10; i++) begin
            value_write = i;
            $fwrite(file_out, "%b\n", value_write);
        end

        // Close the file
        $fclose(file_out);
        $finish;
    end

endmodule

```
**[🔼Back to Top](#table-of-contents)*