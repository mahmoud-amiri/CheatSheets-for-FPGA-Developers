---
title: System verilog coverage CheatSheet
description: The most commonly used System verilog coverage syntaxes are given here.
created: 2024-04-06
---

## Table of Contents

- [CheatSheet-Name CheatSheet for Developers](#cheatsheet-name-cheatsheet-for-developers)
  - [1st Section](#1st-section)
    - [1st Sub/Nested-Section](#1st-subnested-section)
      - [1st Double-Sub/Nested-Section](#1st-double-subnested-section)
  - [2nd Section](#2nd-section)
  - [nth Section](#nth-section)

# System verilog coverage CheatSheet for Developers

## Declare a covergroup

`Covergroup`: A construct used to define a set of coverage points in SystemVerilog.
`Coverpoint`: A specific point within the covergroup to be monitored.
`Clocking Event`: Specifies when the coverage points are sampled.

```systemverilog
bit [1:0] offset; //These variables are used within the covergroup for defining coverpoints.
logic [7:0] addr;

covergroup g1 @(posedge clk);//This determines when the coverage points are sampled.
  oc : coverpoint offset; //oc and ac are the labels for these coverpoints.
  ac : coverpoint addr;
endgroup

g1 g1_inst = new;//You need to instantiate the covergroup using the new operator
```

## iff

`iff` is an optional condition that disable coverage for that cover point.

```systemverilog
bit [1:0] offset; 

covergroup g1 @(posedge clk);
  oc : coverpoint offset iff (!reset){}
endgroup

g1 g1_inst = new;//You need to instantiate the covergroup using the new operator
```

## bins

```systemverilog
enum {iack, IORead, IOWrite, MemRead, MemWite} protocolCommand; 

covergroup g1 @(negedge FRAME_);
  oc : coverpoint offset;//5 auto generated bins
endgroup

g1 g1_inst = new;
```

```systemverilog
enum [PCI_CB_ENUM_WIDTH] {
    MemRead, IoRead, MemWrite, MemCommandWait,
    ConfRead_Write_ConfWait_MemMutual,
    LdAddrdr,
    iack_SpecialAck
};

covergroup pciCmdCov with function sample (pciCmdType cmd);
    coverpoint pciCmds : coverpoint cmd;
    
    {
        bins pcicmds [] = {IoRead_MemWrite_ConfReadWrite_MemMutual};
        bins pcicmds [] = {iack_SpecialAck};
        
        // EXPLICIT bin to categorize when PCI cycles are 100% covered.
        // For example, when PCI bins are 100% covered,
        // we know that all PCI Read type cycles have been exercised.
    }
endgroup

```

```systemverilog
covergroup g1 @(posedge clk);
  // SINGLE bin to cover ALL adr values 0, 1, 2, 3
  bins adrbin1 = {[0:3]};

  // INDIVIDUAL bins adrbin2 and adrbin3 for EACH adr value (4, 5)
  bins adrbin2 = {[4:5]};
  bins adrbin3 = {[6:8]};

  // Fixed array of bins (here with # of bins less than range value)
  // 'adr' value 6 is in bin 'adrbin3[1]'
  bins adrbin4[3] = {[9:10]};

  // Fixed array of bins (here with # of bins greater than range value)
  // 'adr' value 9 will be covered in bin 'adrbin5[1]'
  bins adrbin5[2] = {[9:12], [11:16]};

  // Everything else that's not covered by bins above ends up in 'others'
  bins others = default;
endgroup
```

## passing arguments

```systemverilog
bit [1:0] adr1, adr2; 

covergroup g1(int low, int high, ref bit [7:0] address)@(negedge clk);
  ac : coverpoint address{
    bind addrbin[] = {[low:high]};
  }
endgroup

g1 g1_inst1 = new(0,127, addr1);
g1 g1_inst2 = new(128,255, addr2);
```

## cross coverage

```systemverilog
bit [1:0] offset, adr;

covergroup cg1 @(posedge clk);
  ofst: coverpoint offset { bins ofsbin[] = {[0:3]}; }//has 4 bins for values 0, 1, 2, 3.
  ar: coverpoint adr { bins adrbin[] = {[0:3]}; }//has 4 bins for values 0, 1, 2, 3.
  adr_ofst: cross ar, ofst;// results in 16 cross coverpoints 
endgroup

cg1 cg1Inst = new;

```

### ignore

```systemverilog
int x, y;
covergroup xyCG;
  x_c : coverpoint x;
  y_c : coverpoint y;
  xy_cross : cross x_c, y_c {
    ignore_bins ignore_x_GT_y = xy_cross with (x_c > y_c);//selectively filters bins based on the condition x_c > y_c
  }
endgroup
```

```systemverilog
module top;
  logic [0 : 3] a, b;
  covergroup cg @(posedge clk);
    coverpoint a {
      bins low = {[0 : 7]};
      bins high = {[8 : 15]};
    }
    coverpoint b {
      bins two[] = b with (item%2 == 0);
      bins three[] = b with (item%3 == 0);
    }
    X: cross a, b
    {
    bins XAB =  binsof ((b.low) with (b > 5)) && binsof ((a.low) with (a < 10));
    }
    endgroup
endmodule
```

## transition

```systemverilog
bit[7:0] adr1;
bit[7:0] adr2;

covergroup cg @(posedge clk);
{
  ac:coverpoint adr1
  {
    bins ar1 = (8'h00 => 8'hff);
  }
  dc:coverpoint adr2
  {
    bins ar2 = (1'b1 => 1'b0);
  }
  
  cross: cross ac, dc;
}

endgroup

gc = new;
gc.sclnst();

```

## wildcard

```systemverilog
covergroup gc @(posedge clk);
  coverpoint adr1 {
    wildcard bins ainc = {4'b11??};// matches any four-bit value where the first two bits are 11. This includes the values 1100, 1101, 1110, and 1111.
    wildcard bins adrb1[ ] = (2'b0x => 2'b1x);//captures transitions from any state starting with 0 (either 00 or 01) to any state starting with 1 (either 10 or 11). This creates separate bins for each of the possible transitions (00=>10, 00=>11, 01=>10, 01=>11).
    wildcard bins adrb2 = (2'b0x => 2'b1x);//captures any transition from a state starting with 0 to a state starting with 1. This uses a single bin for all possible transitions.
  }
endgroup

// Instantiate the covergroup
gc gcInst = new();
```

## ignore_bins

```systemverilog
bit [3:0] adr1;

covergroup gc @(posedge clk);
  ac: coverpoint adr1 {
    ignore_bins igvalues0 = {4, 5}; // Ignore bin to exclude values 4 and 5 from coverage.
    ignore_bins igvalues1 = {[6:$]}; //Ignore bin to exclude the range of values from 6 to 15 from coverage.
  }
endgroup

// Instantiate the covergroup
gc gcInst = new();
```

## Illegal_bins

```systemverilog
bit [3:0] adr1;

covergroup gc @(posedge clk);
  ac: coverpoint adr1 { //automatically create 16 bins, one for each possible value of the 4-bit signal adr1.
    illegal_bins ilvalues0 = {0}; //If adr1 equals 0 during simulation, it will trigger a runtime error.
  }
endgroup

// Instantiate the covergroup
gc gcInst = new();

```

## binsof and intersect

```systemverilog
bit [1:0] a, c;
bit [3:0] b;

covergroup gc @(posedge clk);
  bc: coverpoint b {
    bins bb = {0:12};
    bins cc = {13, 14, 15, 16};
  }

  ic: cross a, bc {//all possible cross production: <a[0], bb>, <a[1], bb>, <a[2], bb>, <a[3], bb>, <a[0], cc>, <a[1], cc>, <a[2], cc>, and <a[3], cc>.
    bins isect_ab = binsof (bc) intersect {[0:1]};//This creates a user-defined cross bin isect_ab that includes only those cross products of (a, bc) where bc intersects with the values 0 or 1(just b has value 0 and 1).Thus, isect_ab includes the cross products: <a[0], bb>, <a[1], bb>, <a[2], bb>, and <a[3], bb>.
    bins isect_nab = ! binsof (bc) intersect {[0:3]};//This creates a user-defined cross bin isect_nab that includes only those cross products of (a, bc) where bc does not intersect with the values 0, 1, 2, or 3.Thus, isect_nab includes the cross products: <a[0], cc>, <a[1], cc>, <a[2], cc>, and <a[3], cc>.
  }
endgroup

// Instantiate the covergroup
gc gcInst = new();

```

## Memory Controller Functional Coverage Example

```systemverilog
typedef enum {READ, WRITE, REFRESH} operation_t;
typedef enum {NORMAL, BURST} mode_t;

covergroup mem_ctrl_cg @(posedge clk);
  option.per_instance = 1;

  // Variables to sample
  operation_t operation;
  mode_t mode;
  bit [7:0] address;
  bit [31:0] data;

  // Coverpoints
  cp_operation: coverpoint operation {
    bins read = {READ};
    bins write = {WRITE};
    bins refresh = {REFRESH};
  }

  cp_mode: coverpoint mode {
    bins normal = {NORMAL};
    bins burst = {BURST};
  }

  cp_address: coverpoint address {
    bins lower_half = {[0:127]};
    bins upper_half = {[128:255]};
  }

  cp_data: coverpoint data {
    bins zero = {32'h00000000};
    bins max = {32'hFFFFFFFF};
    bins mid = {32'h7FFFFFFF, 32'h80000000};
    bins others = default;
  }

  // Cross coverage
  cross_op_mode: cross cp_operation, cp_mode {
    ignore_bins ignored_comb = binsof(cp_operation) intersect {REFRESH} && binsof(cp_mode) intersect {BURST};
  }

  cross_op_addr: cross cp_operation, cp_address;

  cross_op_data: cross cp_operation, cp_data;

endgroup

```

## FFT Algorithm Functional Coverage Example

```systemverilog
typedef enum {SINE_WAVE, SQUARE_WAVE, NOISE} signal_type_t;

covergroup fft_cg @(posedge clk);
  option.per_instance = 1;

  // Variables to sample
  signal_type_t signal_type;
  int signal_length;
  real frequency_bins[0:7];

  // Coverpoints
  cp_signal_type: coverpoint signal_type {
    bins sine_wave = {SINE_WAVE};
    bins square_wave = {SQUARE_WAVE};
    bins noise = {NOISE};
  }

  cp_signal_length: coverpoint signal_length {
    bins small = {[8:32]};
    bins medium = {[33:128]};
    bins large = {[129:1024]};
  }

  cp_frequency_bins: coverpoint frequency_bins[0] {
    bins low_freq = {[0:1.0]};
    bins mid_freq = {[1.0:2.0]};
    bins high_freq = {[2.0:$]};
  }

  // Cross coverage
  cross_signal_type_length: cross cp_signal_type, cp_signal_length;
  cross_signal_type_freq: cross cp_signal_type, cp_frequency_bins;

endgroup

```

## Edge Detection Algorithm Functional Coverage Example

```systemverilog
typedef enum {SIMPLE_SHAPES, NATURAL_SCENES, NOISE} image_type_t;

covergroup edge_detection_cg @(posedge clk);
  option.per_instance = 1;

  // Variables to sample
  image_type_t image_type;
  int image_width;
  int image_height;
  int low_threshold;
  int high_threshold;
  int edge_pixel_count;

  // Coverpoints
  cp_image_type: coverpoint image_type {
    bins simple_shapes = {SIMPLE_SHAPES};
    bins natural_scenes = {NATURAL_SCENES};
    bins noise = {NOISE};
  }

  cp_image_size: coverpoint {image_width, image_height} {
    bins small = binsof(image_width) intersect {[64:128]} && binsof(image_height) intersect {[64:128]};
    bins medium = binsof(image_width) intersect {[129:512]} && binsof(image_height) intersect {[129:512]};
    bins large = binsof(image_width) intersect {[513:1024]} && binsof(image_height) intersect {[513:1024]};
  }

  cp_thresholds: coverpoint {low_threshold, high_threshold} {
    bins low = binsof(low_threshold) intersect {[0:50]} && binsof(high_threshold) intersect {[50:100]};
    bins medium = binsof(low_threshold) intersect {[51:100]} && binsof(high_threshold) intersect {[101:150]};
    bins high = binsof(low_threshold) intersect {[101:150]} && binsof(high_threshold) intersect {[151:200]};
  }

  cp_edge_pixel_count: coverpoint edge_pixel_count {
    bins few_edges = {[0:1000]};
    bins moderate_edges = {[1001:10000]};
    bins many_edges = {[10001:$]};
  }

  // Cross coverage
  cross_type_size: cross cp_image_type, cp_image_size;
  cross_type_thresholds: cross cp_image_type, cp_thresholds;
  cross_thresholds_edges: cross cp_thresholds, cp_edge_pixel_count;

endgroup

```

## Class-Based Functional Coverage

``` systemverilog
class helper;
  // Signal to be used as a sampling trigger
  bit SyncSig;
  // Address signal to be covered
  bit [7:0] address;

  // Constructor to initialize the signals
  function new();
    // Initialize the signals if needed
    SyncSig = 0;
    address = 0;
  endfunction
endclass

```

``` systemverilog
class myclass;
  // Instance of the helper class
  helper m_obj;

  // Define the covergroup within the class
  covergroup Cov @(m_obj.SyncSig);
    // Coverpoint to monitor the address from the helper class
    cp_address: coverpoint m_obj.address {
      // Define bins for different address ranges
      bins addr_bins[] = {[0:63], [64:127], [128:191], [192:255]};
    }
  endgroup

  // Constructor to instantiate the helper class and covergroup
  function new();
    // Instantiate the helper class
    m_obj = new();
    // Instantiate the covergroup
    Cov = new();
  endfunction
endclass

```

``` systemverilog
module tb;
  logic clk;
  // Instance of the main class
  myclass mc;

  // Clock generation: toggles clk every 5 time units
  always #5 clk = ~clk;

  initial begin
    // Initialize the clock
    clk = 0;

    // Instantiate the main class
    mc = new();

    // Stimulus
    repeat (100) begin
      @(posedge clk);
      // Toggle SyncSig to trigger sampling
      mc.m_obj.SyncSig = 1;
      // Assign random values to address
      mc.m_obj.address = $random % 256;
      // Sample the covergroup
      mc.Cov.sample();
      // De-assert SyncSig
      mc.m_obj.SyncSig = 0;
    end

    // Display the coverage results
    $display("Coverage Results:");
    mc.Cov.display_coverage();

    $finish;
  end
endmodule

```