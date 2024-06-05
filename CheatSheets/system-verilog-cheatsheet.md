---
title: CheatSheet-Name CheatSheet
description: The most commonly used CheatSheet-Name commands/keyboard-shortcuts/concepts/tags/properties/attributes are given here.
created: 2022-10-01
---

## Table of Contents

- [CheatSheet-Name CheatSheet for Developers](#cheatsheet-name-cheatsheet-for-developers)
  - [constraints](#constraints)
    - [Weighted Distributions](#weighted-distributions)
    - [inside](#inside)
    - [Implication](#implication)
    - [foreach](#foreach)
    - [solve before](#solve-before)
    - [Memory Block](#memory-block)
    - [Bus Protocol Constraints](#bus-protocol-constraints)
    - [soft](#soft)
    - [Disable](#disable)
    - [randcase](#randcase)

# CheatSheet-Name CheatSheet for Developers

## constraints

### Weighted Distributions

```systemverilog
  // Weighted distribution using := operator
  //Each value in the range from 1 to 5 has a weight of 50. This means values 1, 2, 3, 4, and 5 each have a weight of 50.
  constraint dist1 { 
      typ dist { 0:=20, [1:5]:=50, 6:=40, 7:=10 }; 
  }

  // Weighted distribution using :/ operator
  //The range 1 to 5 has a total proportional weight of 50, which will be equally divided among the values 1, 2, 3, 4, and 5. Therefore, each of these values gets a weight of 10 (since 50 / 5 = 10).
  constraint dist2 { 
      typ dist { 0:/20, [1:5]:/50, 6:/10, 7:/20 }; 
  }
```

### inside

```systemverilog
  //Simple Integer Constraint
  constraint c_value {
    value inside {[1, 2, 4, 8, 16]};
  }

  //Range of Values
  constraint c_value {
    value inside { [10:20] };
  }

  //Mixed Sets and Ranges
  constraint c_value {
    value inside { [1, 3, 5, 7, 9], [20:30] };
  }

  //Constraining Strings
  rand string color;
  constraint c_color {
    color inside { "red", "green", "blue", "yellow" };
  }

  //Array Constraints
  constraint c_data {
    foreach (data[i]) data[i] inside {8'h00, 8'hFF};
  }

  // Constraint to exclude values between 3 and 6
  constraint inv_range { 
      ! (typ inside {[3:6]}); 
  }
```

### Implication

```systemverilog
  //Basic Implication:if a is greater than 0, then b must be one of the values in the set {1, 2, 3, 4, 5}.
  constraint c_implication {
    a > 0 -> b inside {[1, 2, 3, 4, 5]};
  }

  //Nested Implication:if x is 1, then if y is 2, z must be 3
  constraint c_nested_implication {
    x == 1 -> (y == 2 -> z == 3);
  }

  //Using Implication with Ranges:if a is one of the values in the set {1, 2, 3}, then b must be within the range [10:20].
  constraint c_range_implication {
    a inside {1, 2, 3} -> b inside {[10:20]};
  }
  //Implication with Multiple Conditions:if a is greater than 5 and b is less than 10, then c must be an even number.
  constraint c_multi_condition_implication {
    (a > 5 && b < 10) -> c % 2 == 0;
  }

  //Implication with Arrays:if the first element of the array array[0] is 1, then the second element array[1] must be 2.
  constraint c_array_implication {
    array[0] == 1 -> array[1] == 2;
  }
```

### foreach

```systemverilog
  //Simple Foreach Constraint:each element of the data array is constrained to be either 8'h00 or 8'hFF.
  constraint c_data {
    foreach (data[i]) data[i] inside {8'h00, 8'hFF};
  }

  //Applying a Range Constraint:each element of the values array is constrained to be within the range [0:100].
  constraint c_values {
    foreach (values[i]) values[i] inside { [0:100] };
  }

  //Relationship Between Array Elements:each element of the values array is constrained to be greater than the previous element, ensuring that the array is sorted in ascending order.
  constraint c_values {
    foreach (values[i]) {
      if (i > 0) {
        values[i] > values[i-1];
      }
    }
  }

  //Nested Foreach for Multi-dimensional Arrays:each element of the 2-dimensional matrix array is constrained to be within the range [1:10]
  constraint c_matrix {
    foreach (matrix[i, j]) matrix[i][j] inside { [1:10] };
  }
```

### solve before

```systemverilog
  //Basic solve before Constraint
  rand int a, b;
  constraint c_solve {
      solve a before b;
  }
  constraint c_a {
      a inside {1, 2, 3};
  }
  constraint c_b {
      b == a + 1;
  }

  //Conditional solve before
  rand int x, y, z;
  constraint c_solve {
      if (x < 10) solve x before y;
      else solve y before x;
      solve x before z;
      solve y before z;
  }
  constraint c_x {
      x inside {5, 15};
  }
  constraint c_y {
      y inside {10, 20};
  }
  constraint c_z {
      z == x + y;
  }
```

### Memory Block

```systemverilog
  //Memory Block Randomization
  bit [31:0] m_ram_start;
  bit [31:0] m_ram_end;
  rand bit [31:0] m_start_addr;
  rand bit [31:0] m_end_addr;
  rand int m_block_size;

  constraint c_addr {
    m_start_addr >= m_ram_start;
    m_start_addr < m_ram_end;
    m_start_addr % 4 == 0;
    m_end_addr == m_start_addr + m_block_size - 1;
  }

  constraint c_blk_size {
    m_block_size inside {64, 128, 512};
  }
```

```systemverilog
  //Equal Partitions of Memory
  bit [31:0] m_ram_start;
  bit [31:0] m_ram_end;
  rand int m_num_part;
  rand bit [31:0] m_part_start [];
  rand int m_part_size;

  constraint c_parts {
    m_num_part > 4;
    m_num_part <= 10;
  }

  constraint c_size {
    m_part_size == (m_ram_end - m_ram_start + 1) / m_num_part;
  }

  constraint c_part {
    m_part_start.size() == m_num_part;
    foreach (m_part_start[i]) {
      if (i == 0) {
        m_part_start[i] == m_ram_start;
      } else {
        m_part_start[i] == m_part_start[i-1] + m_part_size;
      }
    }
  }
```

```systemverilog
  //Variable Memory Partitions
  bit [31:0] m_ram_start;
  bit [31:0] m_ram_end;
  rand int m_num_part;
  rand bit [31:0] m_part_start [];
  rand int m_part_size [];

  constraint c_parts {
    m_num_part > 4;
    m_num_part <= 10;
  }

  constraint c_size {
    m_part_size.size() == m_num_part;
    m_part_size.sum() == m_ram_end - m_ram_start + 1;
    foreach (m_part_size[i]) m_part_size[i] inside {64, 128, 256, 512};
  }

  constraint c_part {
    m_part_start.size() == m_num_part;
    foreach (m_part_start[i]) {
      if (i == 0) {
        m_part_start[i] == m_ram_start;
      } else {
        m_part_start[i] == m_part_start[i-1] + m_part_size[i-1];
      }
    }
  }
```

```systemverilog
  //Variable Memory Partitions with Space in Between
  bit [31:0] m_ram_start;
  bit [31:0] m_ram_end;
  rand int m_num_part;
  rand bit [31:0] m_part_start [];
  rand int m_part_size [];
  rand int m_space [];

  constraint c_parts {
    m_num_part > 4;
    m_num_part <= 10;
  }

  constraint c_size {
    m_part_size.size() == m_num_part;
    m_space.size() == m_num_part - 1;
    m_part_size.sum() + m_space.sum() == m_ram_end - m_ram_start + 1;
    foreach (m_part_size[i]) m_part_size[i] inside {64, 128, 256, 512};
    foreach (m_space[i]) m_space[i] inside {0, 16, 32};
  }

  constraint c_part {
    m_part_start.size() == m_num_part;
    foreach (m_part_start[i]) {
      if (i == 0) {
        m_part_start[i] == m_ram_start;
      } else {
        m_part_start[i] == m_part_start[i-1] + m_part_size[i-1] + m_space[i-1];
      }
    }
  }

```

```systemverilog
  //Partition for Programs and Data
  rand int num_pgm;
  rand int num_data;
  rand int num_space;
  rand int max_pgm_size;
  rand int max_data_size;
  rand int pgm_size [];
  rand int data_size [];
  rand int space_size [];
  const int total_ram = 6 * 1024; // Assume total 6KB RAM

  constraint c_num_size {
    max_pgm_size == 512;
    max_data_size == 128;
  }

  constraint c_num {
    num_pgm inside {[1:10]};
    num_data inside {[1:50]};
    num_space inside {[1:50]};
  }

  constraint c_size {
    pgm_size.size() == num_pgm;
    data_size.size() == num_data;
    space_size.size() == num_space;
  }

  constraint c_ram {
    foreach (pgm_size[i]) {
      pgm_size[i] dist {[128:512] :/ 1};
      pgm_size[i] % 4 == 0;
    }
    foreach (data_size[i]) {
      data_size[i] inside {64, 128};
    }
    foreach (space_size[i]) {
      space_size[i] inside {4, 8, 16, 32};
    }
    total_ram == pgm_size.sum() + data_size.sum() + space_size.sum();
  }
```

### Bus Protocol Constraints

```systemverilog
  //AXI Stream Protocol Constraint
  rand bit [31:0] tdata;    // Data
  rand bit [3:0] tkeep;     // Byte Qualifier
  rand bit tvalid;          // Data is valid
  rand bit tready;          // Slave ready to accept data
  rand bit tlast;           // End of frame

  constraint c_axi_stream {
    // Ensure valid transactions only occur when both tvalid and tready are high
    tvalid == 1'b1 -> tready == 1'b1;

    // tlast should be high only for the last transaction in a frame
    tlast inside {0, 1};

    // tkeep specifies which bytes of tdata are valid
    tkeep inside {4'b0001, 4'b0011, 4'b0111, 4'b1111};

    // tdata should only be valid when tvalid is high
    tvalid -> tdata inside {32'h0000_0000, 32'hFFFF_FFFF, 32'hA5A5_A5A5, 32'h5A5A_5A5A};
  }
```

```systemverilog
  //AXI Lite Protocol Constraint
  rand bit [31:0] awaddr;   // Write address
  rand bit awvalid;         // Write address valid
  rand bit awready;         // Write address ready
  rand bit [31:0] wdata;    // Write data
  rand bit [3:0] wstrb;     // Write strobes
  rand bit wvalid;          // Write valid
  rand bit wready;          // Write ready
  rand bit [1:0] bresp;     // Write response
  rand bit bvalid;          // Write response valid
  rand bit bready;          // Write response ready

  rand bit [31:0] araddr;   // Read address
  rand bit arvalid;         // Read address valid
  rand bit arready;         // Read address ready
  rand bit [31:0] rdata;    // Read data
  rand bit [1:0] rresp;     // Read response
  rand bit rvalid;          // Read valid
  rand bit rready;          // Read ready

  constraint c_axi_lite {
    // Write address handshake
    awvalid == 1'b1 -> awready == 1'b1;

    // Write data handshake
    wvalid == 1'b1 -> wready == 1'b1;

    // Write response handshake
    bvalid == 1'b1 -> bready == 1'b1;

    // Read address handshake
    arvalid == 1'b1 -> arready == 1'b1;

    // Read data handshake
    rvalid == 1'b1 -> rready == 1'b1;

    // Write data strobe must be valid
    wstrb inside {4'b0001, 4'b0011, 4'b0111, 4'b1111};

    // Write response must be OKAY or SLVERR
    bresp inside {2'b00, 2'b10};

    // Read response must be OKAY or SLVERR
    rresp inside {2'b00, 2'b10};
  }
  ```

  ```systemverilog
  //AXI Stream Video Pattern Generation
  rand bit [31:0] tdata;    // Data
  rand bit [3:0] tkeep;     // Byte Qualifier
  rand bit tvalid;          // Data is valid
  rand bit tready;          // Slave ready to accept data
  rand bit tlast;           // End of frame line
  
  const int WIDTH = 1920;   // Video frame width
  const int HEIGHT = 1080;  // Video frame height
  int pixel_count;
  int line_count;

  constraint c_axi_stream {
    tvalid == 1'b1 -> tready == 1'b1;
    
    tkeep == 4'b1111; // Assuming we are always sending full data beats
    
    // Generate valid video data
    tdata inside {32'h0000_0000, 32'hFFFFFFFF, 32'hAAAA_AAAA, 32'h5555_5555, 32'h1234_5678};
    
    // tlast is asserted at the end of each line
    tlast == (pixel_count == WIDTH - 1);
    
    // tvalid is high for the entire frame
    tvalid == 1'b1;
    
    // tready should be high for the entire frame
    tready == 1'b1;
  }
  ```

### soft

```systemverilog
    // Hard constraints
    constraint c_hard {
        a inside {1, 100};
        b inside {1, 100};
    }

    // Soft constraint: prefer a + b to be less than 50
    soft constraint c_soft {
        a + b < 50;
    }
```

### Disable

```systemverilog
  class DisableExample;
    rand int a, b;

    // Constraint to ensure a is between 1 and 10
    constraint c_a {
      a inside {1, 10};
    }

    // Constraint to ensure b is between 20 and 30
    constraint c_b {
      b inside {20, 30};
    }
  endclass

  module test;
    initial begin
      DisableExample example = new();

      // Disable constraint c_b and randomize
      example.c_b.constraint_mode(0);

      // Re-enable constraint c_b and randomize
      example.c_b.constraint_mode(1);

    end
  endmodule
```

```systemverilog
class DisableRandomizationExample;
  rand int a;
  rand int b;

  // Constraint to ensure a and b are within certain ranges
  constraint c_range {
    a inside {1, 10};
    b inside {20, 30};
  }
endclass

module test;
  initial begin
    DisableRandomizationExample example = new();
    
    // Disable randomization of variable b
    example.b.rand_mode(0);
    
    // Re-enable randomization of variable b
    example.b.rand_mode(1);
  end
endmodule
```

### randcase

```systemverilog
  module randcase_example;
    initial begin
      // Use randcase to select a value based on weights
      int selected_value;
      randcase
        30: selected_value = 1;  // 30% probability
        50: selected_value = 2;  // 50% probability
        20: selected_value = 3;  // 20% probability
      endcase
      
      $display("Selected value: %0d", selected_value);
    end
  endmodule
```
