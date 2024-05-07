---
title: TCL CheatSheet
description: The most commonly used TCL commands are given here.
created: 2022-10-01
---

## Table of Contents

- [TCL CheatSheet for FPGA Developers](#tcl-cheatsheet-for-fpga-developers)
  - [Questasim TCL](#questasim-tcl)
    - [syntax](#syntax)
      - [vdel](#vdel)
      - [vlib](#vlib)
      - [vcom](#vcom)
      - [vlog](#vlog)
      - [vopt](#vopt)
      - [vsim](#vsim)
      - [onbreak](#onbreak)
      - [log](#log)
      - [run](#run)
      - [coverage exclude](#coverage-exclude)
      - [coverage attribute](#coverage-attribute)
      - [coverage save](#coverage-save)
      - [vcover merge](#vcover-merge)
      - [vcover report](#vcover-report)
      - [quit](#quit)
    - [example](#example)
      - [dut.f](#dutf)
      - [tb.f](#tbf)
      - [wave.do](#wavedo)

# TCL CheatSheet for FPGA Developers

## Questasim TCL

### syntax

#### vdel

This command deletes a design unit from a specified library. 

**Ex:** Checks if a working library (folder) named "work" exists. If it does, it deletes all items within it using the vdel command with the -all option. This is typically used to clear any previous compilation or simulation artifacts.

```tcl
if [file exists "work"] {vdel -all}
```

---

#### vlib

This command creates a design library.

**Ex:** Creates a new library directory named "work". This is essential for storing compiled simulation models.

```tcl
vlib work
```

---

#### vcom

Commands The vcom command compiles VHDL source code into a specified working library (or to the work library by default).

**Ex:** Compiles all VHDL files listed in the file dut.f into the library. The -f parameter specifies a file that contains a list of design unit files to compile.

```tcl
vcom -f dut.f
```

---

#### vlog

The vlog command compiles Verilog source code and SystemVerilog extensions into a specified working library (or to the work library by default).

**Ex:** Compiles all SystemVerilog files listed in the file tb.f. This file likely includes testbench files necessary for simulating the Device Under Test (DUT).

```tcl
vlog -f tb.f
```

---

#### vopt

**Ex:** Optimizes the simulation model named "top" for faster simulation and better performance. The optimized model is named "top_optimized". Flags +acc and +cover enable additional simulation features like access to internals and coverage collection respectively.
+acc: This option enables full visibility of your design. This means that the simulator will be able to access all signals, variables, and other design elements during simulation.
+cover=sbfec : is used to enable coverage for the dut_top design unit during the optimization process

```tcl
vopt top -o top_optimized  +acc +cover=sbfec+dut_top.
```

---

#### vsim

The vsim command invokes the VSIM simulator, which you can use to view the results of a previous simulation run (when invoked with the -view switch)

**Ex:** Launches the simulator using the optimized model "top_optimized". It runs with coverage analysis enabled and specifies the UVM test named <test-name> .

```tcl
vsim top_optimized -coverage +UVM_TESTNAME=<test-name> 
```

---

**Ex:** Configures the simulation environment so that it does not automatically close upon completing the simulation.

```tcl
set NoQuitOnFinish 1
```

---

#### onbreak

This command is used within a DO file and specifies one or more scripts to be executed when running a script that encounters a breakpoint in the source code. 

**Ex:**  Resume execution of the DO file on encountering a breakpoint.

```tcl
onbreak {resume}
```

---

#### log

This command creates a wave log format (WLF) file containing simulation data for all HDL objects whose names match the provided specifications.

**Ex:** Starts logging all simulation messages. The -r log all objects in the design.

```tcl
log /* -r
```

---

#### run

This command advances the simulation by the specified number of timesteps.

**Ex:** Starts the simulation and runs it until all activity is completed. Causes the simulator to run the current simulation forever, or until it hits a 
breakpoint or specified break event.

```tcl
run -all
```

---

#### coverage exclude

**Ex:** Excludes specific lines and types of coverage (in this case, statement coverage denoted by 's') for the specified file and line during coverage analysis.

```tcl
coverage exclude -src <file-name>.vhd -line <line-number> -code s 
```

---

#### coverage attribute

**Ex:** Sets a coverage attribute, labeling the coverage data with the test name <test-name>.

```tcl
coverage attribute -name TESTNAME -value <test-name> 
```

---

#### coverage save

**Ex:** Saves the coverage data to a file named <test-name>.ucdb".

```tcl
coverage save <test-name>.ucdb 
```

---

#### vcover merge

**Ex:** Merges several UCDB (Unified Coverage Database) files into a single UCDB file named <merged-file>.ucdb". This is typically done to consolidate coverage data from multiple test runs. 

```tcl
vcover merge  <merged-file>.ucdb <test1>.ucdb <test2>.ucdb <test3>.ucdb
```

---

#### vcover report

**Ex:** Generates a detailed coverage report from the merged UCDB file, showing detailed statistics for analysis.

```tcl
vcover report <merged-file>.ucdb -cvg -details|
```

---

#### quit

**Ex:** Exits the simulation tool.

```tcl
quit
```

### example

#### dut.f 

```tcl
<file1>.vhd
<file2>.vhd
<file3>.vhd
```

---

#### tb.f

+incdir is a common command line argument used to specify include directories to the simulator.
-suppress is used to suppress specific warnings or errors during simulation or compilation. 

```tcl
<file1>.sv
<file2>.sv
<file3>.sv
+incdir+<tb_classes>
-suppress 2286
```

---

#### wave.do

```tcl
onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /top/clk
add wave -noupdate -radix hexadecimal /top/DUT/A
add wave -noupdate -radix hexadecimal /top/DUT/B
add wave -noupdate -radix hexadecimal /top/DUT/clk
add wave -noupdate -radix hexadecimal /top/op_set
add wave -noupdate -radix hexadecimal /top/DUT/op
add wave -noupdate -radix hexadecimal /top/DUT/reset_n
add wave -noupdate -radix hexadecimal /top/DUT/start
add wave -noupdate -radix hexadecimal /top/DUT/done
add wave -noupdate -radix hexadecimal /top/DUT/result
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {50316229 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 0
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {0 ns} {212795720 ns}
```

```tcl
if [file exists "work"] {vdel -all}
vlib work

# Comment out either the SystemVerilog or VHDL DUT.
# There can be only one!

#VHDL DUT
vcom -f dut.f

# SystemVerilog DUT
# vlog ../misc/tinyalu.sv

vlog -f tb.f
vopt top -o top_optimized  +acc +cover=sbfec+dut_top

vsim top_optimized -coverage +UVM_TESTNAME=fibonacci_test
set NoQuitOnFinish 1
onbreak {resume}
log /* -r
run -all
coverage exclude -src tinyalu_dut/single_cycle_add_and_xor.vhd -line 49 -code s
coverage exclude -src tinyalu_dut/single_cycle_add_and_xor.vhd -scope /top/DUT/add_and_xor -line 49 -code b
coverage attribute -name TESTNAME -value fibonacci_test
coverage save fibonacci_test.ucdb

vsim top_optimized -coverage +UVM_TESTNAME=parallel_test 
set NoQuitOnFinish 1
onbreak {resume}
log /* -r
run -all
coverage exclude -src tinyalu_dut/single_cycle_add_and_xor.vhd -line 49 -code s
coverage exclude -src tinyalu_dut/single_cycle_add_and_xor.vhd -scope /top/DUT/add_and_xor -line 49 -code b
coverage attribute -name TESTNAME -value parallel_test
coverage save parallel_test.ucdb

vsim top_optimized -coverage +UVM_TESTNAME=full_test
set NoQuitOnFinish 1
onbreak {resume}
log /* -r
run -all
coverage exclude -src tinyalu_dut/single_cycle_add_and_xor.vhd -line 49 -code s
coverage exclude -src tinyalu_dut/single_cycle_add_and_xor.vhd -scope /top/DUT/add_and_xor -line 49 -code b
coverage attribute -name TESTNAME -value full_test
coverage save full_test.ucdb

vcover merge  tinyalu.ucdb fibonacci_test.ucdb parallel_test.ucdb full_test.ucdb
vcover report tinyalu.ucdb -cvg -details|

quit
```

**[🔼Back to Top](#table-of-contents)**
