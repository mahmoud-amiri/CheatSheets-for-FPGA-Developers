---
title: TCL CheatSheet
description: The most commonly used TCL commands are given here.
created: 2022-10-01
---

## Table of Contents

- [TCL CheatSheet for FPGA Developers](#tcl-cheatsheet-for-fpga-developers)
  - [General TCL syntax](#general-tcl-syntax)
    - [List](#list)
      - [lappend](#lappend)
      - [lappend](#lappend-1)
      - [concat](#concat)
      - [llength](#llength)
      - [lindex](#lindex)
      - [lrange](#lrange)
      - [linsert](#linsert)
      - [lreplace](#lreplace)
      - [lsearch](#lsearch)
      - [lsort](#lsort)
      - [split](#split)
      - [join](#join)
    - [string](#string)
      - [string match](#string-match)
      - [string equal](#string-equal)
      - [string compare](#string-compare)
      - [string map](#string-map)
      - [string replace](#string-replace)
      - [subst](#subst)
      - [string range](#string-range)
      - [string length](#string-length)
      - [string first](#string-first)
      - [string index](#string-index)
      - [append](#append)
      - [string is](#string-is)
    - [Array](#array)
      - [Setting up an Array](#setting-up-an-array)
      - [array size](#array-size)
      - [array names](#array-names)
      - [array get](#array-get)
      - [array exists](#array-exists)
      - [foreach with array names](#foreach-with-array-names)
      - [parray](#parray)
    - [Dictionary](#dictionary)
      - [dict set](#dict-set)
      - [dict set](#dict-set-1)
      - [dict set](#dict-set-2)
      - [dict set](#dict-set-3)
      - [dict set](#dict-set-4)
      - [dict set](#dict-set-5)
      - [dict set](#dict-set-6)
      - [dict set](#dict-set-7)
      - [dict set](#dict-set-8)
      - [dict set](#dict-set-9)
      - [dict set](#dict-set-10)
      - [dict set](#dict-set-11)
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
      - [run.do](#rundo)

# TCL CheatSheet for FPGA Developers

## General TCL syntax

### List

#### lappend

```tcl
#The lappend command is used to append elements to the end of a list. Each element you append becomes a single new element in the list.
set mylist [list a b c]
lappend mylist d
# Now mylist is "a b c d"
```

---

#### lappend

```tcl
# concat merges one or more lists or values into a single list. If you concatenate lists, set list1 [list a b c]
set list2 [list d e f]
set result [concat $list1 $list2]
# result is "a b c d e f"
```

---

#### concat

```tcl
#The lappend command is used to append elements to the end of a list. Each element you append becomes a single new element in the list.
set mylist [list a b c]
lappend mylist d
# Now mylist is "a b c d"
```

---

#### llength

```tcl
#This command returns the number of elements in a list.
set mylist [list a b c d e]
puts [llength $mylist]
# Output: 5
```

---

#### lindex

```tcl
#lindex is used to retrieve an element from a list based on its index. TCL lists are zero-indexed.
set mylist [list a b c d e]
puts [lindex $mylist 2]
# Output: c
```

---

#### lrange

```tcl
#This command returns a range of elements from a list, specified by start and end indexes.
set mylist [list a b c d e]
puts [lrange $mylist 1 3]
# Output: b c d
```

---

#### linsert

```tcl
#linsert inserts elements at a specified position in the list.
set mylist [list a b c d]
set mylist [linsert $mylist 2 x y z]
# mylist is now "a b x y z c d"
```

---

#### lreplace

```tcl
#This command replaces a range of elements in a list with new elements.

set mylist [list a b c d e]
set mylist [lreplace $mylist 1 3 x y]
# mylist becomes "a x y e"
```

---

#### lsearch

```tcl
#lsearch searches for an element in the list that matches a pattern and returns its index.

set mylist [list apple banana grapefruit banana]
puts [lsearch -exact $mylist banana]
# Output: 1 (index of the first "banana")
```

---

#### lsort

```tcl
#lsort sorts a list according to various sorting options like numeric or dictionary order.

set mylist [list 10 2 30]
puts [lsort -integer $mylist]
# Output: 2 10 30
```

---

#### split

```tcl
#Converts a string into a list, optionally splitting by specified delimiters.

set mystring "a-b-c"
puts [split $mystring "-"]
# Output: a b c
```

---

#### join

```tcl
#Converts a list into a string, optionally joining with a specified delimiter.

set mylist [list a b c]
puts [join $mylist "-"]
# Output: a-b-c
```

---

### string 

#### string match

```tcl
#Checks if a pattern matches a string. Returns 1 if true, 0 if false.
puts [string match "*lo" "Hello"]  # Output: 1

```

---

#### string equal

```tcl
#Compares two strings for exact equality. Returns 1 if equal, 0 otherwise.
puts [string equal -nocase "hello" "HELLO"]  # Output: 1

```

---

#### string compare

```tcl
#Lexicographically compares two strings. Returns -1, 0, or 1.
puts [string compare "abc" "abd"]  # Output: -1

```

---

#### string map

```tcl
#Maps substrings of a string to new substrings.
puts [string map {"H" "000"} "Hello"]  # Output: 000ello

```

---

#### string replace

```tcl
#Replaces part of a string with another string.
puts [string replace "Hello" 1 3 "a"]  # Output: Ha

```

---

#### subst

```tcl
#Performs backslash, command, and variable substitutions.
set a 44
puts [subst "xyz {$a}"]  # Output: xyz {44}

```

---

#### string range

```tcl
#Returns a substring based on start and end indexes.
puts [string range "Hello, World" 7 11]  # Output: World

```

---


#### string length

```tcl
#Returns the number of characters in a string.
puts [string length "Hello"]  # Output: 5

```

---

#### string first

```tcl
#Finds the first occurrence of a substring.
puts [string first "e" "Hello"]  # Output: 1

```

---

#### string index

```tcl
#Returns the character at a specific index.
puts [string index "Hello" 4]  # Output: o

```

---

#### append

```tcl
#Appends one or more values to a variable.
set str "Hello"
append str ", World"
puts $str  # Output: Hello, World

```

---

#### string is

```tcl
#Checks if the entire string conforms to a certain type.Checks if the entire string conforms to a certain type.
puts [string is integer "1234"]  # Output: 1

```

---

### Array 

#### Setting up an Array

```tcl
#!
array set array1 [list {123} {Abigail Aardvark} {234} {Bob Baboon} {345} {Cathy Coyote} {456} {Daniel Dog}]


```

---

#### array size

```tcl
#Returns the number of elements (key-value pairs) in the array.
puts [array size array1]  # Output: 4


```

---

#### array names

```tcl
#Returns a list of all keys in the array, optionally matching a pattern.
puts [array names array1]  # Outputs all keys in array1

```

---

#### array get

```tcl
#Returns a list where each odd member is a key and the even member is its corresponding value.
puts [array get array1]
# Output might look like: 123 Abigail Aardvark 234 Bob Baboon 345 Cathy Coyote 456 Daniel Dog


```

---

#### array exists

```tcl
#Checks if an array with the given name exists. Returns 1 if true, otherwise 0.
puts [array exists array1]  # Output: 1

```

---

#### foreach with array names

```tcl
#Iterates over each key of the array, and you can access values inside the loop.
foreach key [array names array1] {
   puts "Key is $key and value is $array1($key)"
}


```

---

#### parray

```tcl
#Prints the contents of an array in a readable form.
parray array1


```

---

### Dictionary 

#### dict set

```tcl
#Creates or modifies entries in a dictionary.
dict set myDict key1 "value1"
dict set myDict key1 nestedKey1 "value2"
puts $myDict
```

---

#### dict set

```tcl
#Creates or modifies entries in a dictionary.
dict set myDict key1 "value1"
dict set myDict key1 nestedKey1 "value2"
puts $myDict
```

---

#### dict set

```tcl
#Creates or modifies entries in a dictionary.
dict set myDict key1 "value1"
dict set myDict key1 nestedKey1 "value2"
puts $myDict
```

---

#### dict set

```tcl
#Creates or modifies entries in a dictionary.
dict set myDict key1 "value1"
dict set myDict key1 nestedKey1 "value2"
puts $myDict
```

---

#### dict set

```tcl
#Creates or modifies entries in a dictionary.
dict set myDict key1 "value1"
dict set myDict key1 nestedKey1 "value2"
puts $myDict
```

---

#### dict set

```tcl
#Creates or modifies entries in a dictionary.
dict set myDict key1 "value1"
dict set myDict key1 nestedKey1 "value2"
puts $myDict
```

---

#### dict set

```tcl
#Creates or modifies entries in a dictionary.
dict set myDict key1 "value1"
dict set myDict key1 nestedKey1 "value2"
puts $myDict
```

---

#### dict set

```tcl
#Creates or modifies entries in a dictionary.
dict set myDict key1 "value1"
dict set myDict key1 nestedKey1 "value2"
puts $myDict
```

---

#### dict set

```tcl
#Creates or modifies entries in a dictionary.
dict set myDict key1 "value1"
dict set myDict key1 nestedKey1 "value2"
puts $myDict
```

---

#### dict set

```tcl
#Creates or modifies entries in a dictionary.
dict set myDict key1 "value1"
dict set myDict key1 nestedKey1 "value2"
puts $myDict
```

---

#### dict set

```tcl
#Creates or modifies entries in a dictionary.
dict set myDict key1 "value1"
dict set myDict key1 nestedKey1 "value2"
puts $myDict
```

---

#### dict set

```tcl
#Creates or modifies entries in a dictionary.
dict set myDict key1 "value1"
dict set myDict key1 nestedKey1 "value2"
puts $myDict
```

---

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

#### run.do

```tcl
if [file exists "work"] {vdel -all}
vlib work

vcom -f dut.f

vlog -f tb.f

vopt top -o top_optimized  +acc +cover=sbfec+dut_top

#Test 1
vsim top_optimized -coverage +UVM_TESTNAME=<test1-name>  #CHANGE_ME
set NoQuitOnFinish 1
onbreak {resume}
log /* -r
run -all
coverage exclude -src <file-addr>/<file-name>.vhd -line <n> -code s #CHANGE_ME
coverage attribute -name TESTNAME -value <test1-name> #CHANGE_ME
coverage save <test1-name>.ucdb #CHANGE_ME

#Test 2
vsim top_optimized -coverage +UVM_TESTNAME=<test2-name>  #CHANGE_ME
set NoQuitOnFinish 1
onbreak {resume}
log /* -r
run -all
coverage exclude -src <file-addr>/<file-name>.vhd -line <n> -code s #CHANGE_ME
coverage attribute -name TESTNAME -value <test2-name> #CHANGE_ME
coverage save <test2-name>.ucdb #CHANGE_ME


vcover merge  <merged_tests_name>.ucdb <test1-name>.ucdb <test2-name>.ucdb #CHANGE_ME
vcover report <merged_tests_name>.ucdb -cvg -details| #CHANGE_ME

quit
```

**[🔼Back to Top](#table-of-contents)**
