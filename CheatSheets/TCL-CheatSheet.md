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
      - [dict create](#dict-create)
      - [dict unset](#dict-unset)
      - [dict replace](#dict-replace)
      - [dict keys and dict values](#dict-keys-and-dict-values)
      - [dict get](#dict-get)
      - [dict for](#dict-for)
      - [foreach with dict keys](#foreach-with-dict-keys)
      - [dict append and dict lappend](#dict-append-and-dict-lappend)
      - [dict exists](#dict-exists)
      - [dict merge](#dict-merge)
      - [dict remove](#dict-remove)
      - [dict size](#dict-size)
    - [Looping](#looping)
      - [while](#while)
      - [for](#for)
      - [foreach](#foreach)
    - [conditional statements](#conditional-statements)
      - [if](#if)
      - [switch](#switch)
    - [Proc](#proc)
      - [Proc with Optional Arguments](#proc-with-optional-arguments)
      - [Proc with Variable Number of Arguments](#proc-with-variable-number-of-arguments)
      - [Returning Values](#returning-values)
      - [Local Variables](#local-variables)
      - [Error Handling in Procs](#error-handling-in-procs)
    - [Files](#files)
      - [Opening and Closing Files](#opening-and-closing-files)
      - [Reading Files](#reading-files)
      - [Error Handling in File Operations](#error-handling-in-file-operations)
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
    - [verification example](#verification-example)
      - [dut.f](#dutf)
      - [tb.f](#tbf)
      - [test\_config.tcl](#test_configtcl)
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

#### lappend

```tcl
# concat merges one or more lists or values into a single list. If you concatenate lists, set list1 [list a b c]
set list2 [list d e f]
set result [concat $list1 $list2]
# result is "a b c d e f"
```

#### concat

```tcl
#The lappend command is used to append elements to the end of a list. Each element you append becomes a single new element in the list.
set mylist [list a b c]
lappend mylist d
# Now mylist is "a b c d"
```

#### llength

```tcl
#This command returns the number of elements in a list.
set mylist [list a b c d e]
puts [llength $mylist]
# Output: 5
```

#### lindex

```tcl
#lindex is used to retrieve an element from a list based on its index. TCL lists are zero-indexed.
set mylist [list a b c d e]
puts [lindex $mylist 2]
# Output: c
```

#### lrange

```tcl
#This command returns a range of elements from a list, specified by start and end indexes.
set mylist [list a b c d e]
puts [lrange $mylist 1 3]
# Output: b c d
```

#### linsert

```tcl
#linsert inserts elements at a specified position in the list.
set mylist [list a b c d]
set mylist [linsert $mylist 2 x y z]
# mylist is now "a b x y z c d"
```

#### lreplace

```tcl
#This command replaces a range of elements in a list with new elements.

set mylist [list a b c d e]
set mylist [lreplace $mylist 1 3 x y]
# mylist becomes "a x y e"
```

#### lsearch

```tcl
#lsearch searches for an element in the list that matches a pattern and returns its index.

set mylist [list apple banana grapefruit banana]
puts [lsearch -exact $mylist banana]
# Output: 1 (index of the first "banana")
```

#### lsort

```tcl
#lsort sorts a list according to various sorting options like numeric or dictionary order.

set mylist [list 10 2 30]
puts [lsort -integer $mylist]
# Output: 2 10 30
```

#### split

```tcl
#Converts a string into a list, optionally splitting by specified delimiters.

set mystring "a-b-c"
puts [split $mystring "-"]
# Output: a b c
```

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

#### string equal

```tcl
#Compares two strings for exact equality. Returns 1 if equal, 0 otherwise.
puts [string equal -nocase "hello" "HELLO"]  # Output: 1

```

#### string compare

```tcl
#Lexicographically compares two strings. Returns -1, 0, or 1.
puts [string compare "abc" "abd"]  # Output: -1

```

#### string map

```tcl
#Maps substrings of a string to new substrings.
puts [string map {"H" "000"} "Hello"]  # Output: 000ello

```

#### string replace

```tcl
#Replaces part of a string with another string.
puts [string replace "Hello" 1 3 "a"]  # Output: Ha

```

#### subst

```tcl
#Performs backslash, command, and variable substitutions.
set a 44
puts [subst "xyz {$a}"]  # Output: xyz {44}

```

#### string range

```tcl
#Returns a substring based on start and end indexes.
puts [string range "Hello, World" 7 11]  # Output: World

```

#### string length

```tcl
#Returns the number of characters in a string.
puts [string length "Hello"]  # Output: 5

```

#### string first

```tcl
#Finds the first occurrence of a substring.
puts [string first "e" "Hello"]  # Output: 1

```

#### string index

```tcl
#Returns the character at a specific index.
puts [string index "Hello" 4]  # Output: o

```

#### append

```tcl
#Appends one or more values to a variable.
set str "Hello"
append str ", World"
puts $str  # Output: Hello, World

```

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

#### array size

```tcl
#Returns the number of elements (key-value pairs) in the array.
puts [array size array1]  # Output: 4


```

#### array names

```tcl
#Returns a list of all keys in the array, optionally matching a pattern.
puts [array names array1]  # Outputs all keys in array1

```

#### array get

```tcl
#Returns a list where each odd member is a key and the even member is its corresponding value.
puts [array get array1]
# Output might look like: 123 Abigail Aardvark 234 Bob Baboon 345 Cathy Coyote 456 Daniel Dog


```

#### array exists

```tcl
#Checks if an array with the given name exists. Returns 1 if true, otherwise 0.
puts [array exists array1]  # Output: 1

```

#### foreach with array names

```tcl
#Iterates over each key of the array, and you can access values inside the loop.
foreach key [array names array1] {
   puts "Key is $key and value is $array1($key)"
}


```

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

#### dict create

```tcl
#Creates a new dictionary with specified key-value pairs.
set myDict [dict create 1 "SK" 2 "KK" 3 "ZK"]
```

#### dict unset

```tcl
#Removes a key (and its corresponding value) from a dictionary.
dict unset myDict key1
```

#### dict replace

```tcl
#Replaces the value for a given key in the dictionary.
dict replace myDict key1 "new value"
```

#### dict keys and dict values

```tcl
#These commands list all keys or values in the dictionary.
puts [dict keys myDict]
puts [dict values myDict]
```

#### dict get

```tcl
#Retrieves the value for a specific key or the entire dictionary as a list.
puts [dict get myDict key1]
puts [dict get myDict]
```

#### dict for

```tcl
#Iterates over each key-value pair in the dictionary.
dict for {key value} $myDict {
    puts "Key: $key Value: $value"
}
```

#### foreach with dict keys

```tcl
#Another way to iterate using the keys.
foreach key [dict keys $myDict] {
    puts "Key: $key Value: [dict get $myDict $key]"
}
```

#### dict append and dict lappend

```tcl
#These commands append values to an existing key, where dict lappend treats all added elements as a single list item under the key.
dict append myDict 4 "LA"
dict lappend myDict 4 "SF" "PO"
```

#### dict exists

```tcl
#Checks if a key exists in the dictionary.
puts [dict exists $myDict key1]
```

#### dict merge

```tcl
#Merges two dictionaries into one.
set dict1 [dict create a 1 b 2]
set dict2 [dict create c 3 d 4]
set merged [dict merge $dict1 $dict2]
```

#### dict remove

```tcl
#Removes one or more keys from the dictionary.
set newDict [dict remove $myDict key1 key2]
```

#### dict size

```tcl
#Returns the number of key-value pairs in the dictionary.
puts [dict size $myDict]
```

---

### Looping

#### while

```tcl
#The while loop in TCL repeatedly executes a block of code as long as a specified condition remains true.
set count 10
while {$count > 0} {
    puts "Count is $count"
    incr count -1
}
```

#### for

```tcl
#The for loop is a versatile looping construct that allows you to initialize a variable, specify a continuation condition, and define an increment or decrement operation, all in one line.
for {set i 10} {$i >= 0} {incr i -1} {
    puts "i is $i"
}
```

#### foreach

```tcl
#The foreach loop is used to iterate over items in a list. It can handle multiple lists and variables, which makes it quite flexible.
set myList [list apple banana cherry]
foreach fruit $myList {
    puts "Fruit: $fruit"
}

#You can use foreach to iterate over a list with two variables, each taking values two elements at a time from the list.
set myList [list a 1 b 2 c 3]
foreach {letter number} $myList {
    puts "Letter: $letter, Number: $number"
}

#You can also iterate over multiple lists simultaneously with different variables
set list1 [list a b c]
set list2 [list 1 2 3]
foreach ele1 $list1 ele2 $list2 {
    puts "$ele1 is paired with $ele2"
}
```

---

### conditional statements

#### if

```tcl
#The if statement evaluates a condition, and if that condition is true, the specified block of code is executed.
set age 20
if {$age >= 18} {
    puts "You are eligible to vote."
}

#You can extend an if statement with an else block to handle the false case of the condition.
set score 75
if {$score >= 50} {
    puts "Passed"
} else {
    puts "Failed"
}

#You can use elseif to specify additional conditions if the initial if condition is false. You can chain as many elseif statements as needed.
set marks 85
if {$marks >= 90} {
    puts "Grade: A"
} elseif {$marks >= 80} {
    puts "Grade: B"
} elseif {$marks >= 70} {
    puts "Grade: C"
} else {
    puts "Grade: F"
}
```

#### switch

```tcl
#The switch statement matches a variable against several values and executes a block of code corresponding to the first matching value. 
set color "red"
switch $color {
    "red" {
        puts "The color is red."
    }
    "blue" {
        puts "The color is blue."
    }
    default {
        puts "Unknown color."
    }
}
```

---

### Proc

#### Proc with Optional Arguments

```tcl
#Procs in TCL can have optional arguments by specifying default values in the argument list. If the caller does not supply these arguments when calling the proc, the default values are used.
proc random_num {min {max 100}} {
    set range [expr {$max - $min + 1}]
    set num [expr {$min + int(rand() * $range)}]
    return $num
}

#Usage
puts [random_num 10]      ;# Will generate a number between 10 and 100
puts [random_num 10 50]   ;# Will generate a number between 10 and 50
```

#### Proc with Variable Number of Arguments

```tcl
#TCL allows you to define procs that can accept a variable number of arguments. This is achieved by using args as the argument in the proc definition. Inside the proc, args is treated as a list containing all the arguments passed to the proc.
proc process_args {args} {
    puts "Number of arguments: [llength $args]"
    puts "The arguments are: $args"
    foreach arg $args {
        puts "Processing argument: $arg"
    }
}

#Usage
process_args 1 2 3 4 5  ;# Processes five arguments
process_args "hello" "world" ;# Processes two arguments
```

#### Returning Values

```tcl
#Procs in TCL implicitly return the result of the last command executed in the proc. To explicitly return a value, use the return command.
proc sum {a b} {
    return [expr {$a + $b}]
}
puts [sum 5 3]  ;# Output will be 8
```

#### Local Variables

```tcl
#Variables declared within a proc are local to that proc unless they are explicitly declared as global.
proc demo_local_vars {} {
    set local_var "I am local"
    puts $local_var
}
demo_local_vars
# puts $local_var  ;# This would raise an error because local_var is not accessible outside the proc.
```

#### Error Handling in Procs

```tcl
#You can handle errors within a proc using catch.
proc safe_div {a b} {
    if {$b == 0} {
        return -code error "Division by zero is not allowed"
    }
    return [expr {$a / $b}]
}

set result [catch {safe_div 10 0} err]
if {$result != 0} {
    puts "Error: $err"
} else {
    puts "Result: $err"  ;# $err contains the result if no error occurred
}
```

---

### Files

#### Opening and Closing Files

```tcl
#To work with files in TCL, you first need to open the file using the open command, which returns a file handle. You can specify different modes for accessing the file:

#r: Open the file for reading only; the file must exist.
#r+: Open the file for reading and writing; the file must exist.
#w: Open the file for writing only; overwrite the file if it exists, create a new file if it does not.
#w+: Open the file for reading and writing; overwrite the file if it exists, create a new file if it does not.
#a: Open the file for appending; data written will be added to the end. Creates the file if it does not exist.
#a+: Open the file for reading and appending; data written will be added to the end. Creates the file if it does not exist.

set filename "example.txt"
set filehandle [open $filename "w"]
puts $filehandle "This is a test."
close $filehandle
```

#### Reading Files

```tcl
#Memory-Efficient Line-by-Line Reading: This method uses less memory as it reads one line at a time without loading the entire file into memory.
proc read_file_less_memory {file_in} {
    if {[file exists $file_in]} {
        set filehandle [open $file_in "r"]
        set file_data {}
        while {[gets $filehandle line] >= 0} {
            lappend file_data $line
        }
        close $filehandle
        return $file_data
    } else {
        puts "File does not exist: $file_in"
    }
}

#Reading Entire File at Once
proc read_file {file_in} {
    puts "Reading: $file_in"
    if {[catch {set filehandle [open $file_in "r"]} err]} {
        puts "Error opening file: $err"
    } else {
        set file_data [split [read $filehandle] "\n"]
        close $filehandle
        return $file_data
    }
}
```

#### Error Handling in File Operations

```tcl
if {[catch {set filehandle [open "nonexistentfile.txt" "r"]} err]} {
    puts "Error opening file: $err"
}
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

### verification example

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

#### test_config.tcl

```tcl
# Define all tests in a dictionary
set tests {
    test1-name {
        {file_addr "/path/to/src1"}
        {file_name "file1"}
        {line_number 123}
        {description "Test 1 - Checking basic functionality"}
    }
    test2-name {
        {file_addr "/path/to/src2"}
        {file_name "file2"}
        {line_number 456}
        {description "Test 2 - Edge case handling"}
    }
}
return $tests
```

#### run.do

```tcl
# Check and delete the existing work library if it exists
if {[file exists "work"]} {
    vdel -all
}
vlib work

# Compile the Design Under Test (DUT) and Testbench (TB)
vcom -f dut.f
vlog -f tb.f

# Optimize the top module
vopt top -o top_optimized +acc +cover=sbfec+dut_top

# Load test configurations from an external file
set tests [source test_config.tcl]

# Procedure to run a test with coverage, logging, and result saving
proc run_test {test_name file_addr file_name line_number description} {
    puts "Running test: $test_name - $description"
    vsim top_optimized -coverage +UVM_TESTNAME=$test_name
    set NoQuitOnFinish 1
    onbreak {resume}
    log /* -r
    run -all
    coverage exclude -src $file_addr/$file_name.vhd -line $line_number -code s
    coverage attribute -name TESTNAME -value $test_name
    coverage save $test_name.ucdb
}

# Iterate over the dictionary and run each test
foreach {test_name test_config} $tests {
    dict with $test_config {
        run_test $test_name $file_addr $file_name $line_number $description
    }
}

# Merge coverage data and generate a report
set merged_tests_name "all_tests_merged"
vcover merge $merged_tests_name.ucdb {*}[dict keys [dict map {key val} $tests {set val $key.ucdb}]]
vcover report $merged_tests_name.ucdb -cvg -details

# Exit QuestaSim
quit

```

**[🔼Back to Top](#table-of-contents)**
