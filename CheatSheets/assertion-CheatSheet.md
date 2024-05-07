---
title: assertion CheatSheet
description: The most commonly used assertion properties are given here.
created: 2024-05-06
---

## Table of Contents

- [CheatSheet-Name CheatSheet for Developers](#cheatsheet-name-cheatsheet-for-developers)
  - [1st Section](#1st-section)
    - [1st Sub/Nested-Section](#1st-subnested-section)
      - [1st Double-Sub/Nested-Section](#1st-double-subnested-section)
  - [2nd Section](#2nd-section)
  - [nth Section](#nth-section)

# Assertion CheatSheet for FPGA Developers

## Systemverilog Concurrent assertion
### Boolean Expression
1. Logical operators: && (logical AND), || (logical OR), ! (logical NOT)
2. Equality operators: == (equal), != (not equal)
3. Relational operators: < (less than), <= (less than or equal), > (greater than), >= (greater than or equal)
4. Bitwise operators: & (bitwise AND), | (bitwise OR), ^ (bitwise XOR)
5. Reduction operators: & (AND reduction), | (OR reduction), ^ (XOR reduction)
```systemverilog
c_assert: assert property(@(posedge clk) not(a && b)); //If there is a posedge in the clk, the assertion will be failed if a and b are high at the same times.
```
**[🔼Back to Top](#table-of-contents)**

### Sequence

```systemverilog
sequence <name_of_sequence>;
  ……
endsequence
```

Sequences with Timing Relationship
```systemverilog
// "a" should be high at every clock's positive edge, "b" should be high two cycles later; otherwise, the sequence fails.
sequence seq;
@(posedge clk) a ##2 b;
endsequence
```

Implication operator
```systemverilog
// The |-> symbol represents the overlapped implication operator.if signal "a" is high on a given positive clock edge, then signal "b" should also be high on the same clock edge
property p;
@(posedge clk) a|->b;
endproperty

//The |=> symbol denotes the non-overlapped implication operator.If "a" is high at a positive clock edge, "b" should be high at the next clock edge.
property p;
@(posedge clk) a |=> b;
endproperty

//Implication with a fixed delay on the consequent:The property verifies that if "a" is high on a specific positive clock edge, then "b" should be high after a delay of n clock cycles.
property p;
@(posedge clk) a |-> ##n b;
endproperty

//Timing Window: The property "p" asserts that if "a" rises on a positive clock edge, then within n to m clock cycles, "b" should also rise. (n>=0, m>1, m>n)
//m upper limit can be defined with a "$" sign, indicating no upper bound, termed the "eventuality" operator. The checker continues matching until the end of the simulation.
property p;
@(posedge clk) a |-> ##[n:m] b;
endproperty
```
repetition operator
```systemverilog
//If a sequence of events occurs repeatedly for n times, it's represented as [*n].(n > 0, n < $)
//if req1 is true, req2 must be true for n consecutive clock cycles after 1 clock cycle.
sequence seq;
@(posedge clk) req1 ##1 req2[*n];
endsequence

//The repetition operator can be used in a range using [*m:n].
//if req1 is true, then after 1 clock cycle, req2 must be true for a minimum of m and a maximum of n consecutive clock cycles.
sequence seq;
@(posedge clk) req1 ##1 req2[*m:n];
endsequence

//Non Consecutive repetitive operator:If sequence event repetition needs to be detected for n non-consecutive clock cycles, [=n] can be used
sequence seq;
@(posedge clk) req1 ## req2[=n];
endsequence

//The non-consecutive repetitive operator with a range:Non-consecutive repetition can be specified within a range as [=m:n]
sequence seq;
@(posedge clk) req1 ##1 req2[=n:m];
endsequence
```

```systemverilog
//return true if LSB of signal changed to 1.
sequence seq;
@(posedge clk) $rose(a);
endsequence

//return true if LSB of signal changed to 0.
sequence seq;
@(posedge clk) $fell(a);
endsequence

//return true if the value of signal did not changed.
sequence seq;
@(posedge clk) $stable(a);
endsequence
```
The "ended" construct
```systemverilog
//Attaching ended to a sequence name, such as s.ended, indicates that you are referring to the exact clock cycle in which the sequence s completes.
sequence sl5a;
  ©(posedge elk) a ##n1 b;
endsequence
sequence sl5b;
  ©{posedge elk) c ##n2 d;
endsequence

//after the sequence sla completes, the sequence slb should begin immediately in the next clock cycle
property pla;
sla |=> slb;
endproperty

//n3 clock cycles after the sequence sla ends, the sequence slb must also end. 
property plb;
  sla.ended |-> ##n3 slb.ended;
endproperty

ala: assert property(pla);
alb: assert property(plb);
```

The "$past" construct
```systemverilog
//it provides the value of the signal from the previous clock cycle. Property p1 verifies that at a given positive clock edge, if the expression (a) is true, then n cycles earlier, the expression (b) was true.
Property p1;
@(posedge clk) a |-> ($past(b, n) == I'bl);
endproperty
al: assert property(pl);
```

combine two sequences
```systemverilog
//and:The final property succeeds only if both sequences succeed. They must start at the same point but can end at different points.
sequence s1a;
@(posedge elk) a##[l:2] b;
endsequence
sequence s2b;
@(posedge elk) c##[2:3] d;
endsequence
property p2;
@{posedge elk) s2a and s2b;
endproperty
a2: assert property(p2);

//intersect:very similar to the "and" operator, The final property succeeds only if both sequences succeed, both sequences must start and end simultaneously, meaning they must have the same length.
property p2;
@{posedge clk) s2a intersect s2b;
endproperty

//Or: The final property succeeds when any one of the sequences succeed
property p2;
@(posedge clk) s2a or s2b;
endproperty

//first_match: The "first_match" construct ensures that only the initial sequence match is utilized, disregarding others. This is valuable when merging multiple sequences, as only the first match within the timing window is needed to evaluate the property further.
property p3;
@(posedge clk) first_match(s2a or s2b);
endproperty

//throughout:The throughout operator in SVA is used when you need the expression to be true at every clock cycle throughout the duration of the specified sequence.
//This part of the property ensures that during the entire evaluation of the sequence, the signal "start" must always be low. 
property p1;
@(posedge clk) $fell(start) |->(!start) throughout (##1 (!a&&b) ##1 (c[->5]) ##1 (a&&!b));
endproperty

//within:The "within" construct permits the definition of a sequence contained within another sequence.
sequence s3a;
  @(posedge clk)
    ((!a&&b) ##1 (c[->5]) ##1 (a&&!b));
endsequence
sequence s3b;
  @(posedge clk)
    $fell(start) ##[15:20] $rose(start);
endsequence
sequence s3;
  @(posedge clk) s3a within s3b;
endsequence
property p3;
  @(posedge clk) $fell(start) |-> s3;
endproperty
a3: assert property(p3);
```

Built-in system function
```systemverilog
//onehot: only one bit of the expression can be high on any given clock edge
a1a: assert
  property(@(posedge elk) $onehot(state));

//onehot0: only one bit of the expression can be high or none of the bits can be high on any given clock edge.
a1b: assert
  property(@(posedge elk) $onehot0(state));

//isunknown: checks if any bit of the expression is X or Z  
a1c: assert
  property (@(posedge elk) $isunknown(bus) ) ;

//countones: counts the number of bits that are high in a vector  
a1d: assert
  property(@(posedge elk)$countones(bus)> 1);
```

```systemverilog
//In specific design scenarios, if a certain condition is true, we may not want to proceed with the check. SVA offers a construct called "disable iff" which acts as an asynchronous reset for the checker.
property p34;
©(posedge clk)
disable iff (reset)
$rose(start) |=> a[=2] ##1 c[=5] ##1 !start;
endproperty
```

**[🔼Back to Top](#table-of-contents)**

#### reusability
```systemverilog
Sequence and_seq(a,b);
a  && b;
endsequence

sequence sig_34
and_seq(sig_3,sig_4);
endsequence
```
**[🔼Back to Top](#table-of-contents)**

### Property

```systemverilog
property name_of_property;
  < test expression> or <complex sequence expressions>
endproperty
```
**[🔼Back to Top](#table-of-contents)**

### Assert

```systemverilog
  assertion_name: assert_property( property_name );
  coverage_name: cover_property( property_name );
```
**[🔼Back to Top](#table-of-contents)**







```systemverilog
// Registers and outputs at reset: 
//Checks that when reset is not active, data and addr must be zero
    property reset_check;
        (!rst_n) |-> (data === 32'b0 && addr === 32'b0);
    endproperty

    assert property (reset_check)
        else $error("Assertion failed: data or addr not zero when reset is inactive.");

//Restrictions on control and data signals:   
// Assert that control signals are known (not x or z)
    assert property (@(posedge clk) !$isunknown(ctrl))
        else $error("Error: Control signals contain unknown values");  
// Assert that at most one control signal is high at a time
    assert property (@(posedge clk) $onehot0(ctrl))
        else $error("Error: Multiple control signals are active simultaneously");

    // Assert that cmd signal must be either READ or WRITE
    assert property (@(posedge clk) cmd inside {READ, WRITE})
        else $error("Error: Command signal is out of expected range");


//Handshaking protocols:

```


### Binding with Access to Internal Signal
```systemverilog
module counter(
    input logic clk,
    input logic rst_n,
    input logic mode, // 0 for count down, 1 for count up
    output logic [7:0] count_out
);
    logic [7:0] internal_count; // Internal signal to be monitored

    // internal logic...

endmodule
```

```systemverilog
module counter_checker(
    input logic clk,
    input logic rst_n,
    input logic [7:0] internal_count, // Accessing the internal signal
    input logic mode
);

    // Check the count does not exceed the upper limit
    property check_upper_limit;
        @(posedge clk) mode && (internal_count == 8'hFF) |-> ##1 internal_count == 8'h00;
    endproperty
    assert_upper_limit: assert property(check_upper_limit);

    // Check the count does not go below zero
    property check_lower_limit;
        @(posedge clk) !mode && (internal_count == 8'h00) |-> ##1 internal_count == 8'hFF;
    endproperty
    assert_lower_limit: assert property(check_lower_limit);

endmodule
```
```systemverilog
module top;
    logic clk, rst_n, mode;
    logic [7:0] count_out;

    // Instantiating the Counter
    counter my_counter(
        .clk(clk),
        .rst_n(rst_n),
        .mode(mode),
        .count_out(count_out)
    );

    // Binding the checker with access to the internal signal
    bind counter counter_checker checker_instance(
        .clk(clk),
        .rst_n(rst_n),
        .internal_count(my_counter.internal_count), // Direct access to internal signal
        .mode(mode)
    );

endmodule
```
