---
title: OVL CheatSheet
description: The most commonly used CheatSheet-Name commands/keyboard-shortcuts/concepts/tags/properties/attributes are given here.
created: 2024-05-09
---

## Table of Contents

- [OVL CheatSheet for Developers](#ovl-cheatsheet-for-developers)
  - [ovl\_always](#ovl_always)
  - [ovl\_cycle\_sequence](#ovl_cycle_sequence)
  - [ovl\_implication](#ovl_implication)
  - [ovl\_never](#ovl_never)
  - [ovl\_never\_unknown](#ovl_never_unknown)
  - [ovl\_next](#ovl_next)
  - [ovl\_one\_hot](#ovl_one_hot)
  - [ovl\_range](#ovl_range)
  - [ovl\_win\_unchange (Verilog-95, SVA-05, PSL-05, PSL-05)](#ovl_win_unchange-verilog-95-sva-05-psl-05-psl-05)
  - [ovl\_zero\_one\_hot](#ovl_zero_one_hot)
- [Comparision with sva](#comparision-with-sva)
  - [Implication operator](#implication-operator)
    - [Overlapped Implication Operator (a |-\> b)](#overlapped-implication-operator-a---b)
    - [Non-overlapped Implication Operator (a |=\> b)](#non-overlapped-implication-operator-a--b)
    - [Implication with a Fixed Delay (a |-\> ##n b)](#implication-with-a-fixed-delay-a---n-b)
    - [Timing Window (a |-\> ##\[n:m\] b)](#timing-window-a---nm-b)
  - [repetition operator](#repetition-operator)
    - [Consecutive Repetition for a Fixed Number of Cycles (req1 ##1 req2\[\*n\])](#consecutive-repetition-for-a-fixed-number-of-cycles-req1-1-req2n)
    - [Consecutive Repetition for a Range of Cycles (req1 ##1 req2\[\*m:n\])](#consecutive-repetition-for-a-range-of-cycles-req1-1-req2mn)
    - [Non-Consecutive Repetitive Operator (req1 ##1 req2\[=n\])](#non-consecutive-repetitive-operator-req1-1-req2n)
    - [Non-Consecutive Repetitive Operator with a Range (req1 ##1 req2\[=m:n\])](#non-consecutive-repetitive-operator-with-a-range-req1-1-req2mn)

# OVL CheatSheet for Developers

## ovl_always

## ovl_cycle_sequence

## ovl_implication

## ovl_never

## ovl_never_unknown

## ovl_next

## ovl_one_hot

## ovl_range

## ovl_win_unchange (Verilog-95, SVA-05, PSL-05, PSL-05)

## ovl_zero_one_hot

# Comparision with sva

## Implication operator

### Overlapped Implication Operator (a |-> b)

``` verilog
ovl_implication #(
    `OVL_ERROR,           // Severity level if the assertion fails
    `OVL_ASSERT,          // Property type
    "Error: a |-> b failed", // Message if the assertion fails
    `OVL_COVER_NONE,      // Coverage level
    `OVL_POSEDGE,         // Clock edge (positive edge)
    `OVL_ACTIVE_LOW,      // Reset polarity (active low)
    `OVL_GATE_CLOCK       // Gating type
) impl_a_to_b (
    .clock    (clk),
    .reset    (reset),
    .enable   (enable),
    .antecedent_expr(a), // Antecedent expression
    .consequent_expr(b), // Consequent expression
    .fire     (fire)
);
```

### Non-overlapped Implication Operator (a |=> b)

``` verilog
ovl_next #(
    `OVL_ERROR,
    `OVL_ASSERT,
    "Error: a |=> b failed",
    `OVL_COVER_NONE,
    `OVL_POSEDGE,
    `OVL_ACTIVE_LOW,
    `OVL_GATE_CLOCK
) next_a_to_b (
    .clock    (clk),
    .reset    (reset),
    .enable   (enable),
    .start_event(a),
    .test_expr(b),
    .fire     (fire)
);

```

### Implication with a Fixed Delay (a |-> ##n b)

``` verilog
ovl_cycle_sequence #(
    `OVL_ERROR,
    `OVL_ASSERT,
    "Error: a |-> ##n b failed",
    `OVL_COVER_NONE,
    `OVL_POSEDGE,
    `OVL_ACTIVE_LOW,
    `OVL_GATE_CLOCK
) cycle_seq_a_to_b (
    .clock    (clk),
    .reset    (reset),
    .enable   (enable),
    .start_event(a),
    .test_expr(b),
    .num_cks(n), // Number of clock cycles delay
    .fire     (fire)
);
```

### Timing Window (a |-> ##[n:m] b)

``` verilog
ovl_cycle_sequence #(
    `OVL_ERROR,
    `OVL_ASSERT,
    "Error: a |-> ##[n:m] b failed",
    `OVL_COVER_NONE,
    `OVL_POSEDGE,
    `OVL_ACTIVE_LOW,
    `OVL_GATE_CLOCK
) cycle_window_a_to_b (
    .clock    (clk),
    .reset    (reset),
    .enable   (enable),
    .start_event(a),
    .test_expr(b),
    .min_cks(n),   // Minimum clock cycles
    .max_cks(m),   // Maximum clock cycles
    .fire     (fire)
);
```

## repetition operator

### Consecutive Repetition for a Fixed Number of Cycles (req1 ##1 req2[*n])

``` verilog
ovl_sequence #(
    `OVL_ERROR,            // Severity level if the assertion fails
    `OVL_ASSERT,           // Property type
    "Error: req2 does not hold for n consecutive cycles after req1",
    `OVL_COVER_NONE,       // Coverage level
    `OVL_POSEDGE,          // The clock edge (positive edge)
    `OVL_ACTIVE_LOW,       // The reset polarity (active low)
    `OVL_GATE_CLOCK        // Gating type
) seq_req1_req2_n (
    .clock    (clk),
    .reset    (reset),
    .enable   (enable),
    .start_event(req1),
    .test_expr(req2),
    .num_cks(n),
    .fire     (fire)
);

```

### Consecutive Repetition for a Range of Cycles (req1 ##1 req2[*m:n])

``` verilog
ovl_sequence #(
    `OVL_ERROR,
    `OVL_ASSERT,
    "Error: req2 does not hold for m to n consecutive cycles after req1",
    `OVL_COVER_NONE,
    `OVL_POSEDGE,
    `OVL_ACTIVE_LOW,
    `OVL_GATE_CLOCK
) seq_req1_req2_m_to_n (
    .clock    (clk),
    .reset    (reset),
    .enable   (enable),
    .start_event(req1),
    .test_expr(req2),
    .min_cks(m),
    .max_cks(n),
    .fire     (fire)
);


```

### Non-Consecutive Repetitive Operator (req1 ##1 req2[=n])

``` verilog
```

### Non-Consecutive Repetitive Operator with a Range (req1 ##1 req2[=m:n])

``` verilog
```