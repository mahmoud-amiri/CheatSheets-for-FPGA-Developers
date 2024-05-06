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

```systemverilog
c_assert: assert property(@(posedge clk) not(a && b));
```
**[🔼Back to Top](#table-of-contents)**