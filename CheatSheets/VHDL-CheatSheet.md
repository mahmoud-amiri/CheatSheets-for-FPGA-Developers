---
title: CheatSheet-Name CheatSheet
description: The most commonly used CheatSheet-Name commands/keyboard-shortcuts/concepts/tags/properties/attributes are given here.
created: 2022-10-01
---

## Table of Contents

- [VHDL CheatSheet for Developers](#vhdl-cheatsheet-for-developers)
  - [Libraries](#libraries)
  - [Entities and Architecture](#entities-and-architecture)
  - [Instantiate the Component](#instantiate-the-component)
  - [Process](#process)
  - [Assignment](#assignment)
  - [Data type](#data-type)
  - [Data type conversions](#data-type-conversions)
  - [Operators](#operators)
  - [Conditions](#conditions)

# VHDL CheatSheet for Developers

## Libraries

```vhdl
Library ieee; --IEEE
use ieee.std_logic_1164.all;  --logic vector definitions
use ieee.numeric_std.all; -- arithmetic operations on logic vectors
```
**[🔼Back to Top](#table-of-contents)**

## Entities and Architecture

```vhdl
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;

-- Entity declaration with generics
entity EntityName is
    generic (
        n : integer := 16; -- Default value 16
        m : integer := 32  -- Default value 32
    );
    port (
        FirstPort  : in  std_logic;                        -- Single bit input
        SecondPort : out std_logic;                        -- Single bit output
        ThirdPort  : inout std_logic_vector(n-1 downto 0)  -- Bi-directional bus with size defined by generic 'n'
    );
end EntityName;

-- Architecture declaration
architecture ArchitectureName of EntityName is

    -- Signal declarations
    signal wire : std_logic;                             -- Single wire signal
    signal bus : std_logic_vector(m-1 downto 0);         -- Bus signal with size defined by generic 'm'

begin

    -- Behavior and assignments go here
    -- Example: Simple assignment (not practical, just illustrative)
    wire <= FirstPort;
    SecondPort <= wire;
    bus <= (others => '0'); -- Initialize bus to all zeros

end ArchitectureName;

```
**[🔼Back to Top](#table-of-contents)**

## Instantiate the Component

```vhdl
architecture Behavioral of ParentEntity is

-- Component declaration for instantiation
    component SubComponent is
        port (
            InputA   : in  std_logic_vector(7 downto 0);
            InputB   : in  std_logic_vector(7 downto 0);
            OutputX  : out std_logic_vector(7 downto 0)
        );
    end component;
begin

-- Instantiation of SubComponent
    InstanceName: SubComponent
        port map (
            InputA   => ParentInput1,
            InputB   => ParentInput2,
            OutputX  => InternalOutput
        );

end Behavioral;
```
**[🔼Back to Top](#table-of-contents)**


## Process

```vhdl
 -- Process with synchronous reset
    process(clk)
    begin
        if rising_edge(clk) then  -- Triggering on the rising edge of the clock
            if reset = '1' then   -- Checking for a synchronous reset
                data_out <= (others => '0');  -- Reset data output to all zeros
            else
                data_out <= data_in;  -- Transfer input to output if not reset
            end if;
        end if;
    end process;
```
**[🔼Back to Top](#table-of-contents)**

## Assignment

1. signal assignment
```vhdl
 A <= B;-- A will take the value of B at the end of the simulation cycle
```

2. Variable Assignment (:=)
```vhdl
process
    variable count : integer := 0;
begin
    count := count + 1;  -- The value of count is updated immediately
end process;
```

3. Conditional Signal Assignment
```vhdl
-- Conditional signal assignment
C <= A when SEL = "00" else
     B when SEL = "01" else
     '0';
```

4. Selected Signal Assignment
```vhdl
-- Selected signal assignment
with SEL select
    D <= A when "00",
         B when "01",
         C when "10",
         '0' when others;
```

5. Blocking and Non-blocking Assignments 
```vhdl
--Example for Blocking (Variables):
process
    variable temp : integer;
begin
    temp := 5;  -- Immediate update
    temp := temp + 1;  -- Also immediate
end process;
```

```vhdl
--Example for Non-blocking (Signals):
process
begin
    A <= B;  -- Scheduled for the end of the process
    A <= A + 1;  -- Still scheduled; does not immediately see the first assignment's effect
end process;
```

**[🔼Back to Top](#table-of-contents)**


## Data type

```vhdl
 -- Enumerated Type
type State_Type is (Idle, Running, Stopped);
signal state : State_Type;
```

```vhdl
 -- Integer Type
signal counter : integer range 0 to 100;
```

```vhdl
 -- Floating Point Type
-- Note: Floating point is typically used via library definitions
library IEEE;
use IEEE.float_pkg.all;

signal real_number : float;
```

```vhdl
 -- Physical Type
type Time_ns is range 0 to 1000 units
    ns;
end units;
signal delay_time : Time_ns := 500 ns;
```

```vhdl
 -- Arrays
type Byte is array (7 downto 0) of bit;
signal data_byte : Byte;
```

```vhdl
 -- Multidimensional Array
type Matrix is array (1 to 3, 1 to 3) of integer;
signal my_matrix : Matrix;
```

```vhdl
 -- Records
type Complex_Number is record
    Real : integer;
    Imag : integer;
end record;
signal complex_val : Complex_Number;
```

**[🔼Back to Top](#table-of-contents)**


## Data type conversions

```vhdl
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.NUMERIC_STD.ALL;

-- Entity declaration (not strictly necessary for the example, but included for completeness)
entity TypeConversionExample is
end TypeConversionExample;

-- Architecture body
architecture Behavioral of TypeConversionExample is

    -- Signals declaration
    signal i : integer;
    signal s : signed(7 downto 0);
    signal u : unsigned(7 downto 0);
    signal v : std_logic_vector(7 downto 0);
    
begin

    -- Conversions from 'integer' to 'signed' and 'unsigned'
    s <= to_signed(i, s'length);  -- Converts 'integer' to 'signed'
    u <= to_unsigned(i, u'length); -- Converts 'integer' to 'unsigned'
    
    -- Conversions from 'signed' and 'unsigned' to 'integer'
    i <= to_integer(s);  -- Converts 'signed' to 'integer'
    i <= to_integer(u);  -- Converts 'unsigned' to 'integer'
    
    -- Conversions between 'signed', 'unsigned', and 'std_logic_vector'
    s <= signed(v);        -- Type cast from 'std_logic_vector' to 'signed'
    u <= unsigned(v);      -- Type cast from 'std_logic_vector' to 'unsigned'
    v <= std_logic_vector(s); -- Converts 'signed' to 'std_logic_vector'
    v <= std_logic_vector(u); -- Converts 'unsigned' to 'std_logic_vector'

    -- Convert integer to std_logic_vector
    v <= std_logic_vector(to_signed(i, v'length)); 
    v <= std_logic_vector(to_unsigned(u, v'length)); 

    -- Convert std_logic_vector to integer (as unsigned)
    i <= to_integer(unsigned(v));
    
    -- Alternatively, for a signed representation:
    i <= to_integer(signed(v));

end Behavioral;
```
**[🔼Back to Top](#table-of-contents)**



## Operators

```vhdl
--Logical Operators
C <= A and B; -- Logical AND
C <= A or B;  --Logical OR
C <= A nand B;  --Logical NAND
C <= A nor B; --Logical NOR
C <= A xor B; --Logical Exclusive OR
C <= A xnor B;  --Logical Exclusive NOR
B <= not A; --Logical NOT 
```

```vhdl
--Relational Operators
if (A = B) then ... --Equal to
if (A /= B) then ...  --Not equal to
if (A < B) then ... --Less than
if (A <= B) then ...  --Less than or equal to
if (A > B) then ... --Greater than
if (A >= B) then ...  --Greater than or equal to
```

```vhdl
--Arithmetic Operators
C <= A + B; --Addition 
D <= +A;  --Unary Plus
C <= A - B; --Subtraction 
D <= -A;  --Unary Minus
C <= A * B; --Multiplication
C <= A / B; --Division
C <= A mod B; --Modulus
C <= A rem B; --Remainder
```

```vhdl
--Shift Operators
C <= A sll 1; --Shift left logical
C <= A srl 1; --Shift right logical
C <= A sla 1; --Shift left arithmetic (keeps sign)
C <= A sra 1; --Shift right arithmetic (keeps sign)
C <= A rol 1; --Rotate left
C <= A ror 1; --Rotate right
```
```vhdl
--Concatenation
C <= A & B;
```

```vhdl
--Condition
C <= (A > B) ? A : B; -- This is not supported in pre-2008 standards
```

**[🔼Back to Top](#table-of-contents)**

## Conditions

```vhdl
--If Statement
process(clk)
begin
    if rising_edge(clk) then
        if reset = '1' then
            -- Synchronous reset condition
            counter <= (others => '0');
        elsif enable = '1' then
            -- Enable condition
            counter <= counter + 1;
        else
            -- Default condition
            counter <= counter;
        end if;
    end if;
end process;
```

```vhdl
--Case Statement
process(state)
begin
    case state is
        when IDLE =>
            -- IDLE state actions
            led <= '0';
        when RUNNING =>
            -- RUNNING state actions
            led <= '1';
        when ERROR =>
            -- ERROR state actions
            led <= '0';
        when others =>
            -- Default actions
            led <= 'X';
    end case;
end process;
```
```vhdl
-- Conditional Signal Assignment
led <= '1' when switch = '1' else
       '0';
```
```vhdl
--Selected Signal Assignment
with state select
    led <= '1' when RUNNING,
           '0' when IDLE,
           '0' when ERROR,
           'X' when others;
```
```vhdl
--With-Select-When
with operation select
    result <= a + b when "00",
              a - b when "01",
              a * b when "10",
              a / b when others;
```
```vhdl
--Conditional Expressions (VHDL-2008)
result <= a when sel = '1' else b;
```
**[🔼Back to Top](#table-of-contents)**


