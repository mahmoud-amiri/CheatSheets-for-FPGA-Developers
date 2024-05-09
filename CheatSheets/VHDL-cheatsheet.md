---
title: VHDL CheatSheet
description: The most commonly used VHDL syntaxes are given here.
created: 2024-04-27
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
  - [Testbench template](#testbench-template)
  - [Read from file and write to file](#read-from-file-and-write-to-file)
  - [assert](#assert)

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

## Testbench template

```vhdl
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.NUMERIC_STD.ALL; -- Only if you're using numeric_std functions

-- Entity declaration for the testbench
-- Note: Testbenches do not have ports
entity tb_MyDesign is
end tb_MyDesign;

-- Architecture of the testbench
architecture behavior of tb_MyDesign is

    -- Component declaration of the design under test (DUT)
    component MyDesign
        port (
            clk        : in  std_logic;
            reset      : in  std_logic;
            input_sig  : in  std_logic_vector(7 downto 0);
            output_sig : out std_logic_vector(7 downto 0)
        );
    end component;

    -- Signals for connecting to the DUT
    signal tb_clk        : std_logic := '0';
    signal tb_reset      : std_logic;
    signal tb_input_sig  : std_logic_vector(7 downto 0);
    signal tb_output_sig : std_logic_vector(7 downto 0);

    -- Clock period definition
    constant clk_period : time := 10 ns;

begin

    -- Instantiation of the DUT
    uut: MyDesign
        port map (
            clk        => tb_clk,
            reset      => tb_reset,
            input_sig  => tb_input_sig,
            output_sig => tb_output_sig
        );

    -- Clock process definition
    clk_process : process
    begin
        tb_clk <= '0';
        wait for clk_period/2;
        tb_clk <= '1';
        wait for clk_period/2;
    end process;

    -- Test stimulus process
    stim_proc: process
    begin       
        -- Initialize Inputs
        tb_reset <= '1';
        tb_input_sig <= (others => '0');
        
        -- Wait for 100 ns for global reset to finish
        wait for 100 ns;
        
        -- Add stimulus here
        tb_reset <= '0';
        wait for clk_period*10;
        
        tb_input_sig <= "00000001";
        wait for clk_period*10;
        
        tb_input_sig <= "00000010";
        wait for clk_period*10;

        -- Finish the test and check the results
        assert false report "End of test" severity failure;

    end process;

end behavior;

```
**[🔼Back to Top](#table-of-contents)**

## Read from file and write to file

```vhdl
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_TEXTIO.ALL; -- For textio operations
use STD.TEXTIO.ALL; -- For textio operations

-- Entity declaration for the testbench
entity ReadFileTB is
end ReadFileTB;

-- Architecture of the testbench
architecture Behavioral of ReadFileTB is

    -- File type declaration
    file file_in : TEXT open READ_MODE is "input_file.txt";

begin

    -- Reading file process
    process
        variable line : LINE; -- Temporary storage for each line read
        variable value_read : std_logic_vector(7 downto 0); -- Modify as needed
    begin
        -- Read until the end of the file
        while not endfile(file_in) loop
            readline(file_in, line); -- Read a line from the file
            read(line, value_read); -- Parse the line into a variable
            -- Now value_read contains the data from the file for further processing
        end loop;

        wait; -- Stop the simulation here
    end process;

end Behavioral;

```

```vhdl
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_TEXTIO.ALL; -- For textio operations
use STD.TEXTIO.ALL; -- For textio operations

-- Entity declaration for the testbench
entity WriteFileTB is
end WriteFileTB;

-- Architecture of the testbench
architecture Behavioral of WriteFileTB is

    -- File type declaration
    file file_out : TEXT open WRITE_MODE is "output_file.txt";

begin

    -- Writing file process
    process
        variable line : LINE; -- Temporary storage for data to write
    begin
        -- Example: Write 10 lines to the file
        for i in 1 to 10 loop
            write(line, std_logic_vector(to_unsigned(i, 8))); -- Convert integer to std_logic_vector and write to the line
            writeline(file_out, line); -- Write the line to the file
        end loop;

        wait; -- Stop the simulation here
    end process;

end Behavioral;

```

**[🔼Back to Top](#table-of-contents)**

## assert

```vhdl
-- Check if the output is as expected
assert (output_signal = expected_value)
    report "Output signal does not match expected value."
    severity error;

-- Check if a signal is stable when it should be
assert not (signal'event and signal = '1')
    report "Signal should not have an event here."
    severity warning;

-- Terminate the simulation if a certain condition is not met
assert (system_state = READY)
    report "System is not ready. Simulation failed."
    severity failure; -- This will stop the simulation if system_state /= READ

```

**[🔼Back to Top](#table-of-contents)**