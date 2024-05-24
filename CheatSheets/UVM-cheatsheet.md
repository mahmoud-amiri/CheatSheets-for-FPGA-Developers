---
title: UVM CheatSheet
description: The most commonly used UVM concepts are given here.
created: 2024-05-17
---

## Table of Contents

- [UVM CheatSheet for Developers](#uvm-cheatsheet-for-developers)
  - [1st Section](#1st-section)
- [UVMF CheatSheet for Developers](#uvmf-cheatsheet-for-developers)
  - [Yaml files](#yaml-files)
    - [interface](#interface)
    - [environment](#environment)
      - [benches](#benches)
    - [predictor](#predictor)
  - [Instantiate \& Wire Up the DUT](#instantiate--wire-up-the-dut)
    - [Clocks \& Resets](#clocks--resets)
    - [Instantiate the DUT](#instantiate-the-dut)
    - [Compiling The DUT](#compiling-the-dut)
  - [Adding Protocol Information To The Driver BFM](#adding-protocol-information-to-the-driver-bfm)
    - [Modifying the ALU\_in driver BFM](#modifying-the-alu_in-driver-bfm)

# UVM CheatSheet for Developers

## 1st Section

**[🔼Back to Top](#table-of-contents)**

# UVMF CheatSheet for Developers

1. First need to determine how many interfaces there are for the design
2. Group signals into interfaces
3. Create a YAML configuration file for each interface
4. Adding the DUT & wiring it up to the BFMs and the clock/reset
5. Adding protocol specific information to the driver BFMs
6. Adding protocol specific information to the monitor BFMs
7. Adding DUT specific behavior to the predictor
8. Extending the default test to create a new test which overrides the default sequence
9. Extending the default sequence to create a new sequence that generates the desired stimulus for the test

## Yaml files

### interface

file name : <design-name>_<interface-name>_interface.yaml

```yaml
uvmf:
  interfaces:
    <design-name>_<interface-name>: #interface name
      clock: clk
      reset: rst
      reset_assertion_level: <'False':#reset active low polarity 'True' :#reset active high polarity>

      config_constraints: [<specify configuration constraints>]
      config_vars: [<specify configuration variables>]

      hdl_typedefs: #Define any types used by the HDL side of the testbench
      - name: <design-name>_<interface-name>_<type-name>_t 
        type: <enum bit[n:0] {A = 3'b000, B = 3'b001, C = 3'b010}>
      hvl_typedefs: []

      parameters: # Any parameters defined here will impact be passed to multiple classes within the agent
      - name: <DESIGN-NAME>_<INTERFACE-NAME>_<PARAMETER-NAME>
        type: <int>
        value: <'8'>

      ports:  #Here we define all of the signal names, directions and widths for the agent/interface
      - name: <port-name>
        dir: <output or input> #Direction specified here is in relation to the testbench
        width: <'1' or PARAMETER_NAME>  
      
      response_info:
        data: []  #The data directive allows the user to specify what response data should be passed back from the driver to the originating sequence.
        operation: 1'b0 #The operation directive allows the user to define if the driver should pass any response data back to the sequence. 1’b0  tells the driver not to send back any response

      transaction_constraints:  #Defines any constraints to be used on the transaction variables
      - name: <constraint-name>_c
        value: '{ <variable-name> inside {A, B, C}; }' 

      transaction_vars: #Defines any variable to be used by the transaction class.
      - name: <variable-name>
        type: <<type-name>  or bit [<PARAMETER-NAME>-1:0]>
        iscompare: 'True'
        isrand: 'True'  
```

**[🔼Back to Top](#table-of-contents)**

### environment

file name : <design-name>_environment.yaml

```yaml

uvmf:
  environments:
    <design-name>:  
    
      agents:
      - name: <design-name>_<interface-name>_agent  
        type: <design-name>_<interface-name> 
        initiator_responder: <"INITIATOR" or "RESPONDER">  

      analysis_components:
      - name: <design-name>_pred
        type: <design-name>_predictor #component name (it has dedicated yaml file)
      
      #These allow the user to specify analysis exports & ports to add to the environment class, typically implemented when the block level environment is to be utilized within a larger system level UVM testbench. 
      analysis_exports: []
      analysis_ports: []

      #These allow the user to specify environment level configuration variables, configuration constraints and parameters for the environment class.
      config_constraints: []
      config_vars: []

      #Parameters specified here can be passed down into any of the instantiated agents or other analysis components.
      parameters: []
    
      scoreboards:
      - name: <design-name>_sb
        sb_type: uvmf_in_order_scoreboard
        trans_type: <design-name>_<interface-name>_transaction   # the transaction class that the scoreboard will operate on 
    
      #The subenvs entry allows the user to import other pre-generated UVMF environments, thus creating a hierarchical environment.
      #Typically this is used when importing QVIP UVMF environments or creating a system level UVMF testbench that is reusing block level UVMF environments
      subenvs: []
    
      tlm_connections:  #specify a point to point connection between ports/exports
      - driver: <design-name>_<interface-name>_agent.monitored_ap       # connection 00     
        receiver: <design-name>_pred.<design-name>_<interface-name>_agent_ae                            
      - driver: <design-name>_pred.<design-name>_sb_ap                  # connection 01
        receiver: <design-name>_sb.expected_analysis_export
      - driver: <design-name>_<interface-name>_agent.monitored_ap       # connection 02
        receiver: <design-name>_sb.actual_analysis_export

```

#### benches

file name : <design-name>_bench.yaml

```yaml
uvmf:
  benches:
    <design-name>:   
    
      active_passive: #define active or passive agents
      - bfm_name: <design-name>_<interface-name>_agent
        value: <ACTIVE or PASSIVE>   #ACTIVE :generating stimulus and monitoring the signal interface #PASSIVE :will not drive stimulus as it only monitors DUT output signals
      
    
      clock_half_period: <5ns :top level testbench clock period>  
      clock_phase_offset: <9ns top level testbench clock phase offset>
    
      interface_params: []  #Enables user to specify how any underlying BFMs should be parameterized
    
      reset_assertion_level: 'False'  
      reset_duration: 200ns         
    
      top_env: <design-name>

```

### predictor

file name : <design-name>_predictor.yaml

```yaml
uvmf:
  util_components:
    <design-name>_predictor:  
      analysis_exports: #Tells UVMF code generator to create exports/ports with the specified names and specified transaction types
      #Tells UVMF code generator to create exports/ports with the specified names and specified transaction types
      - name: <design-name>_<interface-name>_agent_ae
        type: '<design-name>_<interface-name>_transaction #()'
      analysis_ports:
      - name: <design-name>_sb_ap
        type: '<design-name>_<interface-name>_transaction #()'
      type: predictor #do not change


```

## Instantiate & Wire Up the DUT

### Clocks & Resets

`project_benches/ALU/tb/testbench/hdl_top.sv`

The hdl_top module contains simple clock and reset generation code that the user can modify to change frequencies, add more clocks, etc depending on the need for their specific DUT.

### Instantiate the DUT

`project_benches/ALU/tb/testbench/hdl_top.sv`

- Remove the instantiations of ‘dut_verilog’ & ‘dut_vhdl’
- Add instance of the ALU and wire up ports to the corresponding agent interface.

### Compiling The DUT

**windows:** ` project_benches/ALU/sim/compile.do`
Remove the compilation lines for the default verilog_dut.v & vhdl_dut.vhd
Replace with the vlog command to compile the <design-name>.v source file

**linux:** ` project_benches/ALU/sim/Makefile`

- Modify the source file list from the default verilog_dut.sv to use the <design-name>.v source file
- Modify the comp_<design-name>_dut target to only now compile up a Verilog DUT

## Adding Protocol Information To The Driver BFM

### Modifying the ALU_in driver BFM
