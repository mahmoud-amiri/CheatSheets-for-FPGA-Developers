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

# UVM CheatSheet for Developers

## 1st Section

**[🔼Back to Top](#table-of-contents)**

# UVMF CheatSheet for Developers

1. First need to determine how many interfaces there are for the design
2. Group signals into interfaces
3. Create a YAML configuration file for each interface


## Yaml files

### interface

file name : <design-name>_<interface-name>.yaml

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
        data: []
        operation: 1'b0

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
      analysis_exports: []
      analysis_ports: []
    
      config_constraints: []
      config_vars: []
    
      parameters: []
    
      scoreboards:
      - name: <design-name>_sb
        sb_type: <class type for the scoreboard.This is a UVMF base library component #NO_IDEA>
        trans_type: <the scoreboard will operate on  ALU_out_transaction #NO_IDEA>
    
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
    
      interface_params: []
    
      reset_assertion_level: 'False'  
      reset_duration: 200ns         
    
      top_env: <design-name>
```

### predictor

file name : <design-name>_util_comp_predictor.yaml

```yaml
uvmf:
  util_components:
    <design-name>_predictor:  
      analysis_exports: #Tells UVMF code generator to create exports/ports with the specified names and specified transaction types
      - name: <design-name>_<interface-name>_agent_ae
        type: '<design-name>_<interface-name>_transaction #()'
      analysis_ports:
      - name: <design-name>_sb_ap
        type: '<design-name>_<interface-name>_transaction #()'
      type: predictor #do not change

```