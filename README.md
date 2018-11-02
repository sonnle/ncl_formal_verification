# SMT2-LIB Verification Proof Generator

## Given a NCL netlist given in the following format:
    1. First line represents the lists of inputs separated by a comma.
    2. Second line represents the lists of outputs separated by a comma.
    3. Each line starting from the Third line --> EOF represents one gate of the circuit.
  
  #### Each line starting from the Third line --> EOF is formatted as follows:
    1. The NCL gate type is listed first.
    2. Then the name of the gate output wire is second.
    3. Each variable after that represents the gate inputs with the input with highest weight going first.
    
## Proofs can be generated using scripts inside the scripts/ folder:
    python prove_ic_and_obs.py <netlist>
