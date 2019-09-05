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
    Make sure Z3 Theorem Prover binary is on your path (can be found at https://github.com/Z3Prover/z3)
    Make sure you create folder with the same name as the ncl_netlist (i.e. umult5.txt would require a umult5 folder in the scripts/test directory)
    python prove_ic_obs_equiv.py <ncl_netlist> <sync_netlist>
    With the current directory you can run the following:
    1. Make a folder umult5 under scripts/test
    2. Run `python prove_ic_obs_equiv.py ncl_umult/umult5.txt sync_umult/umult5.txt
    3. Feel free to mess around with comparing umult6 with umult5, etc.
