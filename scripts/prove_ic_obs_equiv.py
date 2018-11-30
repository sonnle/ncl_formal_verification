import ProofGenerator

import os
import glob
import argparse
import subprocess

def main():
    args = parse_arguments()
    netlist_name = os.path.splitext(os.path.basename(args.netlist))[0]

    with open(args.netlist, 'r') as netlist_file:
        netlist = netlist_file.read()
        proof_ic_n2d = ProofGenerator.InputCompleteN2D(netlist)
        proof_ic_d2n = ProofGenerator.InputCompleteD2N(netlist)
        proof_obs = ProofGenerator.Observability(netlist)
        with open(args.synclist, 'r') as sync_netlist_file:
            sync_netlist = sync_netlist_file.read()
            proof_equiv = ProofGenerator.Equivalence(netlist, sync_netlist)

    with open('{0}_ic_n2d.smt2'.format(netlist_name), 'wb') as write_file:
        write_file.write(proof_ic_n2d.generate_smt_proof())

    with open('{0}_ic_d2n.smt2'.format(netlist_name), 'wb') as write_file:
        write_file.write(proof_ic_d2n.generate_smt_proof())

    for gate in proof_obs.get_gate_list():
        with open('{0}_obs_n2d_{1}.smt2'.format(netlist_name, gate), 'wb') as write_file:
            write_file.write(proof_obs.generate_n2d_proof(gate))

        with open('{0}_obs_d2n_{1}.smt2'.format(netlist_name, gate), 'wb') as write_file:
            write_file.write(proof_obs.generate_d2n_proof(gate))

    with open('{0}_equiv.smt2'.format(netlist_name), 'wb') as write_file:
        write_file.write(proof_equiv.generate_smt_proof())

    for proof_file in glob.glob('{0}*.smt2'.format(netlist_name)):
        command = 'z3 -smt2 {0}'.format(proof_file)
        try:
            subprocess.check_output(command, shell=True)
            print 'Proof file: {0} returned SAT'.format(proof_file)
            break
        except subprocess.CalledProcessError as e:
            if 'unsat' in e.output:
                print 'Proof file: {0} returned UNSAT'.format(proof_file)
                os.remove(proof_file)
            else:
                print 'Error in reading SMT-LIB file returned: {0}'.format(e.output)

def parse_arguments():
    parser = argparse.ArgumentParser(description='Take in a NCL netlist and generate input-completeness and observability proofs encoded in SMT-LIB and checks them using Z3 solver.')
    parser.add_argument('netlist', type=str, help='Path to the NCL netlist file.')
    parser.add_argument('synclist', type=str, help='Path to the syncrounous netlist file.')
    return parser.parse_args()


if __name__ == '__main__':
    main()
