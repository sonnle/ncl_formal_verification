import glob
import argparse
import subprocess

import Observable
import ObservableData
import CircuitGraph


def main():
    for proof_file in glob.glob('./proof_files/*'):
        subprocess.check_output('rm {0}'.format(proof_file), shell=True)

    args = parse_arguments()
    netlist = None
    with open(args.netlist, 'r') as r_file:
        netlist = r_file.read()
    cirGraph = CircuitGraph.CircuitGraph(netlist)
    graph = cirGraph.get_graph()

    for gate in graph.keys():
        obsProof = Observable.Observable(netlist, gate)
        obsProofData = ObservableData.ObservableData(netlist, gate)
        smt_file_name = 'proof_files/null_{0}_{1}.smt2'.format(args.smt2, gate)
        smt_file_name_data = 'proof_files/data_{0}_{1}.smt2'.format(args.smt2, gate)
        with open(smt_file_name, 'w') as w_file:
            w_file.write(obsProof.generate_smt_proof())

        with open(smt_file_name_data, 'w') as w_file:
            w_file.write(obsProofData.generate_smt_proof())
    
    observable = True
    for proof_file in glob.glob('./proof_files/*'):
        command = 'z3 -smt2 {0}'.format(proof_file)
        try:
            subprocess.check_output(command, shell=True)
            print 'Proof file: {0} returned SAT'.format(proof_file)
            observable = False
        except subprocess.CalledProcessError:
            print 'Proof file: {0} returned UNSAT'.format(proof_file)

    if observable:
        print '{0} is Observable'.format(args.netlist)
    else:
        print '{0} is not Observable'.format(args.netlist)

def parse_arguments():
    parser = argparse.ArgumentParser(description='Process a netlist of a ncl \
        circuit and generate the graph, allowing for evaulation of the boolean \
        function leading up to each gate.')
    parser.add_argument('netlist', help='Netlist of the ncl circuit')
    parser.add_argument('smt2', help='Name of smt2 file to generate proof to')
    return parser.parse_args()

if __name__ == '__main__':
    main()
