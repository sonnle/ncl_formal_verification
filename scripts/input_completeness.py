# -*- coding: utf-8 -*-
import argparse

import InputCompleteN2D
import InputCompleteD2N
import CircuitGraph

def main():
    args = parse_arguments()
    netlist = None

    with open(args.netlist, 'r') as netlist_file:
        netlist = netlist_file.read()

    # myCirGraph = CircuitGraph.CircuitGraph(netlist)

    # print myCirGraph.get_graph()
    # print '\n'

    # print myCirGraph.get_graph_nodes()
    # print '\n'

    # print myCirGraph.get_inputs()
    # print '\n'

    # print myCirGraph.get_outputs()
    # print '\n'

    # print myCirGraph.get_required_gates()
    # print '\n'

    # print myCirGraph.get_outputs_available()
    # print '\n'


    # test = myCirGraph.get_graph()
    # for key in test.keys():
    #     print key
    #     print test[key].get_gate_name()
    #     print test[key].evaluate_smt()
    #     print '\n'

    # print myCirGraph.get_graph_levels()
    # print '\n'

    myIcProof = InputCompleteN2D.InputCompleteN2D(netlist)

    # print myIcProof.generate_logic_type()

    # print myIcProof.generate_input_functions()

    # print myIcProof.generate_output_functions()

    # print myIcProof.generate_current_gate_functions()

    # print myIcProof.generate_required_templates()

    # print myIcProof.generate_required_gate_templates()

    # print myIcProof.generate_proof_obligation()

    # print myIcProof.generate_check_model()

    # myIcProof = InputCompleteD2N.InputCompleteD2N(netlist)

    # print myIcProof.generate_logic_type()

    # print myIcProof.generate_input_functions()

    # print myIcProof.generate_output_functions()

    # print myIcProof.generate_current_gate_functions()

    # print myIcProof.generate_required_templates()

    # print myIcProof.generate_required_gate_templates()

    # print myIcProof.generate_proof_obligation()

    # print myIcProof.generate_check_model()

    with open(args.smt, 'w') as w_file:
        w_file.write(myIcProof.generate_smt_proof())


def parse_arguments():
    parser = argparse.ArgumentParser(description='Process a netlist of a ncl \
        circuit and generate the graph, allowing for evaulation of the boolean \
        function leading up to each gate.')
    parser.add_argument('netlist', help='Netlist of the ncl circuit')
    parser.add_argument('smt', help='SMT2 file to write proof to')
    return parser.parse_args()

if __name__ == '__main__':
    main()
