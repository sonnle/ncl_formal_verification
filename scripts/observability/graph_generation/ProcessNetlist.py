import argparse

import GateNodes

def main():
    args = parse_arguments()
    nl_graph = dict()
    nl_inputs = dict()
    with open(args.netlist, 'r') as netlist_file:
        handle_inputs = getattr(GateNodes, 'InputNode')
        input_vars = netlist_file.readline().strip().split(',')
        for var in input_vars:
            nl_graph[var + '0'] = handle_inputs([var + '0'])
            nl_graph[var + '1'] = handle_inputs([var + '1'])

        output_vars = netlist_file.readline().strip().split(',') # placeholder to read out the outputs, not sure if needed yet for line in netlist_file:

        for line in netlist_file:
            gate, output, inputs = line.split(' ', 2)

            gate_class = gate + 'Node'
            handle_gates = getattr(GateNodes, gate_class)

            nl_inputs[output] = inputs.split()
            nl_graph[output] = handle_gates(inputs.split())

    # This for loop iterates through the circuit and replaces the placeholder objects (strings representing the object)
    # with the actual object by doing a lookup in the graph, once this is done the full graph of the NCL circuit is set-up
    # and each node can call evaluate to get the boolean function leading to that output
    for key in nl_graph.keys():
        if not isinstance(nl_graph[key], GateNodes.InputNode):
            for var in range(len(nl_inputs[key])):
                node_object = nl_graph[nl_inputs[key][var]]
                nl_graph[key].set_input(var, node_object)

    for key in nl_graph.keys():
        print 'Function for {0} with output {1}:\n{2}\n'.format(nl_graph[key].get_gate_name(), key, nl_graph[key].evaluate_smt())

def parse_arguments():
    parser = argparse.ArgumentParser(description='Process a netlist of a ncl \
        circuit and generate the graph, allowing for evaulation of the boolean \
        function leading up to each gate.')
    parser.add_argument('netlist', help='Netlist of the ncl circuit')
    return parser.parse_args()

if __name__ == '__main__':
    main()