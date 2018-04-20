import copy

import GateNodes

class CircuitGraph:
    # Finished circuit graph will be stored here
    graph = dict()

    '''
    Used to map outputs --> inputs
    i.e. graph_nodes[output] = [inputs]
    output - output variable of the gate
    inputs - input variables required to calculate output
    '''
    graph_nodes = dict()

    '''
    Used to map outputs to the level that they can be calculated at
    (i.e. If all inputs to a gate are inputs to circuit, they will be
    in level 0. After level 0 is calculated, then we see gates that can
    be calculated with outputs from level 0 and circuit inputs. These will
    be added to level 1. Repeate until we have all outputs accounted for.
    '''
    graph_levels = dict()

    # List of inputs/outputs/gates to the circuit
    inputs = None
    outputs = None

    # List of the required gates for generating the proof
    required_gates = set()

    # Used to track the outputs that have been calculated
    output_available = set()

    num_levels = 0

    def __init__(self, netlist):
        netlist_split = netlist.splitlines()
        in_list = netlist_split[0]
        out_list = netlist_split[1]
        gates = netlist_split[2:]

        self.inputs = in_list.strip().split(',')
        self.outputs = out_list.strip().split(',')

        self.add_default_output_available()
        self.add_inputs_to_graph()

        self.generate_required_gates(gates)

        self.process_gates(gates)

        self.generate_output_levels()

    def add_default_output_available(self):
        for i in self.inputs:
            # Add both rails of each input
            self.output_available.add(i + '_0')
            self.output_available.add(i + '_1')

    def add_inputs_to_graph(self):
        create_input_node = getattr(GateNodes, 'InputNode')
        for i in self.inputs:
            # Add both rails of each input
            self.graph[i + '_0'] = create_input_node([i + '_0'])
            self.graph[i + '_1'] = create_input_node([i + '_1'])

    def generate_required_gates(self, gatelist):
        for gate_desc in gatelist:
            if not (gate_desc.startswith('#') or len(gate_desc.strip()) == 0):
                g_type, g_other = gate_desc.split(' ', 1)

                self.required_gates.add(g_type.lower())

    def process_gates(self, gatelist):
        self._create_placeholder_gates(gatelist)
        self._replace_placeholder_gates()

    def _create_placeholder_gates(self, gatelist):
        for gate_desc in gatelist:
            if not (gate_desc.startswith('#') or len(gate_desc.strip()) == 0):
                g_type, g_out, g_in = gate_desc.split(' ', 2)

                g_class = g_type + 'Node'
                create_gate_node = getattr(GateNodes, g_class)

                self.graph_nodes[g_out] = g_in.split()
                self.graph[g_out] = create_gate_node(g_in.split())

    def _replace_placeholder_gates(self):
        # This for loop iterates through the circuit and replaces the placeholder objects (strings representing the object)
        # with the actual object by doing a lookup in the graph, once this is done the full graph of the NCL circuit is set-up
        # and each node can call evaluate to get the boolean function leading to that output
        for g_node in self.graph.keys():
            if not isinstance(self.graph[g_node], GateNodes.InputNode):
                for var_index in range(len(self.graph_nodes[g_node])):
                    node_obj = self.graph[self.graph_nodes[g_node][var_index]]
                    self.graph[g_node].set_input(var_index, node_obj)

    def generate_output_levels(self):
        temp_graph_nodes = copy.deepcopy(self.graph_nodes)
        temp_output_available = copy.deepcopy(self.output_available)
        current_level_dependencies = set()
        while(temp_graph_nodes):
            for key in temp_graph_nodes.keys():
                if set(temp_graph_nodes[key]) <= temp_output_available:
                    current_level_dependencies.add(key)
                    temp_graph_nodes.pop(key)
                    try:
                        self.graph_levels[self.num_levels].add(key)
                    except KeyError:
                        self.graph_levels[self.num_levels] = set([key])
            temp_output_available |= current_level_dependencies
            self.num_levels += 1

    # Accessors to class members of CircuitGraph
    def get_graph(self):
        return self.graph

    def get_graph_nodes(self):
        return self.graph_nodes

    def get_graph_levels(self):
        return self.graph_levels

    def get_inputs(self):
        return self.inputs

    def get_outputs(self):
        return self.outputs

    def get_required_gates(self):
        return self.required_gates

    def get_outputs_available(self):
        return self.output_available

    def get_num_levels(self):
        return self.num_levels

