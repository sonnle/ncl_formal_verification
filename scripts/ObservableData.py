from GateNodes import InputNode

import CircuitGraph
import InputCompleteD2N

class ObservableData(InputCompleteD2N.InputCompleteD2N):
    
    def __init__(self, netlist, proof_gate):
        self.circuit_graph = CircuitGraph.CircuitGraph(netlist)
        self.proof_gate = proof_gate

    def _generate_let(self):
        graph = self.circuit_graph.get_graph()
        graph_nodes = self.circuit_graph.get_graph_nodes()
        graph_levels = self.circuit_graph.get_graph_levels()

        statement = ''
        for level in graph_levels.keys():
            statement += '(let\n'
            statement += '(\n'

            for output in graph_levels[level]:
                statement += '({0} ({1} '.format(output, graph[output].get_gate_name().lower())
                for i in graph_nodes[output]:
                    if isinstance(graph[i], InputNode):
                        m = self.input_re.match(i)
                        statement += '(rail{0} {1}) '.format(m.group(2), m.group(1))
                    else:
                        statement += i + ' '
                statement += 'Gc_0))\n'
            statement += ')\n'

            statement += '(let\n'
            statement += '(\n'
            for output in graph_levels[level]:
                statement += '({0}_d ({1} '.format(output, graph[output].get_gate_name().lower())
                for i in graph_nodes[output]:
                    if i == self.proof_gate:
                        statement += '(_ bv1 1) '
                    else:
                        if isinstance(graph[i], InputNode):
                            m = self.input_re.match(i)
                            statement += '(rail{0} {1}_d) '.format(m.group(2), m.group(1))
                        else:
                            statement += i + '_d '
                statement += '{0}))\n'.format(output)
            statement += ')\n'
            
        return statement

    def _generate_let_output(self):
        outputs = self.circuit_graph.get_outputs()

        statement = ''
        statement += '(let\n'
        statement += '(\n'
        for output in outputs:
            rail1 = '{0}_1'.format(output)
            rail0 = '{0}_0'.format(output)
            statement += '({0} (concat {1} {2}))\n'.format(output, rail1, rail0)
            rail1 = '{0}_1_d'.format(output).replace(self.proof_gate+'_d', '(_ bv1 1)')
            rail0 = '{0}_0_d'.format(output).replace(self.proof_gate+'_d', '(_ bv1 1)')
            statement += '({0}_d (concat {1} {2}))\n'.format(output, rail1, rail0)
        statement += ')\n'

        return statement

    def _generate_precondition(self):
        statement = ''
        statement += '(and\n'
        statement += self._generate_inputs_data()
        statement += self._generate_stepped_inputs_null()
        statement += self._generate_proof_gate_function()
        statement += self._generate_current_gate_output_zero()
        statement += ')\n'

        return statement

    def _generate_inputs_data(self):
        inputs = self.circuit_graph.get_inputs()
        
        statement = ''
        for i in inputs:
            statement += '(datap {0})\n'.format(i)
        return statement

    def _generate_stepped_inputs_null(self):
        inputs = self.circuit_graph.get_inputs()

        statement = ''
        for i in inputs:
            statement += '(nullp {0}_d)\n'.format(i)
        return statement

    def _generate_proof_gate_function(self):
        graph = self.circuit_graph.get_graph()
        statement = ''
        statement += '; Gate function for {0}\n'.format(self.proof_gate)
        statement += '(= {0} (_ bv1 1))\n'.format(graph[self.proof_gate].evaluate_smt())
        
        return statement

    def _generate_current_gate_output_zero(self):
        return '(= (_ bv0 1) Gc_0)\n'

    def _generate_postcondition(self):
        statement = ''
        statement += '(not\n'
        statement += '(and\n'
        statement += self._generate_outputs_null()
        statement += ')\n'
        statement += ')\n'

        return statement

    def _generate_outputs_null(self):
        outputs = self.circuit_graph.get_outputs()
        statement = ''
        for output in outputs:
            statement += '(nullp {0}_d)\n'.format(output)

        return statement
        

