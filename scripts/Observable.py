from GateNodes import InputNode

import CircuitGraph
import SMTProofGenerator

class Observable(SMTProofGenerator.SMTProofGenerator):
    
    def __init__(self, netlist, proof_gate):
        self.circuit_graph = CircuitGraph.CircuitGraph(netlist)
        self.proof_gate = proof_gate


    def generate_proof_obligation(self):
        statement = self._generate_assert()

        return statement

    def _generate_assert(self):
        statement = ''
        statement += '(assert\n'
        statement += self._generate_not()
        statement += ')\n'

        return statement

    def _generate_not(self):
        statement = ''
        statement += '(not\n'
        statement += self._generate_let()
        statement += self._generate_let_output()
        statement += self._generate_implication()

        statement += ')\n'*(self.circuit_graph.get_num_levels() + 1)

        statement += ')\n'

        return statement

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
                    if i == self.proof_gate:
                        statement += '(_ bv0 1) '
                    else:
                        if isinstance(graph[i], InputNode):
                            m = self.input_re.match(i)
                            statement += '(rail{0} {1}) '.format(m.group(2), m.group(1))
                        else:
                            statement += i + ' '
                statement += 'Gc_0))\n'

            statement += ')\n'
        return statement

    def _generate_let_output(self):
        outputs = self.circuit_graph.get_outputs()

        statement = ''
        statement += '(let\n'
        statement += '(\n'
        for output in outputs:
            rail1 = '{0}_1'.format(output).replace(self.proof_gate, '(_ bv0 1)')
            rail0 = '{0}_0'.format(output).replace(self.proof_gate, '(_ bv0 1)')
            statement += '({0} (concat {1} {2}))\n'.format(output, rail1, rail0)
        statement += ')\n'

        return statement

    def _generate_implication(self):
        statement = ''
        statement += '(=>\n'

        statement += self._generate_precondition()
        statement += self._generate_postcondition()

        statement += ')\n'

        return statement

    def _generate_precondition(self):
        statement = ''
        statement += '(and\n'
        statement += self._generate_inputs_data()
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
        statement += self._generate_outputs_data()
        statement += ')\n'
        statement += ')\n'

        return statement

    def _generate_outputs_data(self):
        outputs = self.circuit_graph.get_outputs()
        statement = ''
        for output in outputs:
            statement += '(datap {0})\n'.format(output)

        return statement
        

