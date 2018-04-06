from GateNodes import InputNode

import InputComplete

class InputCompleteN2D(InputComplete.InputComplete):

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

        # One for each level, then an extra for the let_outputs
        statement += ')\n'*(self.circuit_graph.get_num_levels() + 1)

        # Another extra for the closing of the not
        statement += ')\n'

        return statement

    def _generate_let(self):
        graph = self.circuit_graph.get_graph()
        graph_node = self.circuit_graph.get_graph_nodes()
        graph_levels = self.circuit_graph.get_graph_levels()

        statement = ''
        for level in graph_levels.keys():
            statement += '(let\n'
            statement += '(\n'

            for output in graph_levels[level]:
                statement += '(%s (%s ' % (output, graph[output].get_gate_name().lower())
                for i in graph_node[output]:
                    if isinstance(graph[i], InputNode):
                        statement += '(rail{0} {1}) '.format(i[-1], i[:-1])
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
            statement += '({0} (concat {0}1 {0}0))\n'.format(output)
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
        statement += self._generate_inputs_not_illegal()
        statement += self._generate_current_gate_output_zero()
        statement += self._generate_or_null_inputs()
        statement += ')\n'

        return statement

    def _generate_postcondition(self):
        outputs = self.circuit_graph.get_outputs()

        statement = ''
        statement += '(or\n'
        for output in outputs:
            statement += '(nullp {0})\n'.format(output)
        statement += ')\n'

        return statement

    def _generate_inputs_not_illegal(self):
        inputs = self.circuit_graph.get_inputs()

        statement = ''
        for i in inputs:
            statement += '(not (= (_ bv3 2) {0}))\n'.format(i)
        return statement

    def _generate_current_gate_output_zero(self):
        return '(= (_ bv0 1) Gc_0)\n'

    def _generate_or_null_inputs(self):
        inputs = self.circuit_graph.get_inputs()
        statement = ''
        statement += '(or\n'
        for i in inputs:
            statement += '(nullp {0})\n'.format(i)
        statement += ')\n'
        return statement
