from GateNodes import InputNode

import SMTProofGenerator

class InputCompleteD2N(SMTProofGenerator.SMTProofGenerator):

    def generate_proof_obligation(self):
        statement = self._generate_assert()

        return statement

    def generate_input_functions(self):
        comment = '; Inputs: '
        comment_d = '; Data Inputs: '
        declarations = '\n'
        declarations_d = '\n'

        for i in self.circuit_graph.get_inputs():
            comment += i + ' '
            comment_d += i + '_d '
            declarations += '(declare-fun {0} () (_ BitVec 2))\n'.format(i)
            declarations_d += '(declare-fun {0}_d () (_ BitVec 2))\n'.format(i)

        statement = comment + declarations + comment_d + declarations_d

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

        # Two for each level, then an extra for the let_outputs
        statement += ')\n'*(self.circuit_graph.get_num_levels()*2 + 1)

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
                statement += '({0} ({1} '.format(output, graph[output].get_gate_name().lower())
                for i in graph_node[output]:
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
                for i in graph_node[output]:
                    if isinstance(graph[i], InputNode):
                        m = self.input_re.match(i)
                        statement += '(rail{0} {1}) '.format(m.group(2), m.group(1))
                    else:
                        statement += i + ' '
                statement += '{0}))\n'.format(output)
            statement += ')\n'

        return statement

    def _generate_let_output(self):
        outputs = self.circuit_graph.get_outputs()

        statement = ''
        statement += '(let\n'
        statement += '(\n'
        for output in outputs:
            statement += '({0} (concat {0}_1_d {0}_0_d))\n'.format(output)
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
        statement += self._generate_d_inputs_not_illegal()
        statement += self._generate_current_gate_output_zero()
        statement += self._generate_or_null_eq_inputs()
        statement += self._generate_or_data_d_inputs()
        statement += ')\n'

        return statement

    def _generate_postcondition(self):
        outputs = self.circuit_graph.get_outputs()

        statement = ''
        statement += '(or\n'
        for o in outputs:
            statement += '(datap {0}_d)\n'.format(o)
        statement += ')\n'

        return statement

    def _generate_inputs_data(self):
        inputs = self.circuit_graph.get_inputs()

        statement = ''
        for i in inputs:
            statement += '(datap {0})\n'.format(i)

        return statement

    def _generate_current_gate_output_zero(self):
        return '(= (_ bv0 1) Gc_0)\n'

    def _generate_d_inputs_not_illegal(self):
        inputs = self.circuit_graph.get_inputs()

        statement = ''
        for i in inputs:
            statement += '(not (= (_ bv3 2) {0}_d))\n'.format(i)

        return statement

    def _generate_or_null_eq_inputs(self):
        inputs = self.circuit_graph.get_inputs()

        statement = ''
        for i in inputs:
            statement += '(or\n'
            statement += '(nullp {0}_d)\n'.format(i)
            statement += '(= {0} {0}_d)\n'.format(i)
            statement += ')\n'
        return statement

    def _generate_or_data_d_inputs(self):
        inputs = self.circuit_graph.get_inputs()

        statement = ''
        statement += '(or\n'
        for i in inputs:
            statement += '(datap {0}_d)\n'.format(i)
        statement += ')\n'

        return statement
