import os
import CircuitGraph

class InputComplete:
    required_templates = set(['rail', 'nullp', 'datap'])

    def __init__(self, netlist):
        self.circuit_graph = CircuitGraph.CircuitGraph(netlist)

    def generate_logic_type(self):
        logic_statement = '(set-logic QF_BV)\n'
        return logic_statement

    def generate_input_functions(self):
        comment = '; Inputs: '
        declarations = ''

        for i in self.circuit_graph.get_inputs():
            comment += i + ' '
            declarations += '(declare-fun %s () (_ BitVec 2))\n' % i

        statement = comment + '\n' + declarations
        return statement

    def generate_output_functions(self):
        comment = '; Outputs: '
        declarations = ''

        for i in self.circuit_graph.get_outputs():
            comment += i + ' '
            declarations += '(declare-fun %s () (_ BitVec 2))\n' % i

        statement = comment + '\n' + declarations
        return statement

    def generate_current_gate_functions(self):
        comment = '; Current gate outputs'
        declarations = '(declare-fun Gc_0 () (_ BitVec 1))\n'

        statement = comment + '\n' + declarations
        return statement

    def generate_required_templates(self):
        statement = ''
        for template in self.required_templates:
            template_file_name = template + '.smt2'
            with open(os.path.join('templates', template_file_name), 'r') as template_file:
                statement += template_file.read()

        return statement

    def generate_required_gate_templates(self):
        statement = ''
        for template in self.circuit_graph.get_required_gates():
            template_file_name = template + '.smt2'
            with open(os.path.join('templates', template_file_name), 'r') as template_file:
                statement += template_file.read()

        return statement

    def generate_proof_obligation(self):
        raise NotImplementedError('This is meant to be an abstract class, the proof obligation should be generated within its respective class that inherits this one.')

    def generate_check_model(self):
        check_sat = '(check-sat)\n'
        get_model = '(get-model)'
        return check_sat + get_model
