import os

class UMultProof(object):
    num_let = 0
    partial_products = dict()
    required_templates = ['rail', 'nullp', 'datap']
    required_gate_templates = set([])

    def __init__(self, bits):
        self.bits = bits

    def generate_smt_proof(self):
        return \
        self.generate_header() + \
        self.generate_logic_type() + \
        self.generate_input_functions() + \
        self.generate_output_functions() + \
        self.generate_current_gate_functions() + \
        self.generate_required_templates() + \
        self.generate_required_gate_templates() + \
        self.generate_proof_obligation() + \
        self.generate_check_model()

    def generate_header(self):
        header = ''

        return header

    def generate_logic_type(self):
        logic_statement = '(set-logic QF_BV)\n'

        return logic_statement

    def generate_input_functions(self):
        comment = '; Inputs: '
        declarations = ''

        for i in range(self.bits):
            comment += 'X{0} Y{0} '.format(i)
            declarations += '(declare-fun X{0} () (_ BitVec 2))\n'.format(i)
            declarations += '(declare-fun Y{0} () (_ BitVec 2))\n'.format(i)
        statement = comment + '\n' + declarations

        return statement

    def generate_output_functions(self):
        comment = '; Outputs: '
        declarations = ''
        for i in range(self.bits*2):
            comment += 'Z{0} '.format(i)
            declarations += '(declare-fun Z{0} () (_ BitVec 2))\n'.format(i)
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
            with open(os.path.join('..', '..', '..', 'templates', template_file_name), 'r') as template_file:
                statement += template_file.read()

        return statement

    def generate_required_gate_templates(self):
        statement = ''
        for template in self.required_gate_templates:
            template_file_name = template + '.smt2'
            with open(os.path.join('..', '..', '..', 'templates', template_file_name), 'r') as template_file:
                statement += template_file.read()

        return statement

    def generate_proof_obligation(self):
        raise NotImplementedError('This is meant to be an abstract class, the proof obligation should be generated within its respective class that inherits this one.')

    def generate_check_model(self):
        check_sat = '(check-sat)\n'
        get_model = '(get-model)'

        return check_sat + get_model
