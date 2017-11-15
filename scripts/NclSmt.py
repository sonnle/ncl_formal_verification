import os
import re

class NclSmt():
    """Class used to encapsulate the information to be written to smt file"""
    gate_used = {'th12'     : 0, 'th13'     : 0, 'th14'     : 0,
                 'th22'     : 0, 'th23'     : 0, 'th23w2'   : 0,
                 'th24'     : 0, 'th24comp' : 0, 'th24w2'   : 0,
                 'th24w22'  : 0, 'th33'     : 0, 'th33w2'   : 0,
                 'th34'     : 0, 'th34w2'   : 0, 'th34w22'  : 0,
                 'th34w3'   : 0, 'th34w32'  : 0, 'th44'     : 0,
                 'th44w2'   : 0, 'th44w22'  : 0, 'th44w3'   : 0,
                 'th44w322' : 0, 'th54w22'  : 0, 'th54w32'  : 0,
                 'th54w322' : 0, 'thand0'   : 0, 'thxor0'   : 0,}
    ha_adder_used = False
    fa_adder_used = False
    inputs = None
    outputs = None
    num_gates = 0
    num_levels = 0
    gate_info = dict()

    def __init__(self, netlist, outfile):
        self.netlist = netlist
        self.outfile = outfile
        self.process_netlist()

    def _prepend_tabs(self, prepend_str, num_tabs=1):
        """Helper function used to clean up code for formatting by prepending tabs to the string"""
        return '\t'*num_tabs + prepend_str

    def process_netlist(self):
        """Process the netlist file to identify inputs, outputs, and gates used"""
        with open(self.netlist, 'r') as netlist_file:
            self.inputs = netlist_file.readline().split(',')
            self.outputs = netlist_file.readline().split(',')
            for line in netlist_file:
                (gate, level, wires) = line.split(' ', 2)
                if gate is 'HA':
                    self.num_gates += 4
                    self.ha_adder_used = True
                elif gate is 'FA':
                    self.num_gates += 4
                    self.fa_adder_used = True
                else:
                    self.num_gates += 1
                self.gate_info[self.num_gates] = dict()
                self.gate_info[self.num_gates]['type'] = gate
                self.gate_info[self.num_gates]['level'] = level
                self.gate_info[self.num_gates]['wires'] = wires.split(' ')

                if self.num_levels < level:
                    self.num_levels = level
                if not self.gate_used[gate]:
                    self.gate_used[gate] = 1

    def helper_let_statements(self, gate_num, gate):
        ret_str = self._prepend_tabs('(Gn_%d (%s ' % (gate_num-1, gate['type']), 4)
        for wire in gate['wires'][:-1]:
            mat = re.search(r'(?P<variable>[A-z]+)(?P<rail>\d+)', wire)
            if mat.group('variable') == 'I':
                ret_str += 'Gc_%d ' % int(mat.group('rail'))
            else:
                ret_str += '(rail%s %s) ' % (mat.group('rail'), mat.group('variable'))
        mat = re.search(r'(?P<variable>[A-z]+)(?P<rail>\d+)', gate['wires'][-1])
        ret_str += 'Gc_%d))\n' % (gate_num-1)
        return ret_str

    def find_gate_num(self, output):
        ret_gate = [0, 0]
        for gate in self.gate_info:
            mat = re.search(r'(?P<variable>[A-z]+)(?P<rail>\d+)', self.gate_info[gate]['wires'][-1])
            if mat.group('variable') == output:
                ret_gate[int(mat.group('rail'))] = gate - 1
        return ret_gate

    @property
    def process_let_statements(self):
        """Temp doc string"""
        ret_str = ''
        for level in range(int(self.num_levels)):
            iter_str = self._prepend_tabs('\n', 2) + self._prepend_tabs('(let\n', 2) + self._prepend_tabs('(\n', 3)
            for gate_num in self.gate_info:
                if int(self.gate_info[gate_num]['level']) == (level + 1):
                    iter_str += self.helper_let_statements(gate_num, self.gate_info[gate_num])
            iter_str += self._prepend_tabs(')', 3)
            ret_str += iter_str

        iter_str = '\n' + self._prepend_tabs('(let\n', 2) + self._prepend_tabs('(\n', 3)
        for output in self.outputs:
            output_gates = self.find_gate_num(output.strip())
            iter_str += self._prepend_tabs('(%s (concat Gn_%d Gn_%d))\n' % \
                (output.strip(), output_gates[1], output_gates[0]), 4)
        iter_str += self._prepend_tabs(')', 3)
        ret_str += iter_str

        return ret_str

    @property
    def heading_smt2(self):
        """Returns the heading for smt2 file"""
        return '; Formal verification proof - input completeness of %s\n' % self.netlist

    @property
    def logic_smt2(self):
        """Returns bit-vector logic, could be changed to accept different logics"""
        return '(set-logic QF_BV)\n\n'

    @property
    def inputs_smt2(self):
        """Returns the declarations of the input variables"""
        return '; Inputs: ' + ', '.join(variable.strip() for variable in self.inputs) + '\n' + \
            '\n'.join('(declare-fun %s () (_ BitVec 2))' % \
            variable.strip() for variable in self.inputs) + '\n\n'

    @property
    def outputs_smt2(self):
        """Returns the declarations of the output variable"""
        return '; Outputs: ' + ', '.join(variable.strip() for variable in self.outputs) + '\n' + \
            '\n'.join('(declare-fun %s () (_ BitVec 2))' % \
            variable.strip() for variable in self.outputs) + '\n\n'

    def template_smt2(self, file_name):
        """Returns what is read from the template file"""
        with open(os.path.join('..', 'templates', file_name), 'r') as temp_file:
            return temp_file.read() + '\n'

    @property
    def gate_current_smt2(self):
        """Returns the declarations of the current state of the threshold gates"""
        return '; Current values of threshold gates\n' + \
            '\n'.join('(declare-fun Gc_%d () (_ BitVec 1))' % \
            num for num in range(self.num_gates)) + '\n\n'

    @property
    def input_not_invalid(self):
        """Returns the declarations that each input is not invalid"""
        not_declaration = []
        for variable in self.inputs:
            not_declaration.append(self._prepend_tabs('(not (= (_ bv3 2) %s))' % variable.strip(), 4))
        return '\n' + '\n'.join(declaration for declaration in not_declaration)

    @property
    def threshold_gates_null(self):
        """Returns the declaration that each threshold gate current value starts at zero"""
        gate_null_declaration = []
        for gate in range(self.num_gates):
            gate_null_declaration.append(self._prepend_tabs('(= (_ bv0 1) Gc_%d)' % gate, 4))
        return '\n' + '\n'.join(declaration for declaration in gate_null_declaration)

    @property
    def one_input_null(self):
        """Returns the check that at least one of the inputs is null"""
        input_null_declaration = []
        for variable in self.inputs:
            input_null_declaration.append(self._prepend_tabs('(nullp %s)' % variable.strip(), 5))
        return '\n' + self._prepend_tabs('(or', 4) + self._prepend_tabs('\n', 5) + \
            '\n'.join(declaration for declaration in input_null_declaration) + '))\n'

    @property
    def one_output_null(self):
        """Returns the declaration that at least one output is null"""
        output_null_declation = []
        for variable in self.outputs:
            output_null_declation.append(self._prepend_tabs('(nullp %s)' % variable.strip(), 3))

        return self._prepend_tabs('(or', 2) + \
            self._prepend_tabs('\n', 3) + \
            '\n'.join(declaration for declaration in output_null_declation) + \
            '))' + \
            (')'*(int(self.num_levels)+1)) + '\n'

    @property
    def implication(self):
        """Returns the implication for the proof"""
        return self._prepend_tabs('(=>\n', 2) + \
            self._prepend_tabs('(and', 3) + \
            self._prepend_tabs('%s' % self.input_not_invalid, 4) + \
            self._prepend_tabs('%s%s%s' % (self.threshold_gates_null, self.one_input_null, self.one_output_null), 4)

    @property
    def proof_input_complete_smt2(self):
        """
        Returns the proof for input completeness based on the
        gate level/inputs/outputs of the netlist
        """
        return '; SAT/UNSAT assertion for %s\n' % self.netlist + \
            '(assert\n' + self._prepend_tabs('(not%s\n%s' % \
            (self.process_let_statements, self.implication)) + \
            self._prepend_tabs(')') + \
            self._prepend_tabs('\n)\n')

    @property
    def footer_smt2(self):
        """Returns the check-sat and get-model method calls"""
        return '(check-sat)\n(get-model)\n'

    def generate_smt2(self):
        """Generate the final smt2 file to the output file"""
        with open(self.outfile, 'w') as smt2_file:
            smt2_file.write(self.heading_smt2)
            smt2_file.write(self.logic_smt2)

            smt2_file.write(self.inputs_smt2)
            smt2_file.write(self.outputs_smt2)

            for file_name in ['rail.smt2', 'nullp.smt2']:
                smt2_file.write(self.template_smt2(file_name))

            for gate in self.gate_used:
                if self.gate_used[gate]:
                    gate_template_file = '%s.smt2' % gate
                    smt2_file.write(self.template_smt2(gate_template_file))

            smt2_file.write(self.gate_current_smt2)
            smt2_file.write(self.proof_input_complete_smt2)
            smt2_file.write(self.footer_smt2)
