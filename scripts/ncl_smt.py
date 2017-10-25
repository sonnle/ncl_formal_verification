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
    inputs = None
    outputs = None
    num_gates = 0
    num_levels = 0
    gate_info = dict()

    def __init__(self, netlist, outfile):
        self.netlist = netlist
        self.outfile = outfile
        self._process_netlist()

    def _process_netlist(self):
        """Process the netlist file to identify inputs, outputs, and gates used"""
        with open(self.netlist, 'r') as netlist_file:
            self.inputs = netlist_file.readline().split(',')
            self.outputs = netlist_file.readline().split(',')
            for line in netlist_file:
                self.num_gates += 1
                (gate, level, wires) = line.split(' ', 2)
                self.gate_info[self.num_gates] = dict()
                self.gate_info[self.num_gates]['type'] = gate
                self.gate_info[self.num_gates]['level'] = level
                self.gate_info[self.num_gates]['wires'] = wires.split(' ')

                if self.num_levels < level:
                    self.num_levels = level
                if not self.gate_used[gate]:
                    self.gate_used[gate] = 1

    def _helper_let_statements(self, gate_num, gate):
        ret_str = '\t\t\t\t(Gn_%d (%s ' % (gate_num-1, gate['type'])
        for wire in gate['wires'][:-1]:
            mat = re.search(r'(?P<variable>[A-Z]+)(?P<rail>\d+)', wire)
            if mat.group('variable') == 'I':
                ret_str += 'Gc_%d ' % int(mat.group('rail'))
            else:
                ret_str += '(rail%s %s) ' % (mat.group('rail'), mat.group('variable'))
        mat = re.search(r'(?P<variable>[A-Z]+)(?P<rail>\d+)', gate['wires'][-1])
        ret_str += 'Gc_%d))\n' % (gate_num-1)
        return ret_str

    def find_gate_num(self, output):
        ret_gate = [0, 0]
        for gate in self.gate_info:
            mat = re.search(r'(?P<variable>[A-Z]+)(?P<rail>\d+)', self.gate_info[gate]['wires'][-1])
            if mat.group('variable') == output:
                ret_gate[int(mat.group('rail'))] = gate - 1
        return ret_gate


    @property
    def _process_let_statements(self):
        """Temp doc string"""
        ret_str = ''
        for x in range(int(self.num_levels)):
            iter_str = '\n\t\t(let\n\t\t\t(\n'
            for gate_num in self.gate_info:
                if int(self.gate_info[gate_num]['level']) == (x + 1):
                    iter_str += self._helper_let_statements(gate_num, self.gate_info[gate_num])
            iter_str += '\t\t\t)'
            ret_str += iter_str

        iter_str = '\n\t\t(let\n\t\t\t(\n'
        for output in self.outputs:
            output_gates = self.find_gate_num(output.strip())
            iter_str += '\t\t\t\t(%s (concat Gn_%d Gn_%d))\n' % \
                (output.strip(), output_gates[1], output_gates[0])
        iter_str += '\t\t\t)'
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
        return '\n\t\t\t\t'.join('(not (= (_ bv3 2) %s))' % \
            variable.strip() for variable in self.inputs) + '\n'

    @property
    def threshold_gates_null(self):
        """Returns the declaration that each threshold gate current value starts at zero"""
        return '\n\t\t\t\t'.join('(= (_ bv0 1) Gc_%d)' % gate for gate in range(self.num_gates))

    @property
    def one_input_null(self):
        """Returns the check that at least one of the inputs is null"""
        return '\n\t\t\t\t(or\n\t\t\t\t\t' + '\n\t\t\t\t\t'.join('(nullp %s)' % \
            variable.strip() for variable in self.inputs) + '))\n'

    @property
    def one_output_null(self):
        """Returns the declaration that at least one output is null"""
        return '\t\t(or\n\t\t\t' + '\n\t\t\t'.join('(nullp %s)' % \
            variable.strip() for variable in self.outputs) + '))' + (')'*(int(self.num_levels)+1)) + '\n'

    @property
    def implication(self):
        """Returns the implication for the proof"""
        return '\t\t(=>\n\t\t\t(and\n\t\t\t\t%s\t\t\t\t%s\t\t\t\t%s%s' % \
            (self.input_not_invalid, self.threshold_gates_null, self.one_input_null, self.one_output_null)

    @property
    def proof_input_complete_smt2(self):
        """
        Returns the proof for input completeness based on the
        gate level/inputs/outputs of the netlist
        """
        return '; SAT/UNSAT assertion for %s\n' % self.netlist + \
            '(assert\n\t(not%s\n%s\t)\n)' % (self._process_let_statements, self.implication) + '\n'

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
