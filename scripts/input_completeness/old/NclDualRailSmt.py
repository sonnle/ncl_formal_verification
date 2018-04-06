import os
import re

class NclDualRailSmt():
    """Class used to encapsulate the information to be written to smt file"""
    gate_used = {'th12'     : 0, 'th13'     : 0, 'th14'     : 0,
                 'th22'     : 0, 'th23'     : 0, 'th23w2'   : 0,
                 'th24'     : 0, 'th24comp' : 0, 'th24w2'   : 0,
                 'th24w22'  : 0, 'th33'     : 0, 'th33w2'   : 0,
                 'th34'     : 0, 'th34w2'   : 0, 'th34w22'  : 0,
                 'th34w3'   : 0, 'th34w32'  : 0, 'th44'     : 0,
                 'th44w2'   : 0, 'th44w22'  : 0, 'th44w3'   : 0,
                 'th44w322' : 0, 'th54w22'  : 0, 'th54w32'  : 0,
                 'th54w322' : 0, 'thand0'   : 0, 'thxor0'   : 0,
                 'ha'       : 0, 'fa'       : 0, 'and'      : 0,}
    inputs = None
    outputs = None
    num_gates = 0
    num_levels = 0
    gate_info = dict()
    print_lines = []

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
                if gate == 'and':
                    self.num_gates += 2
                    self.gate_used['th22'] = 1
                    self.gate_used['thand0'] = 1
                elif gate == 'ha':
                    self.num_gates += 4
                    self.gate_used['th12'] = 1
                    self.gate_used['th22'] = 1
                    self.gate_used['th24comp'] = 1
                elif gate == 'fa':
                    self.num_gates += 4
                    self.gate_used['th23'] = 1
                    self.gate_used['th34w2'] = 1
                else:
                    self.num_gates += 1
                    self.gate_used[gate] = 1

                self.gate_info[self.num_gates] = dict()
                self.gate_info[self.num_gates]['type'] = gate
                self.gate_info[self.num_gates]['level'] = level
                self.gate_info[self.num_gates]['wires'] = wires.split(' ')

                if self.num_levels < int(level):
                    self.num_levels = int(level)

    def helper_let_statements(self, gate_num, gate):
        ret_str = '(Gn_%d (%s ' % (gate_num-1, gate['type'])
        for wire in gate['wires'][:-1]:
            mat = re.search(r'(?P<variable>[A-z]+)', wire)
            if mat.group('variable') == 'I':
                ret_str += 'Gc_%s ' % wire[1:]
            else:
                ret_str += wire + ' '
        mat = re.search(r'(?P<variable>[A-z]+)', gate['wires'][-1])
        ret_str += 'Gc_%d))\n' % (gate_num-1)
        self.print_lines.append(ret_str)

    def find_gate_num(self, output):
        ret_gate = ''
        for gate in self.gate_info:
            ret_gate =  self.gate_info[gate]['wires'][-1]
        return ret_gate

    @property
    def process_let_statements(self):
        for level in range(int(self.num_levels)):
            self.print_lines.append('(let\n')
            iter_str = self._prepend_tabs('\n', 2) + self._prepend_tabs('(let\n', 2) + self._prepend_tabs('(\n', 3)
            for gate_num in self.gate_info:
                if int(self.gate_info[gate_num]['level']) == (level + 1):
                    self.helper_let_statements(gate_num, self.gate_info[gate_num])
            self.print_lines.append(')\n')

        self.print_lines.append('(let\n')
        for output in self.outputs:
            output_gates = self.find_gate_num(output.strip())
            self.print_lines.append('(%s (concat Gn_%s Gn_%s))\n' % (output.strip(), output_gates[1], output_gates[0]))
        self.print_lines.append(')')

    @property
    def heading_smt2(self):
        """Returns the heading for smt2 file"""
        self.print_lines.append('; Formal verification proof - input completeness of %s\n' % self.netlist)

    @property
    def logic_smt2(self):
        """Returns bit-vector logic, could be changed to accept different logics"""
        self.print_lines.append('(set-logic QF_BV)\n\n')

    @property
    def inputs_smt2(self):
        """Returns the declarations of the input variables"""
        self.print_lines.append('; Inputs: ' + ', '.join(variable.strip() for variable in self.inputs) + '\n')
        for variable in self.inputs:
            self.print_lines.append('(declare-fun %s () (_ BitVec 2))\n' % variable.strip())
        self.print_lines.append('\n')

    @property
    def outputs_smt2(self):
        """Returns the declarations of the output variable"""
        self.print_lines.append('; Outputs: ' + ', '.join(variable.strip() for variable in self.outputs) + '\n')
        for variable in self.outputs:
            self.print_lines.append('(declare-fun %s () (_ BitVec 2))\n' % variable.strip())
        self.print_lines.append('\n')

    def template_smt2(self, file_name):
        """Returns what is read from the template file"""
        with open(os.path.join('..', '..', 'templates', file_name), 'r') as temp_file:
            self.print_lines.append(temp_file.read() + '\n')

    @property
    def gate_current_smt2(self):
        """Returns the declarations of the current state of the threshold gates"""
        self.print_lines.append('; Current values of threshold gates\n')
        for num in range(self.num_gates):
            self.print_lines.append('(declare-fun Gc_%d () (_ BitVec 1))\n' % num)
        self.print_lines.append('\n')

    @property
    def input_not_invalid(self):
        """Returns the declarations that each input is not invalid"""
        for variable in self.inputs:
            self.print_lines.append('(not (= (_ bv3 2) %s))\n' % variable.strip())

    @property
    def threshold_gates_null(self):
        """Returns the declaration that each threshold gate current value starts at zero"""
        for gate in range(self.num_gates):
            self.print_lines.append('(= (_ bv0 1) Gc_%d)\n' % gate)

    @property
    def one_input_null(self):
        """Returns the check that at least one of the inputs is null"""
        self.print_lines.append('(or\n')
        for variable in self.inputs:
            self.print_lines.append('(nullp %s)\n' % variable.strip())

    @property
    def one_output_null(self):
        """Returns the declaration that at least one output is null"""
        self.print_lines.append('(or\n')
        for variable in self.outputs:
            self.print_lines.append('(nullp %s)\n' % variable.strip())
        self.print_lines.append('))' + ')'*(int(self.num_levels) + 1) + '\n')

    @property
    def implication(self):
        """Returns the implication for the proof"""
        self.print_lines.append('(=>\n')
        self.print_lines.append('(and\n')
        self.input_not_invalid
        self.threshold_gates_null
        self.one_input_null
        self.one_output_null

    @property
    def proof_input_complete_smt2(self):
        """
        Returns the proof for input completeness based on the
        gate level/inputs/outputs of the netlist
        """
        self.print_lines.append('; SAT/UNSAT assertion for %s\n' % self.netlist)
        self.print_lines.append('(assert\n')
        self.print_lines.append('(not\n')
        self.process_let_statements
        self.implication

    @property
    def footer_smt2(self):
        """Returns the check-sat and get-model method calls"""
        self.print_lines.append('(check-sat)\n')
        self.print_lines.append('(get-model)\n')

    def generate_smt2(self):
        """Generate the final smt2 file to the output file"""
        self.heading_smt2
        self.logic_smt2
        self.inputs_smt2
        self.outputs_smt2
        for file_name in ['rail.smt2', 'nullp.smt2']:
            self.template_smt2(file_name)

        for gate in self.gate_used:
            if self.gate_used[gate]:
                gate_template_file = '%s.smt2' % gate
                self.template_smt2(gate_template_file)

        self.gate_current_smt2
        self.proof_input_complete_smt2
        self.footer_smt2

        with open(self.outfile, 'w') as w_file:
            for line in self.print_lines:
                w_file.write(line)
