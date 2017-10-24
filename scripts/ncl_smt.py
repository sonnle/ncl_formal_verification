import os

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
                self.gate_info[self.num_gates]['level'] = level
                self.gate_info[self.num_gates]['wires'] = wires.split(' ')

                if self.num_levels < level:
                    self.num_levels = level
                if not self.gate_used[gate]:
                    self.gate_used[gate] = 1

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
    def let_statements(self):
        """Returns the assignments of the wires to the correct gate function call"""
        return ''

    @property
    def input_not_invalid(self):
        """Returns the declarations that each input is not invalid"""
        return '\n\t\t\t\t'.join('(not (= (_ bv3 2) %s))' % \
            variable.strip() for variable in self.inputs) + '\n'

    @property
    def threshold_gates_null(self):
        """Returns the declaration that each threshold gate current value starts at zero"""
        return '\n\t\t\t\t'.join('(nullp Gc_%d)' % gate for gate in range(self.num_gates))

    @property
    def one_input_null(self):
        """Returns the check that at least one of the inputs is null"""
        return '\n\t\t\t\t(or\n\t\t\t\t\t' + '\n\t\t\t\t\t'.join('(nullp %s)' % \
            variable.strip() for variable in self.inputs) + '))\n'

    @property
    def one_output_null(self):
        """Returns the declaration that at least one output is null"""
        return '\t\t(or\n\t\t\t' + '\n\t\t\t'.join('(nullp %s)' % \
            variable.strip() for variable in self.outputs) + '))\n'

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
            '(assert\n\t(not\n%s\n%s\t)\n)' % (self.let_statements, self.implication) + '\n'

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
