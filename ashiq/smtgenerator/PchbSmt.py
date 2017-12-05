import os
import re

class PchbSmt():
    """Class used to encapsulate the information to be written to smt file"""
    inputs = None
    outputs = None
    num_gates = 0
    num_levels = 0
    gate_info = dict()

    def __init__(self, netlist, outfile):
        self.netlist = netlist
        self.outfile = outfile
        final_op=''
        self.process_netlist()

    def _prepend_tabs(self, prepend_str, num_tabs=1):
        """Helper function used to clean up code for formatting by prepending tabs to the string"""
        return '\t'*num_tabs + prepend_str

    def process_netlist(self):
        """Process the netlist file to identify inputs, outputs, and gates used"""
        with open(self.netlist, 'r') as netlist_file:
            self.inputs = netlist_file.readline().split(' ')
            self.outputs = netlist_file.readline().split(' ')
            
            for line in netlist_file:
                self.num_gates += 1
                (gate, level, wires) = line.split(' ', 2)
                self.gate_info[self.num_gates] = dict()
                self.gate_info[self.num_gates]['type'] = gate
                self.gate_info[self.num_gates]['level'] = level
                self.gate_info[self.num_gates]['wires'] = wires.split(' ')
                (gate_op, gate_ip) = wires.split(' ', 1)
                self.gate_info[self.num_gates]['gate_op']= gate_op
                self.gate_info[self.num_gates]['gate_ip']= gate_ip.rstrip()
                self.gate_info[self.num_gates]['type_without_number']= self.gate_info[self.num_gates]['type'][:-1]

                if self.num_levels < level:
                    self.num_levels = level

            print self.gate_info[3]['gate_ip']
            
    def helper_let_statements(self, gate_num, gate):
        """used to generate the gate functions of the Pchb_sync netlist"""
        ret_str = self._prepend_tabs('(%s (%s ' % (gate['gate_op'], 'bv'+gate['type_without_number']), 4)
        ret_str += '%s' % gate['gate_ip']+'))'

        return ret_str
    
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
        
        """ writing the specification synchronous function"""
        iter_str = '\n' + self._prepend_tabs('(let\n', 2) + self._prepend_tabs('(\n', 3)
        iter_str += self._prepend_tabs('(%s ' % 'out_sync',4)
        for num_gate in range (self.num_gates,0,-1):
            iter_str +='(bv%s ' % self.gate_info[num_gate]['type_without_number']
            for x in self.gate_info[num_gate]['gate_ip']:
                var=0
                for y in range (1,self.num_gates+1):
                    
                    if x == self.gate_info[y]['gate_op']:
                        var+=1
                if var==0 :
                    iter_str +='%s' %x
                    
                    
        for i in range (1, (int(self.num_levels))+2):
            iter_str +=')'
        iter_str+= self._prepend_tabs('\n)',3)

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
            '\n'.join('(declare-fun %s () (_ BitVec 1))' % \
            variable.strip() for variable in self.inputs) + '\n\n'

    @property
    def outputs_smt2(self):
        """Returns the declarations of the output variable"""
        return '; Outputs: ' + ', '.join(variable.strip() for variable in self.outputs) + '\n' + \
            '\n'.join('(declare-fun %s () (_ BitVec 1))' % \
            variable.strip() for variable in self.outputs) + '\n\n'



    @property
    def implication(self):
        """Returns the implication for the proof"""
        for x in self.outputs:
            final_op = x.rstrip()
        return self._prepend_tabs('(= %s %s )' %(final_op, 'out_sync'), 3)


    @property
    def proof_input_complete_smt2(self):
        """
        Returns the proof for input completeness based on the
        gate level/inputs/outputs of the netlist
        """
        iter_str= ''
        ret_str= ''
        for x in range(1,(self.num_gates+2)):
            iter_str+= ')'
        ret_str+= iter_str
        return '; SAT/UNSAT assertion for %s\n' % self.netlist + \
            '(assert\n' + self._prepend_tabs('(not%s\n%s %s' % \
            (self.process_let_statements,self.implication, ret_str )) + \
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

            smt2_file.write(self.proof_input_complete_smt2)
            smt2_file.write(self.footer_smt2)
