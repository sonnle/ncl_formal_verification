import os
import re

class PchbSync():

    inputs = []
    outputs = []
    num_gates = 0
    num_levels = 0
    gate_inputs_number= 0
    gate_info = dict()
    

    def __init__(self, netlist, outfile):
        self.netlist = netlist
        self.outfile = outfile
        self._process_netlist()

    def _process_netlist(self):
        """Process the netlist file to identify inputs, outputs, and gates used"""
        with open(self.netlist, 'r') as netlist_file:
#            self.inputs = netlist_file.readline().split(',')
            
#            self.inputs = [item[0:2] for item in netlist_file.readline().\
#            split(',')]
            var= netlist_file.readline().split(',')
            for x in var:
                print x
                mat= re.search (r'(?P<variable>[1-9]+)_*',x)
                m= mat.group('variable')
                self.inputs.append(m)
            self.outputs = [item[0:2] for item in netlist_file.readline().\
            split(',')]
          
            for line in netlist_file:
                self.num_gates += 1
                (gate, level,others) = line.split(' ',2)
                self.gate_info[self.num_gates] = dict()
                self.gate_info[self.num_gates]['type'] = gate
                self.gate_info[self.num_gates]['gate_inputs_number'] = [item [-1:] for item in gate.split(',')]
                self.gate_info[self.num_gates]['type_without_number']= [item [:-1] for item in gate.split(',')]
                if self.gate_info[self.num_gates]['type_without_number']== ['and']:
                    self.gate_info[self.num_gates]['type']= '1'
                elif self.gate_info[self.num_gates]['type_without_number']== ['or']:
                    self.gate_info[self.num_gates]['type']= '2'
                elif self.gate_info[self.num_gates]['type_without_number']== ['not']:
                    self.gate_info[self.num_gates]['type']= '3'
                elif self.gate_info[self.num_gates]['type_without_number']== ['nand']:
                    self.gate_info[self.num_gates]['type']= '4'
                elif self.gate_info[self.num_gates]['type_without_number']== ['nor']:
                    self.gate_info[self.num_gates]['type']= '5'
                elif self.gate_info[self.num_gates]['type_without_number']== ['xnor']:
                    self.gate_info[self.num_gates]['type']= '6'
                elif self.gate_info[self.num_gates]['type_without_number']== ['xor']:
                    self.gate_info[self.num_gates]['type']= '7'
                else:
                    self.gate_info[self.num_gates]['type']= 'gate_not_found'
                self.gate_info[self.num_gates]['level'] = level
#                self.gate_info[self.num_gates]['others'] = others
                self.gate_info[self.num_gates]['P']= list()
#                self.gate_info[self.num_gates]['gate_inputs_number'] = [item [-1:] for item in gate.split(',')]
                (gate_inputs, rack, lack, gate_op)= others.split(' ',3)
#                self.gate_info[self.num_gates]['gate_inputs'] = gate_inputs
                self.gate_inputs_number = self.gate_info[self.num_gates]['gate_inputs_number']
                self.gate_inputs_number = [int(i) for i in self.gate_inputs_number]
#                print self.gate_inputs_number
                temp=0
                
                for x in range (1,(self.gate_inputs_number[0]+1)):
                    while (temp<x):
                        string1 = 'input'+ str(x)
                        self.gate_info[self.num_gates][string1] = [item[0] for item in gate_inputs.split(',')][x-1]
                        self.gate_info[self.num_gates]['P'].extend([self.gate_info[self.num_gates][string1]])
                        temp+= 1
                var= gate_op.split(',') 
#                print var
#                mat= re.search (r'(?P<variable>[1-9]+)_1',var)
#                m= mat.group('variable)
#                print 
                self.gate_info[self.num_gates]['output1'] = [item[0] for item in var]

    @property
    def heading_file(self):
        """Returns the heading for output file"""
        return 'PCHB to Synchronous converted Netlist\n'+ '\n'
      
    @property
    def inputs_sync(self):
        """Returns the declarations of the input variables"""
        return 'Inputs:'+ ' '+ ' '.join(variable.strip() for variable in self.inputs) + '\n' 
#
    @property
    def outputs_sync(self):
        """Returns the declarations of the output variable"""
        return 'Outputs:'+ ' ' + ' '.join(variable.strip() for variable in self.outputs) + '\n' 
    
    def gate_struc(self,x):
        """Returns the declarations of the gate variables"""
        return 'gate_struct:' + ' '+ (self.gate_info[x]['type']) +' ' + (self.gate_info[x]['level']) + ' ' +' '.join(variable.strip() for variable in self.gate_info[x]['P']) + ' ' + ' ' + ' '.join(variable.strip() for variable in self.gate_info[x]['output1'])+ '\n' 
                  
    @property
    def footer_smt2(self):
        """conversion done"""
        return '\nNetlist conversion done \n'
#
    def generate_pchbtosyn(self):
        """Generate the final smt2 file to the output file"""
        with open(self.outfile, 'w') as smt2_file:
            smt2_file.write(self.heading_file)
##
            smt2_file.write(self.inputs_sync)
            smt2_file.write(self.outputs_sync)
             
            for x in range (1, self.num_gates+1):
                smt2_file.write(self.gate_struc(x))

            smt2_file.write(self.footer_smt2)
