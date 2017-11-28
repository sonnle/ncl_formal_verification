import os
import re
import networkx as nx

class PchbSync():

    inputs = []
    outputs = []
    num_gates = 0
    num_levels = 0
    gate_inputs_number= 0
    gate_info = dict()
    graph_info= dict()
    

    def __init__(self, netlist, outfile,outfile1,outfile2):
        self.netlist = netlist
        self.outfile = outfile
        self.outfile1 = outfile1
        self.outfile2 = outfile2
        self._process_netlist()

    def _process_netlist(self):
        """Process the netlist file to identify inputs, outputs, and gates used"""
        with open(self.netlist, 'r') as netlist_file:
            var= netlist_file.readline().split(',')
            for x in var:
                mat= re.search (r'(?P<variable>[A-z]+)_.*',x)
                m= mat.group('variable')
                self.inputs.append(m)
            start= self.inputs    
            self.graph_info = dict()
            self.graph_info['start_children'] = start
            self.graph_info['start_parent'] = []
#            print self.inputs
            var= netlist_file.readline().split(',')
            for x in var:
                mat= re.search (r'(?P<variable>[A-z]+)_.*',x)
                m= mat.group('variable')
                self.outputs.append(m)
            self.graph_info['terminate_parent'] = self.outputs
            self.graph_info['terminate_children'] = []
#            print self.graph_info
#            print self.outputs
          
            for line in netlist_file:
                self.num_gates += 1
                (gate, level,others) = line.split(' ',2)
                self.gate_info[self.num_gates] = dict()
                self.gate_info[self.num_gates]['type'] = gate

                self.gate_info[self.num_gates]['gate_inputs_number'] = [item [-1:] for item in gate.split(',')]
                self.gate_info[self.num_gates]['type_without_number']= [item [:-1] for item in gate.split(',')]

                self.gate_info[self.num_gates]['level'] = level
#                self.gate_info[self.num_gates]['others'] = others
                self.gate_info[self.num_gates]['P']= list()
#                self.gate_info[self.num_gates]['gate_inputs_number'] = [item [-1:] for item in gate.split(',')]
                (gate_inputs, rack, lack, gate_op)= others.split(' ',3)
                self.gate_info[self.num_gates]['gate_inputs'] = gate_inputs
#                print gate_op.split(',')
                self.gate_info[self.num_gates]['gate_outputs'] = gate_op
                self.gate_info[self.num_gates]['Rack'] = rack
                self.gate_info[self.num_gates]['Lack'] = lack
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
#                print self.gate_info[self.num_gates]['P']
                var= gate_op.split(',')
#                print var
#                for y in var:
#                    mat= re.search (r'(?P<variables>[1-9]+)_.*',y)
#                    m= mat.group ('variables')
#                    print m 
                self.gate_info[self.num_gates]['output1'] = [item[0] for item in var]
#            print self.num_gates        
            self.graph_info['num_nodes']=0
            for x in range(1,self.num_gates+1):
                
                self.graph_info['node'+ str(x)]= self.gate_info[x]['type']
                var= self.gate_info[x]['gate_inputs'].split(',')
                self.graph_info['node'+str(x)+'_inputs']=[]
                for y in var:
                     mat= re.search (r'(?P<variable>[A-z]+)_.*',y)
                     m= mat.group('variable')
                     self.graph_info['node'+str(x)+'_inputs'].append(m)
                
                self.graph_info['node'+str(x)+'_outputs']=[]
                var_o= self.gate_info[x]['gate_outputs'].split(',') 
#                print var_o
                for z in var_o:
                    mat1= re.search (r'(?P<variable>[A-z]+)_.*',z)
                    n= mat1.group('variable')
                    self.graph_info['node'+str(x)+'_outputs'].append(n)
                
                self.graph_info['node'+str(x)+'_Rack']=[]
                var_rack= self.gate_info[x]['Rack'].split(',') 
                for z in var_rack:
                    self.graph_info['node'+str(x)+'_Rack'].append(z)
                    
                self.graph_info['node'+str(x)+'_Lack']=[]
                var_lack= self.gate_info[x]['Lack'].split(',') 
                for z in var_lack:
                    self.graph_info['node'+str(x)+'_Lack'].append(z) 
                self.graph_info['num_nodes']+=1
            print self.graph_info
#                
    def connection_file(self): 
        with open(self.outfile1, 'w') as smt2_file:
            num_nodes= self.graph_info['num_nodes']
            
            for i in range(1,num_nodes):
               if all(element in self.graph_info['node'+str(num_nodes)+'_inputs'] for element in self.graph_info['node'+str(i)+'_outputs'] ):
                   smt2_file.write ("Output of " + 'node'+str(i) + " is connected to the Input of " + 'node'+str(num_nodes)+ '\n')
                   if self.graph_info['node'+str(num_nodes)+'_Lack'] == self.graph_info['node'+str(i)+'_Rack']:
                       smt2_file.write ("NO error in Connection between   " + 'node'+str(i) + ' ' + 'and'+ ' '+ 'node'+ str(num_nodes) + '\n')
                   else:
                       smt2_file.write ("HANDSHAKING Connection ERROR! between " 'node'+str(i) + ' '+'and'+' ' + 'node'+ str(num_nodes)+ '\n')
#               else:
#                   smt2_file.write ("Output of " + 'node'+str(i) + " is not connected to the Input of " + 'node'+str(num_nodes) + '\n') 
               
               if all(element in self.graph_info['node'+str(num_nodes-i)+'_inputs'] for element in self.graph_info['node'+str(i)+'_outputs'] ):
                   smt2_file.write ("Output of " + 'node'+str(i) + " is connected to the input of " + 'node'+str(num_nodes-i) + '\n')
                   if self.graph_info['node'+str(num_nodes-i)+'_Lack'] == self.graph_info['node'+str(i)+'_Rack']:
                       smt2_file.write ("No error in Connection between " 'node'+str(i) + ' '+'and'+' ' + 'node'+ str(num_nodes-i)+ '\n')
                   else:
                       smt2_file.write ("HANDSHAKING Connection ERROR! between " 'node'+str(i) + ' '+'and'+' ' + 'node'+ str(num_nodes-i)+ '\n')
               else:
#                   smt2_file.write ("Output of " + 'node'+str(i) + " is not connected to the Input of " + 'node'+str(num_nodes-i) + '\n') 
                   smt2_file.write ('\n'+ 'No other interconnections exist \n')
                   
    def graph_structure(self):
        with open(self.outfile2, 'w') as smt2_file:
            num_nodes= self.graph_info['num_nodes']
            smt2_file.write ( 'Graph structure:{' + '\n' + 'START: ' + 'START_parent:' + ' ' + '[ '+' '.join(variable.strip() for variable in self.graph_info['start_parent']) +' ]' + ':::  ' + 'START_children:'+ '[ ' + ' '.join(variable.strip() for variable in self.graph_info['start_children']) + ' ]'+ '\n')
            for x in range (1,num_nodes+1):
                smt2_file.write ('node'+str(x)+': ' +  self.graph_info['node'+ str(x)]+ ' ::: ' + 'node'+str(x)+'_parents: ' + '[ '+' '.join(variable.strip() for variable in self.graph_info['node'+str(x)+'_inputs'])  + ' '+  ' '.join(variable.strip() for variable in self.graph_info['node'+str(x)+'_Rack']) + ' ]' + ' ::: ' + 'node'+str(x)+'_children: ' + '[ '+ ' '.join(variable.strip() for variable in self.graph_info['node'+str(x)+'_outputs']) + ' '+ ' '.join(variable.strip() for variable in self.graph_info['node'+str(x)+'_Lack']) +' ]'+  '\n')
            smt2_file.write ('Terminate: ' + 'terminate_parent:' + ' ' + '[ '+' '.join(variable.strip() for variable in self.graph_info['terminate_parent']) +' ]' + ':::  ' + 'terminate_children:'+ '[ ' + ' '.join(variable.strip() for variable in self.graph_info['terminate_children']) + ' ]'+ '\n' + '}' ) 
            
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
        return 'gate_struct:' + ' '+ (self.gate_info[x]['type']) +' ' + (self.gate_info[x]['level']) + ' '  + ' '.join(variable.strip() for variable in self.gate_info[x]['output1']) + ' ' + ' '.join(variable.strip() for variable in self.gate_info[x]['P']) + '\n' 
                  
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
    

