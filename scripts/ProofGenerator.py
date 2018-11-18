import os
import re

import CircuitGraph
import SyncCircuitGraph

import GateNodes
import SyncGateNodes

class ProofGenerator(object):
    required_templates = set(['rail', 'nullp', 'datap'])
    input_re = re.compile('([A-z]+\\d*)_(\\d+)')
    stepped_circuit = False

    def __init__(self, netlist):
        self.circuit_graph = CircuitGraph.CircuitGraph(netlist)
        self.graph = self.circuit_graph.get_graph()
        self.graph_node = self.circuit_graph.get_graph_nodes()
        self.graph_level = self.circuit_graph.get_graph_levels()
        self.sync_circuit_graph = None
        self.sync_graph = None
        self.sync_graph_node = None
        self.sync_graph_level = None

    def generate_smt_proof(self):
        return self.generate_logic_type() + \
        self.generate_input_functions() + \
        self.generate_output_functions() + \
        self.generate_current_gate_functions() + \
        self.generate_required_templates() + \
        self.generate_required_gate_templates() + \
        self.generate_proof_obligation() + \
        self.generate_check_model()

    def generate_logic_type(self):
        return '(set-logic QF_BV)\n'

    def generate_input_functions(self):
        comment = '; Inputs: ' + ' '.join('{0}'.format(i) for i in self.circuit_graph.get_inputs())
        declarations = ''.join('(declare-fun {0} () (_ BitVec 2))\n'.format(i) for i in self.circuit_graph.get_inputs())

        if self.stepped_circuit:
            comment += ' ' + ' '.join('{0}_d'.format(i) for i in self.circuit_graph.get_inputs())
            declarations += ''.join('(declare-fun {0}_d () (_ BitVec 2))\n'.format(i) for i in self.circuit_graph.get_inputs())

        return '\n'.join([comment, declarations])

    def generate_output_functions(self):
        comment = '; Outputs: ' + ' '.join('{0}'.format(o) for o in self.circuit_graph.get_outputs())
        declarations = ''.join('(declare-fun {0} () (_ BitVec 2))\n'.format(o) for o in self.circuit_graph.get_outputs())

        if self.stepped_circuit:
            comment += ' ' + ' '.join('{0}_d'.format(o) for o in self.circuit_graph.get_outputs())
            declarations += ''.join('(declare-fun {0}_d () (_ BitVec 2))\n'.format(o) for o in self.circuit_graph.get_outputs())

        return '\n'.join([comment, declarations])

    def generate_current_gate_functions(self):
        comment = '; Current gate outputs'
        declarations = '(declare-fun Gc_0 () (_ BitVec 1))\n'
        return '\n'.join([comment, declarations])

    def generate_required_templates(self):
        statement = ''
        for template in self.required_templates:
            template_file_name = template + '.smt2'
            with open(os.path.join('..', 'templates', template_file_name), 'r') as template_file:
                statement += template_file.read()
        return statement

    def generate_required_gate_templates(self):
        statement = ''
        for template in self.circuit_graph.get_required_gates():
            template_file_name = template + '.smt2'
            with open(os.path.join('..', 'templates', template_file_name), 'r') as template_file:
                statement += template_file.read()
        return statement

    def generate_proof_obligation(self):
        statement = '(assert\n'
        statement += '(not\n'
        statement += self._generate_let()
        statement += self._generate_implication()

        # Two closing parens for each level if circuit is stepped, else one
        # Then one/two for output let, one for the not, one for the assert
        let_multiplier = 2 if self.stepped_circuit else 1
        if self.sync_circuit_graph.get_num_levels():
            statement += ')\n' * ((self.circuit_graph.get_num_levels() + self.sync_circuit_graph.get_num_levels() + 1) * let_multiplier + 2)
        else:
            statement += ')\n' * ((self.circuit_graph.get_num_levels() + 1) * let_multiplier + 2)
        return statement

    def _generate_let(self):
        return '{0}{1}'.format(self._generate_circuit_let(), self._generate_output_let())

    def _generate_circuit_let(self):
        statement = ''
        for level in self.graph_level.keys():
            statement += '(let\n(\n'
            for gate_output in self.graph_level[level]:
                statement += self._generate_gate_statement(gate_output, 'Gc_0')
            statement += ')\n'
            if self.stepped_circuit:
                statement += '(let\n(\n'
                for gate_output in self.graph_level[level]:
                    statement += self._generate_gate_statement('{0}_d'.format(gate_output), gate_output)
                statement += ')\n'
        return statement

    def _generate_gate_statement(self, gate_output, current_gate_value):
        output = current_gate_value if gate_output.endswith('_d') else gate_output
        statement = '({0} ({1} '.format(gate_output, self.graph[output].get_gate_name().lower())
        for i in self.graph_node[output]:
            if isinstance(self.graph[i], GateNodes.InputNode):
                m = self.input_re.match(i)
                statement += '(rail{0} {1}{2}) '.format(m.group(2), m.group(1), '_d' if gate_output.endswith('_d') else '')
            else:
                statement += '{0}{1} '.format(i, '_d' if gate_output.endswith('_d') else '')
        statement += '{0}))\n'.format(current_gate_value)
        return statement

    def _generate_output_let(self):
        statement = '(let\n(\n'
        for output in self.circuit_graph.get_outputs():
            statement += '({0} (concat {0}_1 {0}_0))\n'.format(output)
        statement += ')\n'

        if self.stepped_circuit:
            statement += '(let\n(\n'
            for output in self.circuit_graph.get_outputs():
                statement += '({0}_d (concat {0}_1_d {0}_0_d))\n'.format(output)
            statement += ')\n'
        return statement

    def _generate_implication(self):
        statement = '(=>\n'
        statement += self._generate_precondition()
        statement += self._generate_postcondition()
        statement += ')\n'
        return statement

    def _generate_precondition(self):
        raise NotImplementedError('Must be implemented in inheriting class.')

    def _generate_postcondition(self):
        raise NotImplementedError('Must be implemented in inheriting class.')

    def generate_check_model(self):
        check_sat = '(check-sat)'
        get_model = '(get-model)'
        return '\n'.join([check_sat, get_model])

    def _generate_condition_inputs_not_illegal(self, d_flag=False):
        inputs = self.circuit_graph.get_inputs()

        statement = ''
        for i in inputs:
            statement += '(not (= (_ bv3 2) {0}{1}))\n'.format(i, '_d' if d_flag else '')
        return statement

    def _generate_condition_inputs_null(self, d_flag=False):
        inputs = self.circuit_graph.get_inputs()

        statement = ''
        for i in inputs:
            statement += '(nullp {0}{1})\n'.format(i, '_d' if d_flag else '')
        return statement

    def _generate_condition_inputs_data(self, d_flag=False):
        inputs = self.circuit_graph.get_inputs()

        statement = ''
        for i in inputs:
            statement += '(datap {0}{1})\n'.format(i, '_d' if d_flag else '')
        return statement

    def _generate_condition_d_inputs_eq_or_null(self):
        inputs = self.circuit_graph.get_inputs()

        statement = ''
        for i in inputs:
            statement += '(or\n'
            statement += '(nullp {0}_d)\n'.format(i)
            statement += '(= {0} {0}_d)\n'.format(i)
            statement += ')\n'
        return statement

    def _generate_condition_current_gate_output_zero(self):
        return '(= (_ bv0 1) Gc_0)\n'

    def _generate_condition_one_input_null(self, d_flag=False):
        inputs = self.circuit_graph.get_inputs()

        statement = '(or\n'
        for i in inputs:
            statement += '(nullp {0}{1})\n'.format(i, '_d' if d_flag else '')
        statement += ')\n'
        return statement

    def _generate_condition_one_input_data(self, d_flag=False):
        inputs = self.circuit_graph.get_inputs()

        statement = ''
        statement += '(or\n'
        for i in inputs:
            statement += '(datap {0}{1})\n'.format(i, '_d' if d_flag else '')
        statement += ')\n'
        return statement

    def _generate_condition_one_output_null(self):
        outputs = self.circuit_graph.get_outputs()

        statement = '(or\n'
        for o in outputs:
            statement += '(nullp {0})\n'.format(o)
        statement += ')\n'
        return statement

    def _generate_condition_one_output_data(self, d_flag=False):
        outputs = self.circuit_graph.get_outputs()

        statement = ''
        statement += '(or\n'
        for o in outputs:
            statement += '(datap {0}{1})\n'.format(o, '_d' if d_flag else '')
        statement += ')\n'
        return statement

    def _generate_condition_outputs_null(self, d_flag=False):
        outputs = self.circuit_graph.get_outputs()
        statement = ''
        for output in outputs:
            statement += '(nullp {0}{1})\n'.format(output, '_d' if d_flag else '')
        return statement

    def _generate_condition_outputs_data(self):
        outputs = self.circuit_graph.get_outputs()
        statement = ''
        for output in outputs:
            statement += '(datap {0})\n'.format(output)
        return statement

    def _generate_condition_proof_gate_function(self, proof_gate):
        statement = ''
        statement += '; Gate function for {0}\n'.format(proof_gate)
        statement += '(= {0} (_ bv1 1))\n'.format(self.graph[proof_gate].evaluate_smt())
        return statement

class InputCompleteN2D(ProofGenerator):
    stepped_circuit = False

    def _generate_precondition(self):
        statement = '(and\n'
        statement += self._generate_condition_inputs_not_illegal()
        statement += self._generate_condition_current_gate_output_zero()
        statement += self._generate_condition_one_input_null()
        statement += ')\n'
        return statement

    def _generate_postcondition(self):
        return self._generate_condition_one_output_null()

class InputCompleteD2N(ProofGenerator):
    stepped_circuit = True

    def _generate_precondition(self):
        statement = '(and\n'
        statement += self._generate_condition_inputs_data()
        statement += self._generate_condition_inputs_not_illegal(d_flag=True)
        statement += self._generate_condition_current_gate_output_zero()
        statement += self._generate_condition_d_inputs_eq_or_null()
        statement += self._generate_condition_one_input_data(d_flag=True)
        statement += ')\n'
        return statement

    def _generate_postcondition(self):
        return self._generate_condition_one_output_data(d_flag=True)

class ObservabilityN2DGate(ProofGenerator):
    stepped_circuit = False

    def __init__(self, netlist, proof_gate):
        super(self.__class__, self).__init__(netlist)
        self.proof_gate = proof_gate

    def _generate_let(self):
        statement = super(self.__class__, self)._generate_let()
        statement_split = statement.split('\n')
        replacement = '(rail{0} {1})'.format(self.proof_gate[-1], self.proof_gate[:2])
        for index, line in enumerate(statement_split):
            if not line.startswith('({0}'.format(self.proof_gate)):
                if self.proof_gate in line:
                    statement_split[index] = line.replace(self.proof_gate, '(_ bv0 1)')
            if isinstance(self.graph[self.proof_gate], GateNodes.InputNode) and replacement in line:
                statement_split[index] = line.replace(replacement, '(_ bv0 1)')
        return '\n'.join(line for line in statement_split)

    def _generate_precondition(self):
        statement = '(and\n'
        statement += self._generate_condition_inputs_data()
        statement += self._generate_condition_proof_gate_function(self.proof_gate)
        statement += self._generate_condition_current_gate_output_zero()
        statement += ')\n'

        return statement

    def _generate_postcondition(self):
        statement = '(not\n(and\n'
        statement += self._generate_condition_outputs_data()
        statement += ')\n)\n'
        return statement

class ObservabilityD2NGate(ProofGenerator):
    stepped_circuit = True

    def __init__(self, netlist, proof_gate):
        super(self.__class__, self).__init__(netlist)
        self.proof_gate = proof_gate

    def _generate_let(self):
        statement = super(self.__class__, self)._generate_let()
        statement_split = statement.split('\n')
        replacement = '(rail{0} {1}_d)'.format(self.proof_gate[-1], self.proof_gate[:2])
        for index, line in enumerate(statement_split):
            if not line.startswith('({0}_d'.format(self.proof_gate)):
                if '{0}_d'.format(self.proof_gate) in line:
                    statement_split[index] = line.replace('{0}_d'.format(self.proof_gate), '(_ bv1 1)')
            if isinstance(self.graph[self.proof_gate], GateNodes.InputNode) and replacement in line:
                statement_split[index] = line.replace(replacement, '(_ bv1 1)')
        return '\n'.join(line for line in statement_split)

    def _generate_precondition(self):
        statement = '(and\n'
        statement += self._generate_condition_inputs_data()
        statement += self._generate_condition_inputs_null(d_flag=True)
        statement += self._generate_condition_proof_gate_function(self.proof_gate)
        statement += self._generate_condition_current_gate_output_zero()
        statement += ')\n'
        return statement

    def _generate_postcondition(self):
        statement = '(not\n(and\n'
        statement += self._generate_condition_outputs_null(d_flag=True)
        statement += ')\n)\n'
        return statement

class Observability:
    def __init__(self, netlist):
        self.netlist = netlist
        self.circuit_graph = CircuitGraph.CircuitGraph(self.netlist)
        self.gate_list = self.circuit_graph.get_graph().keys()

    def get_gate_list(self):
        return self.gate_list

    def generate_n2d_proof(self, gate):
        proof = ObservabilityN2DGate(self.netlist, gate)
        return proof.generate_smt_proof()

    def generate_d2n_proof(self, gate):
        proof = ObservabilityD2NGate(self.netlist, gate)
        return proof.generate_smt_proof()

class Equivalence(ProofGenerator):
    stepped_circuit = False

    def __init__(self, ncl_netlist, sync_netlist):
        super(self.__class__, self).__init__(ncl_netlist)
        self.sync_circuit_graph = SyncCircuitGraph.SyncCircuitGraph(sync_netlist)
        self.sync_graph = self.sync_circuit_graph.get_graph()
        self.sync_graph_node = self.sync_circuit_graph.get_graph_nodes()
        self.sync_graph_level = self.sync_circuit_graph.get_graph_levels()

    def _generate_let(self):
        statement = super(self.__class__, self)._generate_let()
        for level in self.sync_graph_level.keys():
            statement += '(let\n(\n'
            for gate_output in self.sync_graph_level[level]:
                statement += self._generate_sync_gate_statement(gate_output)
            statement += ')\n'
        return statement

    def _generate_sync_gate_statement(self, gate_output):
        my_temp_var = ''
        for i in self.sync_graph_node[gate_output]:
            if isinstance(self.sync_graph[i], SyncGateNodes.InputNode):
                my_temp_var += '(rail1 {0}) '.format(i)
            else:
                my_temp_var += '{0}_sync '.format(i)
        gate_statement = self.sync_graph[gate_output].gate_template.format(my_temp_var.rstrip())
        statement = '({0}_sync {1}) \n'.format(gate_output, gate_statement)
        return statement

    def _generate_precondition(self):
        statement = '(and\n'
        statement += self._generate_condition_inputs_data()
        statement += self._generate_condition_current_gate_output_zero()
        statement += ')\n'
        return statement

    def _generate_postcondition(self):
        statement = '(and\n'
        statement += self._generate_condition_rail1_eq_sync()
        statement += self._generate_condition_rail0_not_rail1()
        statement += ')\n'
        return statement

    def _generate_condition_rail1_eq_sync(self):
        return '\n'.join('(= {0}_1 {0}_sync)'.format(o) for o in self.sync_circuit_graph.get_outputs()) + '\n'

    def _generate_condition_rail0_not_rail1(self):
        return '\n'.join('(not (= {0}_0 {0}_1))'.format(i) for i in self.circuit_graph.get_outputs()) + '\n'