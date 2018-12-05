import re

class SyncGateNode(object):
    gate_name = None
    def __init__(self, inputs):
        self.inputs = inputs

    def evaluate_smt(self):
        raise NotImplementedError()

    def get_inputs(self):
        return self.inputs

    def get_input(self, input_num):
        return self.inputs[input_num]

    def set_input(self, input_num, input_val):
        self.inputs[input_num] = input_val

    def get_gate_name(self):
        return self.gate_name

class BooleanGateNode(SyncGateNode):
    gate_name = 'BooleanGate'
    gate_template = None
    def evaluate_smt(self):
        return self.gate_template.format(' '.join(i.evaluate_smt() for i in self.inputs))

class InputNode(SyncGateNode):
    gate_name = 'Input'
    def evaluate_smt(self):
        return '(rail1 {0})'.format(self.inputs[0])

class ANDNode(BooleanGateNode):
    gate_name = 'AND'
    gate_template = '(bvand {0})'

class ORNode(BooleanGateNode):
    gate_name = 'OR'
    gate_template = '(bvor {0})'

class XORNode(BooleanGateNode):
    gate_name = 'XOR'
    gate_template = '(bvxor {0})'

class NOTNode(BooleanGateNode):
    gate_name = 'NOT'
    gate_template = '(bvnot {0})'

class NORNode(BooleanGateNode):
    gate_name = 'NOR'
    gate_template = '(bvnor {0})'

class NANDNode(BooleanGateNode):
    gate_name = 'NAND'
    gate_template = '(bvnand {0})'
