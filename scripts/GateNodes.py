import re
import gc

"""
Exception used to catch invalid number of inputs when creating nodes.
"""
class IncorrectNumInputsException(Exception):
    def __init__(self, num_got, num_exp):
        Exception.__init__(self, 'Incorrect number of inputs. Got %d, Expected %d.\n' % (num_got, num_exp))


"""
Generic class used to represent a single node.
"""
class GateNode:
    num_inputs_required = 0
    gate_name = None
    def __init__(self, inputs):
        if len(inputs) != self.num_inputs_required:
            raise IncorrectNumInputsException(len(inputs), self.num_inputs_required)
        else:
            self.inputs = inputs

    def evaluate_smt(self):
        raise NotImplementedError()

    def get_input(self, input_num):
        if input_num < self.num_inputs_required:
            return self.inputs[input_num]

    def set_input(self, input_num, input_val):
        if input_num < self.num_inputs_required:
            self.inputs[input_num] = input_val

    def get_gate_name(self):
        return self.gate_name


"""
Generic classes used to represent NCL gates with X variable inputs.
"""
class TwoVariableNode(GateNode):
    num_inputs_required = 2
    def evaluate_smt(self):
        gc.collect()
        return self.gate_template.format(self.inputs[0].evaluate_smt(), self.inputs[1].evaluate_smt())

class ThreeVariableNode(GateNode):
    num_inputs_required = 3
    def evaluate_smt(self):
        gc.collect()
        return self.gate_template.format(self.inputs[0].evaluate_smt(), self.inputs[1].evaluate_smt(), self.inputs[2].evaluate_smt())

class FourVariableNode(GateNode):
    num_inputs_required = 4
    def evaluate_smt(self):
        gc.collect()
        return self.gate_template.format(self.inputs[0].evaluate_smt(), self.inputs[1].evaluate_smt(), self.inputs[2].evaluate_smt(), self.inputs[3].evaluate_smt())


"""
Explicit class used to represent inputs of circuit.
"""
class InputNode(GateNode):
    num_inputs_required = 1
    gate_name = 'Input'
    def evaluate_smt(self):
        m = re.search('([A-z]+\d*)_(\d+)', self.inputs[0])
        return '(rail{0} {1})'.format(m.group(2), m.group(1))


"""
Explicit classes used to represent NCL gates with
two variable inputs.
"""
class Th12Node(TwoVariableNode):
    gate_name = 'Th12'
    gate_template = '(bvor {0} {1})'

class Th22Node(TwoVariableNode):
    gate_name = 'Th22'
    gate_template = '(bvand {0} {1})'


"""
Explicit classes used to represent NCL gates with
three variable inputs and no weighting.
"""
class Th13Node(ThreeVariableNode):
    gate_name = 'Th13'
    gate_template = '(bvor {0} {1} {2})'

class Th23Node(ThreeVariableNode):
    gate_name = 'Th23'
    gate_template = '(bvor (bvand {0} {1}) (bvand {0} {2}) (bvand {1} {2}))'

class Th33Node(ThreeVariableNode):
    gate_name = 'Th33'
    gate_template = '(bvand {0} {1} {2})'


"""
Explicit classes used to represent NCL gates with
three variable inputs with w2 weighting.
"""
class Th23w2Node(ThreeVariableNode):
    gate_name = 'Th23w2'
    gate_template = '(bvor {0} (bvand {1} {2}))'

class Th33w2Node(ThreeVariableNode):
    gate_name = 'Th33w2'
    gate_template = '(bvor (bvand {0} {1}) (bvand {0} {2}))'


"""
Explicit classes used to represent NCL gates with
four variable inputs and no weighting.
"""
class Th14Node(FourVariableNode):
    gate_name = 'Th14'
    gate_template = '(bvor {0} {1} {2} {3})'

class Th24Node(FourVariableNode):
    gate_name = 'Th24'
    gate_template = '(bvor (bvand {0} {1}) (bvand {0} {2}) (bvand {0} {3}) (bvand {1} {2}) (bvand {1} {3}) (bvand {2} {3}))'

class Th34Node(FourVariableNode):
    gate_name = 'Th34'
    gate_template = '(bvor (bvand {0} {1} {2}) (bvand {0} {1} {3}) (bvand {0} {2} {3}) (bvand {1} {2} {3}))'

class Th44Node(FourVariableNode):
    gate_name = 'Th44'
    gate_template = '(bvand {0} {1} {2} {3})'


"""
Explicit classes used to represent NCL gates with
four variable inputs with w2 weighting.
"""
class Th24w2Node(FourVariableNode):
    gate_name = 'Th24w2'
    gate_template = '(bvor {0} (bvand {1} {2}) (bvand {1} {3}) (bvand {2} {3}))'

class Th34w2Node(FourVariableNode):
    gate_name = 'Th34w2'
    gate_template = '(bvor (bvand {0} {1}) (bvand {0} {2}) (bvand {0} {3}) (bvand {1} {2} {3}))'

class Th44w2Node(FourVariableNode):
    gate_name = 'Th44w2'
    gate_template = '(bvor (bvand {0} {1} {2}) (bvand {0} {1} {3}) (bvand {1} {2} {3}))'


"""
Explicit classes used to represent NCL gates with
four variable inputs with w3 weighting.
"""
class Th34w3Node(FourVariableNode):
    gate_name = 'Th34w3'
    gate_template = '(bvor {0} (bvand {1} {2} {3}))'

class Th44w3Node(FourVariableNode):
    gate_name = 'Th44w3'
    gate_template = '(bvor (bvand {0} {1}) (bvand {0} {2}) (bvand {0} {3}))'


"""
Explicit classes used to represent NCL gates with
four variable inputs with w22 weighting.
"""
class Th24w22Node(FourVariableNode):
    gate_name = 'Th24w22'
    gate_template = '(bvor {0} {1} (bvand {2} {3}))'

class Th34w22Node(FourVariableNode):
    gate_name = 'Th34w22'
    gate_template = '(bvor (bvand {0} {1}) (bvand {0} {2}) (bvand {0} {3}) (bvand {1} {2}) (bvand {1} {3}))'

class Th44w22Node(FourVariableNode):
    gate_name = 'Th44w22'
    gate_template = '(bvor (bvand {0} {1}) (bvand {0} {2} {3}) (bvand {1} {2} {3}))'

class Th54w22Node(FourVariableNode):
    gate_name = 'Th54w22'
    gate_template = '(bvor (bvand {0} {1} {2}) (bvand {0} {1} {3}))'


"""
Explicit classes used to represent NCL gates with
four variable inputs with w32 weighting.
"""
class Th34w32Node(FourVariableNode):
    gate_name = 'Th34w32'
    gate_template = '(bvor {0} (bvand {1} {2}) (bvand {1} {3}))'

class Th54w32Node(FourVariableNode):
    gate_name = 'Th54w32'
    gate_template = '(bvor (bvand {0} {1}) (bvand {0} {2} {3}))'


"""
Explicit classes used to represent NCL gates with
four variable inputs with w322 weighting.
"""
class Th44w322Node(FourVariableNode):
    gate_name = 'Th44w322'
    gate_template = '(bvor (bvand {0} {1}) (bvand {0} {2}) (bvand {0} {3}) (bvand {1} {2}))'

class Th54w322Node(FourVariableNode):
    gate_name = 'Th54w322'
    gate_template = '(bvor (bvand {0} {1}) (bvand {0} {2}) (bvand {1} {2} {3}))'


"""
Explicit classes used to represent NCL gates with
four variable inputs with special weighting.
"""
class Thxor0Node(FourVariableNode):
    gate_name = 'Thxor0'
    gate_template = '(bvor (bvand {0} {1}) (bvand {2} {3}))'

class Thand0Node(FourVariableNode):
    gate_name = 'Thand0'
    gate_template = '(bvor (bvand {0} {1}) (bvand {1} {2}) (bvand {0} {3}))'

class Th24compNode(FourVariableNode):
    gate_name = 'Th24comp'
    gate_template = '(bvor (bvand {0} {2}) (bvand {1} {2}) (bvand {0} {3}) (bvand {1} {3}))'

