import UMultProof

class UMultProofData(UMultProof.UMultProof):
    and2_str = 'and2'
    and2_incomplete_str = 'and2_incomplete'
    ha_str = 'ha'
    fa_str = 'fa'

    gc_0 = 'Gc_0'
    extract32 = '(_ extract 3 2)'
    extract10 = '(_ extract 1 0)'
    rail1 = 'rail1'
    rail0 = 'rail0'

    bug_bit = None

    partial_products_d = dict()

    def __init__(self, bits):
        super(UMultProofData, self).__init__(bits)
        self.required_gate_templates = ['th34w2', 'th24comp', 'th22', 'th23', 'th12', 'thand0', 'and2', 'and2_incomplete', 'ha', 'fa']

    def generate_proof_obligation(self):
        statement = self._generate_assert()

        return statement

    def generate_input_functions(self):
        comment = '; Inputs: '
        comment_d = '; Data Inputs: '
        declarations = ''
        declarations_d = ''

        for i in range(self.bits):
            comment += 'X{0} '.format(i)
            comment += 'Y{0} '.format(i)
            comment_d += 'X{0}_d '.format(i)
            comment_d += 'Y{0}_d '.format(i)
            declarations += '(declare-fun X{0} () (_ BitVec 2))\n'.format(i)
            declarations_d += '(declare-fun X{0}_d () (_ BitVec 2))\n'.format(i)
            declarations += '(declare-fun Y{0} () (_ BitVec 2))\n'.format(i)
            declarations_d += '(declare-fun Y{0}_d () (_ BitVec 2))\n'.format(i)

        statement = comment + '\n' + declarations + '\n' + comment_d + '\n' + declarations_d

        return statement

    def _generate_assert(self):
        statement = ''
        statement += '(assert\n'
        statement += self._generate_not()
        statement += ')\n'

        return statement

    def _generate_not(self):
        statement = ''
        statement += '(not\n'
        statement += self._generate_and_let()
        statement += self._generate_adder_let()
        statement += self._generate_and_d_let()
        statement += self._generate_adder_d_let()
        statement += self._generate_output_d_let()

        statement += self._generate_implication()

        # Two for each level, then an extra for the let_outputs
        statement += ')\n'*(self.num_let)

        # Another extra for the closing of the not
        statement += ')\n'

        return statement

    def _generate_and_let(self):
        statement = ''
        statement += '(let\n'
        statement += '(\n'
        self.num_let += 1
        for row in range(self.bits):
            for column in range(self.bits):
                index = row + column
                if row != column or row == self.bug_bit:
                    statement += '(and{0}x{1} ({2} X{0} Y{1} {3} {3}))\n'.format(row, column, self.and2_incomplete_str, self.gc_0)
                else:
                    statement += '(and{0}x{1} ({2} X{0} Y{1} {3} {3}))\n'.format(row, column, self.and2_str, self.gc_0)
                try:
                    self.partial_products[index].append('and{0}x{1}'.format(row,column))
                except KeyError:
                    self.partial_products[index] = ['and{0}x{1}'.format(row, column)]
        statement += ')\n'

        return statement

    def _generate_adder_let(self):
        statement = ''
        statement += '(let\n'
        statement += '(\n'
        statement += '(S0x0 {0})\n'.format(self.partial_products[0].pop())
        statement += ')\n'
        self.num_let += 1

        for row in range(self.bits):
            for column in range(self.bits - 1):
                statement += '(let\n'
                statement += '(\n'
                self.num_let += 1
                index = row + column
                if row == 0:
                    val1 = self.partial_products[index + 1].pop()
                    val2 = self.partial_products[index + 1].pop()
                    if column == 0:
                        statement += '(S{0}x{1} ({2} ({3} {4} {5} {6} {6} {6} {6})))\n'.format(row+1, index+1, self.extract32, self.ha_str, val1, val2, self.gc_0)
                        statement += '(C{0}x{1} ({2} ({3} {4} {5} {6} {6} {6} {6})))\n'.format(row+1, index+1, self.extract10, self.ha_str, val1, val2, self.gc_0)
                    else:
                        statement += '(S{0}x{1} ({2} ({3} {4} {5} C{0}x{6} {7} {7} {7} {7})))\n'.format(row+1, index+1, self.extract32, self.fa_str, val1, val2, index, self.gc_0)
                        statement += '(C{0}x{1} ({2} ({3} {4} {5} C{0}x{6} {7} {7} {7} {7})))\n'.format(row+1, index+1, self.extract10, self.fa_str, val1, val2, index, self.gc_0)
                else:
                    val = self.partial_products[index + 1].pop()
                    if column == 0:
                        statement += '(S{0}x{1} ({2} ({3} {4} S{5}x{0} {6} {6} {6} {6})))\n'.format(row+1, index+1, self.extract32, self.ha_str, val, row, self.gc_0)
                        statement += '(C{0}x{1} ({2} ({3} {4} S{5}x{0} {6} {6} {6} {6})))\n'.format(row+1, index+1, self.extract10, self.ha_str, val, row, self.gc_0)
                    elif column == self.bits - 2:
                        statement += '(S{0}x{1} ({2} ({3} {4} C{5}x{6} C{0}x{6} {7} {7} {7} {7})))\n'.format(row+1, index+1, self.extract32, self.fa_str, val, row, index, self.gc_0)
                        statement += '(C{0}x{1} ({2} ({3} {4} C{5}x{6} C{0}x{6} {7} {7} {7} {7})))\n'.format(row+1, index+1, self.extract10, self.fa_str, val, row, index, self.gc_0)
                    else:
                        statement += '(S{0}x{1} ({2} ({3} {4} S{5}x{1} C{0}x{6} {7} {7} {7} {7})))\n'.format(row+1, index+1, self.extract32, self.fa_str, val, row, index, self.gc_0)
                        statement += '(C{0}x{1} ({2} ({3} {4} S{5}x{1} C{0}x{6} {7} {7} {7} {7})))\n'.format(row+1, index+1, self.extract10, self.fa_str, val, row, index, self.gc_0)
                statement += ')\n'

        return statement

    def _generate_and_d_let(self):
        statement = ''
        statement += '(let\n'
        statement += '(\n'
        self.num_let += 1
        for row in range(self.bits):
            for column in range(self.bits):
                index = row + column
                if row != column or row == self.bug_bit:
                    statement += '(and{0}x{1}_d ({2} X{0}_d Y{1}_d ({3} and{0}x{1}) ({4} and{0}x{1})))\n'.format(row, column, self.and2_incomplete_str, self.rail1, self.rail0)
                else:
                    statement += '(and{0}x{1}_d ({2} X{0}_d Y{1}_d ({3} and{0}x{1}) ({4} and{0}x{1})))\n'.format(row, column, self.and2_str, self.rail1, self.rail0)
                try:
                    self.partial_products_d[index].append('and{0}x{1}_d'.format(row,column))
                except KeyError:
                    self.partial_products_d[index] = ['and{0}x{1}_d'.format(row, column)]
        statement += ')\n'

        return statement

    def _generate_adder_d_let(self):
        statement = ''
        statement += '(let\n'
        statement += '(\n'
        statement += '(S0x0_d {0})\n'.format(self.partial_products_d[0].pop())
        statement += ')\n'
        self.num_let += 1

        for row in range(self.bits):
            for column in range(self.bits - 1):
                statement += '(let\n'
                statement += '(\n'
                self.num_let += 1
                index = row + column
                if row == 0:
                    val1 = self.partial_products_d[index + 1].pop()
                    val2 = self.partial_products_d[index + 1].pop()
                    if column == 0:
                        statement += '(S{0}x{1}_d ({2} ({3} {4} {5} ({6} S{0}x{1}) ({7} S{0}x{1}) ({6} C{0}x{1}) ({7} C{0}x{1}))))\n'.format(row+1, index+1, self.extract32, self.ha_str, val1, val2, self.rail1, self.rail0)
                        statement += '(C{0}x{1}_d ({2} ({3} {4} {5} ({6} S{0}x{1}) ({7} S{0}x{1}) ({6} C{0}x{1}) ({7} C{0}x{1}))))\n'.format(row+1, index+1, self.extract10, self.ha_str, val1, val2, self.rail1, self.rail0)
                    else:
                        statement += '(S{0}x{1}_d ({2} ({3} {4} {5} C{0}x{6}_d ({7} S{0}x{1}) ({8} S{0}x{1}) ({7} C{0}x{1}) ({8} C{0}x{1}))))\n'.format(row+1, index+1, self.extract32, self.fa_str, val1, val2, index, self.rail1, self.rail0)
                        statement += '(C{0}x{1}_d ({2} ({3} {4} {5} C{0}x{6}_d ({7} S{0}x{1}) ({8} S{0}x{1}) ({7} C{0}x{1}) ({8} C{0}x{1}))))\n'.format(row+1, index+1, self.extract10, self.fa_str, val1, val2, index, self.rail1, self.rail0)
                else:
                    val = self.partial_products_d[index + 1].pop()
                    if column == 0:
                        statement += '(S{0}x{1}_d ({2} ({3} {4} S{5}x{0}_d ({6} S{0}x{1}) ({7} S{0}x{1}) ({6} C{0}x{1}) ({7} C{0}x{1}))))\n'.format(row+1, index+1, self.extract32, self.ha_str, val, row, self.rail1, self.rail0)
                        statement += '(C{0}x{1}_d ({2} ({3} {4} S{5}x{0}_d ({6} S{0}x{1}) ({7} S{0}x{1}) ({6} C{0}x{1}) ({7} C{0}x{1}))))\n'.format(row+1, index+1, self.extract10, self.ha_str, val, row, self.rail1, self.rail0)
                    elif column == self.bits - 2:
                        statement += '(S{0}x{1}_d ({2} ({3} {4} C{5}x{6}_d C{0}x{6}_d ({7} S{0}x{1}) ({8} S{0}x{1}) ({7} C{0}x{1}) ({8} C{0}x{1}))))\n'.format(row+1, index+1, self.extract32, self.fa_str, val, row, index, self.rail1, self.rail0)
                        statement += '(C{0}x{1}_d ({2} ({3} {4} C{5}x{6}_d C{0}x{6}_d ({7} S{0}x{1}) ({8} S{0}x{1}) ({7} C{0}x{1}) ({8} C{0}x{1}))))\n'.format(row+1, index+1, self.extract10, self.fa_str, val, row, index, self.rail1, self.rail0)
                    else:
                        statement += '(S{0}x{1}_d ({2} ({3} {4} S{5}x{1}_d C{0}x{6}_d ({7} S{0}x{1}) ({8} S{0}x{1}) ({7} C{0}x{1}) ({8} C{0}x{1}))))\n'.format(row+1, index+1, self.extract32, self.fa_str, val, row, index, self.rail1, self.rail0)
                        statement += '(C{0}x{1}_d ({2} ({3} {4} S{5}x{1}_d C{0}x{6}_d ({7} S{0}x{1}) ({8} S{0}x{1}) ({7} C{0}x{1}) ({8} C{0}x{1}))))\n'.format(row+1, index+1, self.extract10, self.fa_str, val, row, index, self.rail1, self.rail0)
                statement += ')\n'

        return statement

    def _generate_output_d_let(self):
        statement = ''
        statement += '(let\n'
        statement += '(\n'
        self.num_let += 1
        for row in range(self.bits + 1):
            for column in range(self.bits):
                index = row + column
                if index == self.bits * 2 - 1:
                    statement += '(Z%d C%dx%d_d)\n' % (index, row, index-1)
                elif (row == index) or (row == self.bits and index > self.bits):
                    statement += '(Z%d S%dx%d_d)\n' % (index, row, index)
        statement += ')\n'

        return statement


    def _generate_implication(self):
        statement = ''
        statement += '(=>\n'
        statement += self._generate_precondition()
        statement += self._generate_postcondition()
        statement += ')\n'

        return statement

    def _generate_precondition(self):
        statement = ''
        statement += '(and\n'
        statement += self._generate_inputs_data()
        statement += self._generate_d_inputs_not_illegal()
        statement += self._generate_current_gate_output_zero()
        statement += self._generate_or_null_eq_inputs()
        statement += self._generate_or_data_d_inputs()
        statement += ')\n'

        return statement

    def _generate_postcondition(self):
        statement = ''
        statement += '(or\n'
        for output in range(self.bits*2):
            statement += '(datap Z{0})\n'.format(output)
        statement += ')\n'

        return statement

    def _generate_inputs_data(self):
        statement = ''
        for i in range(self.bits):
            statement += '(datap X{0})\n'.format(i)
            statement += '(datap Y{0})\n'.format(i)

        return statement

    def _generate_current_gate_output_zero(self):
        return '(= (_ bv0 1) Gc_0)\n'

    def _generate_d_inputs_not_illegal(self):
        statement = ''
        for i in range(self.bits):
            statement += '(not (= (_ bv3 2) X{0}_d))\n'.format(i)
            statement += '(not (= (_ bv3 2) Y{0}_d))\n'.format(i)

        return statement

    def _generate_or_null_eq_inputs(self):
        statement = ''
        for i in range(self.bits):
            statement += '(or\n'
            statement += '(nullp X{0}_d)\n'.format(i)
            statement += '(= X{0} X{0}_d)\n'.format(i)
            statement += ')\n'
            statement += '(or\n'
            statement += '(nullp Y{0}_d)\n'.format(i)
            statement += '(= Y{0} Y{0}_d)\n'.format(i)
            statement += ')\n'

        return statement

    def _generate_or_data_d_inputs(self):
        statement = ''
        statement += '(or\n'
        for i in range(self.bits):
            statement += '(datap X{0}_d)\n'.format(i)
            statement += '(datap Y{0}_d)\n'.format(i)
        statement += ')\n'

        return statement