import random
import UMultProofDataRelax

class UMultProofDataRelaxBuggy(UMultProofDataRelax.UMultProofDataRelax):
    fa_str = 'fa'
    ha_str = 'ha_relax'
    and2_str = 'and2'

    def __init__(self, bits):
        super(UMultProofDataRelaxBuggy, self).__init__(bits)
        self.and_bug = ['and2_relax_buggy_th22', 'and2_relax_buggy_thand0']
        self.ha_bug = ['ha_relax_buggy']
        self.fa_bug = ['fa_relax_buggy_th34w2', 'fa_relax_buggy_th23']
        self.bug_type = random.choice(self.and_bug + self.ha_bug + self.fa_bug)

        if self.bug_type in self.and_bug:
            self.and2_str = self.bug_type
        if self.bug_type in self.ha_bug:
            self.ha_str = self.bug_type
        if self.bug_type in self.fa_bug:
            self.fa_str = self.bug_type

        self.required_gate_templates += self.and_bug + self.ha_bug + self.fa_bug
        self.bug_bit = random.randint(0, bits - 1)

    def generate_header(self):
        header = ''
        header += '; Bug bit is: {0} (if applicable)\n'.format(self.bug_bit)
        header += '; Bug type is: {0}\n'.format(self.bug_type)

        return header

    def _generate_and_let(self):
        gc_0 = 'Gc_0'
        statement = ''
        statement += '(let\n'
        statement += '(\n'
        self.num_let += 1
        for row in range(self.bits):
            for column in range(self.bits):
                index = row + column
                if row == column:
                    statement += '(and{0}x{1} ({2} X{0} Y{1} {3} {3}))\n'.format(row, column, self.and2_str, gc_0)
                else:
                    statement += '(and{0}x{1} ({2} X{0} Y{1} {3} {3}))\n'.format(row, column, 'and2_incomplete_relax', gc_0)
                try:
                    self.partial_products[index].append('and{0}x{1}'.format(row,column))
                except KeyError:
                    self.partial_products[index] = ['and{0}x{1}'.format(row, column)]
        statement += ')\n'

        return statement

    def _generate_adder_let(self):
        extract32 = '(_ extract 3 2)'
        extract10 = '(_ extract 1 0)'
        gc_0 = 'Gc_0'
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
                        statement += '(S{0}x{1} ({2} ({3} {4} {5} {6} {6} {6} {6})))\n'.format(row+1, index+1, extract32, self.ha_str, val1, val2, gc_0)
                        statement += '(C{0}x{1} ({2} ({3} {4} {5} {6} {6} {6} {6})))\n'.format(row+1, index+1, extract10, self.ha_str, val1, val2, gc_0)
                    else:
                        statement += '(S{0}x{1} ({2} ({3} {4} {5} C{0}x{6} {7} {7} {7} {7})))\n'.format(row+1, index+1, extract32, self.fa_str, val1, val2, index, gc_0)
                        statement += '(C{0}x{1} ({2} ({3} {4} {5} C{0}x{6} {7} {7} {7} {7})))\n'.format(row+1, index+1, extract10, self.fa_str, val1, val2, index, gc_0)
                else:
                    val = self.partial_products[index + 1].pop()
                    if column == 0:
                        statement += '(S{0}x{1} ({2} ({3} {4} S{5}x{0} {6} {6} {6} {6})))\n'.format(row+1, index+1, extract32, self.ha_str, val, row, gc_0)
                        statement += '(C{0}x{1} ({2} ({3} {4} S{5}x{0} {6} {6} {6} {6})))\n'.format(row+1, index+1, extract10, self.ha_str, val, row, gc_0)
                    elif column == self.bits - 2:
                        statement += '(S{0}x{1} ({2} ({3} {4} C{5}x{6} C{0}x{6} {7} {7} {7} {7})))\n'.format(row+1, index+1, extract32, self.fa_str, val, row, index, gc_0)
                        statement += '(C{0}x{1} ({2} ({3} {4} C{5}x{6} C{0}x{6} {7} {7} {7} {7})))\n'.format(row+1, index+1, extract10, self.fa_str, val, row, index, gc_0)
                    else:
                        statement += '(S{0}x{1} ({2} ({3} {4} S{5}x{1} C{0}x{6} {7} {7} {7} {7})))\n'.format(row+1, index+1, extract32, self.fa_str, val, row, index, gc_0)
                        statement += '(C{0}x{1} ({2} ({3} {4} S{5}x{1} C{0}x{6} {7} {7} {7} {7})))\n'.format(row+1, index+1, extract10, self.fa_str, val, row, index, gc_0)
                statement += ')\n'

        return statement

    def _generate_and_d_let(self):
        gc_0 = 'Gc_0'
        rail1 = 'rail1'
        rail0 = 'rail0'
        statement = ''
        statement += '(let\n'
        statement += '(\n'
        self.num_let += 1
        for row in range(self.bits):
            for column in range(self.bits):
                index = row + column
                if row == column:
                    statement += '(and{0}x{1}_d ({2} X{0}_d Y{1}_d ({3} and{0}x{1}) ({4} and{0}x{1})))\n'.format(row, column, self.and2_str, rail1, rail0)
                else:
                    statement += '(and{0}x{1}_d ({2} X{0}_d Y{1}_d ({3} and{0}x{1}) ({4} and{0}x{1})))\n'.format(row, column, 'and2_incomplete_relax', rail1, rail0)
                try:
                    self.partial_products_d[index].append('and{0}x{1}_d'.format(row,column))
                except KeyError:
                    self.partial_products_d[index] = ['and{0}x{1}_d'.format(row, column)]
        statement += ')\n'

        return statement

    def _generate_adder_d_let(self):
        extract32 = '(_ extract 3 2)'
        extract10 = '(_ extract 1 0)'
        rail1 = 'rail1'
        rail0 = 'rail0'
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
                        statement += '(S{0}x{1}_d ({2} ({3} {4} {5} ({6} S{0}x{1}) ({7} S{0}x{1}) ({6} C{0}x{1}) ({7} C{0}x{1}))))\n'.format(row+1, index+1, extract32, self.ha_str, val1, val2, rail1, rail0)
                        statement += '(C{0}x{1}_d ({2} ({3} {4} {5} ({6} S{0}x{1}) ({7} S{0}x{1}) ({6} C{0}x{1}) ({7} C{0}x{1}))))\n'.format(row+1, index+1, extract10, self.ha_str, val1, val2, rail1, rail0)
                    else:
                        statement += '(S{0}x{1}_d ({2} ({3} {4} {5} C{0}x{6}_d ({7} S{0}x{1}) ({8} S{0}x{1}) ({7} C{0}x{1}) ({8} C{0}x{1}))))\n'.format(row+1, index+1, extract32, self.fa_str, val1, val2, index, rail1, rail0)
                        statement += '(C{0}x{1}_d ({2} ({3} {4} {5} C{0}x{6}_d ({7} S{0}x{1}) ({8} S{0}x{1}) ({7} C{0}x{1}) ({8} C{0}x{1}))))\n'.format(row+1, index+1, extract10, self.fa_str, val1, val2, index, rail1, rail0)
                else:
                    val = self.partial_products_d[index + 1].pop()
                    if column == 0:
                        statement += '(S{0}x{1}_d ({2} ({3} {4} S{5}x{0}_d ({6} S{0}x{1}) ({7} S{0}x{1}) ({6} C{0}x{1}) ({7} C{0}x{1}))))\n'.format(row+1, index+1, extract32, self.ha_str, val, row, rail1, rail0)
                        statement += '(C{0}x{1}_d ({2} ({3} {4} S{5}x{0}_d ({6} S{0}x{1}) ({7} S{0}x{1}) ({6} C{0}x{1}) ({7} C{0}x{1}))))\n'.format(row+1, index+1, extract10, self.ha_str, val, row, rail1, rail0)
                    elif column == self.bits - 2:
                        statement += '(S{0}x{1}_d ({2} ({3} {4} C{5}x{6}_d C{0}x{6}_d ({7} S{0}x{1}) ({8} S{0}x{1}) ({7} C{0}x{1}) ({8} C{0}x{1}))))\n'.format(row+1, index+1, extract32, self.fa_str, val, row, index, rail1, rail0)
                        statement += '(C{0}x{1}_d ({2} ({3} {4} C{5}x{6}_d C{0}x{6}_d ({7} S{0}x{1}) ({8} S{0}x{1}) ({7} C{0}x{1}) ({8} C{0}x{1}))))\n'.format(row+1, index+1, extract10, self.fa_str, val, row, index, rail1, rail0)
                    else:
                        statement += '(S{0}x{1}_d ({2} ({3} {4} S{5}x{1}_d C{0}x{6}_d ({7} S{0}x{1}) ({8} S{0}x{1}) ({7} C{0}x{1}) ({8} C{0}x{1}))))\n'.format(row+1, index+1, extract32, self.fa_str, val, row, index, rail1, rail0)
                        statement += '(C{0}x{1}_d ({2} ({3} {4} S{5}x{1}_d C{0}x{6}_d ({7} S{0}x{1}) ({8} S{0}x{1}) ({7} C{0}x{1}) ({8} C{0}x{1}))))\n'.format(row+1, index+1, extract10, self.fa_str, val, row, index, rail1, rail0)
                statement += ')\n'

        return statement
