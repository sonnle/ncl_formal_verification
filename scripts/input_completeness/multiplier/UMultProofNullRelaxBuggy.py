import random
import UMultProofNullRelax

class UMultProofNullRelaxBuggy(UMultProofNullRelax.UMultProofNullRelax):
    fa_str = 'fa'
    ha_str = 'ha_relax'
    and2_str = 'and2'

    def __init__(self, bits):
        super(UMultProofNullRelaxBuggy, self).__init__(bits)
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
        statement = ''
        statement += '(let\n'
        statement += '(\n'
        self.num_let += 1
        for row in range(self.bits):
            for column in range(self.bits):
                index = row + column
                if row == column:
                    statement += '(and{0}x{1} ({2} X{0} Y{1} {3} {3}))\n'.format(row, column, self.and2_str, 'Gc_0')
                else:
                    statement += '(and{0}x{1} ({2} X{0} Y{1} {3} {3}))\n'.format(row, column, 'and2_incomplete_relax', 'Gc_0')
                try:
                    self.partial_products[index].append('and{0}x{1}'.format(row, column))
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
                index = row + column
                statement += '(let\n'
                statement += '(\n'
                self.num_let += 1
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
                        statement += '(S{0}x{1} ({2} ({3} {4} S{5}x{1} {6} {6} {6} {6})))\n'.format(row+1, index+1, extract32, self.ha_str, val, row, gc_0)
                        statement += '(C{0}x{1} ({2} ({3} {4} S{5}x{1} {6} {6} {6} {6})))\n'.format(row+1, index+1, extract10, self.ha_str, val, row, gc_0)
                    elif column == self.bits-2:
                        statement += '(S{0}x{1} ({2} ({3} {4} C{5}x{6} C{0}x{6} {7} {7} {7} {7})))\n'.format(row+1, index+1, extract32, self.fa_str, val, row, index, gc_0)
                        statement += '(C{0}x{1} ({2} ({3} {4} C{5}x{6} C{0}x{6} {7} {7} {7} {7})))\n'.format(row+1, index+1, extract10, self.fa_str, val, row, index, gc_0)
                    else:
                        statement += '(S{0}x{1} ({2} ({3} {4} S{5}x{1} C{0}x{6} {7} {7} {7} {7})))\n'.format(row+1, index+1, extract32, self.fa_str, val, row, index, gc_0)
                        statement += '(C{0}x{1} ({2} ({3} {4} S{5}x{1} C{0}x{6} {7} {7} {7} {7})))\n'.format(row+1, index+1, extract10, self.fa_str, val, row, index, gc_0)
                statement += ')\n'

        return statement
