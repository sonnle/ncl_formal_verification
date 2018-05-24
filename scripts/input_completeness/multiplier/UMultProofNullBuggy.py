import random

import UMultProofNull

class UMultProofNullBuggy(UMultProofNull.UMultProofNull):
    def __init__(self, bits):
        super(UMultProofNullBuggy, self).__init__(bits)
        self.bug_bit = random.randint(0, bits - 1)

    def generate_header(self):
        header = ''
        header += '; Random bug bit is {0}\n'.format(self.bug_bit)

        return header

    def _generate_and_let(self):
        statement = ''
        statement += '(let\n'
        statement += '(\n'
        self.num_let += 1
        for row in range(self.bits):
            for column in range(self.bits):
                index = row + column
                if row != column or row == self.bug_bit:
                    statement += '(and{0}x{1} ({2} X{0} Y{1} {3} {3}))\n'.format(row, column, 'and2_incomplete', 'Gc_0')
                else:
                    statement += '(and{0}x{1} ({2} X{0} Y{1} {3} {3}))\n'.format(row, column, 'and2', 'Gc_0')
                try:
                    self.partial_products[index].append('and{0}x{1}'.format(row, column))
                except KeyError:
                    self.partial_products[index] = ['and{0}x{1}'.format(row, column)]
        statement += ')\n'

        return statement
