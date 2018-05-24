import random

import UMultProofData

class UMultProofDataBuggy(UMultProofData.UMultProofData):
    def __init__(self, bits):
        super(UMultProofDataBuggy, self).__init__(bits)
        self.bug_bit = random.randint(0, bits - 1)

    def generate_header(self):
        header = ''
        header += '; Random bug bit is {0}\n'.format(self.bug_bit)

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
                if row != column or row == self.bug_bit:
                    statement += '(and{0}x{1} ({2} X{0} Y{1} {3} {3}))\n'.format(row, column, 'and2_incomplete', gc_0)
                else:
                    statement += '(and{0}x{1} ({2} X{0} Y{1} {3} {3}))\n'.format(row, column, 'and2', gc_0)
                try:
                    self.partial_products[index].append('and{0}x{1}'.format(row,column))
                except KeyError:
                    self.partial_products[index] = ['and{0}x{1}'.format(row, column)]
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
                if row != column or row == self.bug_bit:
                    statement += '(and{0}x{1}_d ({2} X{0}_d Y{1}_d ({3} and{0}x{1}) ({4} and{0}x{1})))\n'.format(row, column, 'and2_incomplete', rail1, rail0)
                else:
                    statement += '(and{0}x{1}_d ({2} X{0}_d Y{1}_d ({3} and{0}x{1}) ({4} and{0}x{1})))\n'.format(row, column, 'and2', rail1, rail0)
                try:
                    self.partial_products_d[index].append('and{0}x{1}_d'.format(row,column))
                except KeyError:
                    self.partial_products_d[index] = ['and{0}x{1}_d'.format(row, column)]
        statement += ')\n'

        return statement