import random

import UMultProofNull

class UMultProofNullBuggy(UMultProofNull.UMultProofNull):
    and2_str = 'and2'
    and2_incomplete_str = 'and2_incomplete'
    ha_str = 'ha'
    fa_str = 'fa'

    def __init__(self, bits):
        super(UMultProofNullBuggy, self).__init__(bits)
        self.bug_bit = random.randint(0, bits - 1)

    def generate_header(self):
        header = ''
        header += '; Random bug bit is {0}\n'.format(self.bug_bit)

        return header
