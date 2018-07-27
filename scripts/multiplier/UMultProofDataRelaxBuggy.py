import random
import UMultProofDataRelax

class UMultProofDataRelaxBuggy(UMultProofDataRelax.UMultProofDataRelax):
    and2_str = 'and2'
    and2_incomplete_str = 'and2_incomplete_relax'
    ha_str = 'ha_relax'
    fa_str = 'fa'

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

        self.required_gate_templates.append(self.bug_type)

    def generate_header(self):
        header = ''
        header += '; Bug type is: {0}\n'.format(self.bug_type)

        return header
