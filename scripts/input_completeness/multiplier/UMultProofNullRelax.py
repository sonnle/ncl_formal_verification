import UMultProofNull

class UMultProofNullRelax(UMultProofNull.UMultProofNull):
    and2_str = 'and2'
    and2_incomplete_str = 'and2_incomplete_relax'
    ha_str = 'ha_relax'
    fa_str = 'fa'

    def __init__(self, bits):
        super(UMultProofNullRelax, self).__init__(bits)
        self.required_gate_templates += ['and2_incomplete_relax', 'ha_relax']