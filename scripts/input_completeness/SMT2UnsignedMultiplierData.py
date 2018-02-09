class SMT2UnsignedMultiplierData():
    partial_products = dict()
    partial_products_d = dict()
    templates = ['rail', 'nullp', 'datap', 'th34w2', 'th24comp', 'th22', 'th23', 'th12', 'thand0', 'and2', 'ha', 'fa']
    num_let = 0

    def __init__(self, num_bits):
        self.n = num_bits

    def generate_proof(self):
        return self.generate_logic() + \
               self.generate_inputs() + \
               self.generate_templates() + \
               self.generate_assert() + \
               self.generate_and_gates() + \
               self.generate_adders() + \
               self.generate_and_d_gates() + \
               self.generate_adders_d() + \
               self.generate_outputs() + \
               self.generate_proof_obligations() + \
               self.generate_check_model()

    def generate_logic(self):
        return '(set-logic QF_BV)\n'

    def generate_inputs(self):
        x_in = '; Inputs X:\n'
        y_in = '; Inputs Y:\n'
        z_out = '; Outputs Z:\n'
        g_c = '; Current Theshold Gate Values:\n'
        g_c += '(declare-fun Gc_0 () (_ BitVec 1))\n'
        for bit in range(self.n):
            x_in += '(declare-fun X%d () (_ BitVec 2))\n' % bit
            x_in += '(declare-fun X%d_d () (_ BitVec 2))\n' % bit
            y_in += '(declare-fun Y%d () (_ BitVec 2))\n' % bit
            y_in += '(declare-fun Y%d_d () (_ BitVec 2))\n' % bit
        for bit in range(self.n*2):
            z_out += '(declare-fun Z%d () (_ BitVec 2))\n' % bit
        return x_in + y_in + z_out + g_c

    def generate_templates(self):
        template_str = ''
        for template in self.templates:
            file_name = '../templates/%s.smt2' % template
            with open(file_name, 'r') as r_file:
                template_str += r_file.read()
        return template_str

    def generate_assert(self):
        return '(assert\n(not\n'

    def generate_and_gates(self):
        let_statement = '(let\n(\n'
        self.num_let += 1
        for row in range(self.n):
            for column in range(self.n):
                test = row + column
                let_statement += '(and%dx%d (and2 X%d Y%d Gc_0 Gc_0))\n' % (row, column, row, column)
                try:
                    self.partial_products[test].append('and%dx%d' % (row, column))
                except KeyError:
                    self.partial_products[test] = ['and%dx%d' % (row, column)]
        let_statement = let_statement.rstrip() + ')\n'
        return let_statement

    def generate_adders(self):
        let_statement = '(let\n(\n(S0x0 %s))\n' % self.partial_products[0].pop()
        for row in range(self.n):
            if row == 0:
                for column in range(self.n-1):
                    let_statement += '(let\n(\n'
                    self.num_let += 1
                    first_val = self.partial_products[row+column+1].pop()
                    sec_val = self.partial_products[row+column+1].pop()
                    if column == 0:
                        let_statement += '(S%dx%d ((_ extract 3 2) (ha %s %s Gc_0 Gc_0 Gc_0 Gc_0)))\n' % \
                            (row+1, row+column+1, first_val, sec_val)
                        let_statement += '(C%dx%d ((_ extract 1 0) (ha %s %s Gc_0 Gc_0 Gc_0 Gc_0)))\n' % \
                            (row+1, row+column+1, first_val, sec_val)
                    else:
                        let_statement += '(S%dx%d ((_ extract 3 2) (fa %s %s C%dx%d Gc_0 Gc_0 Gc_0 Gc_0)))\n' % \
                            (row+1, row+column+1, first_val, sec_val, row+1, row+column)
                        let_statement += '(C%dx%d ((_ extract 1 0) (fa %s %s C%dx%d Gc_0 Gc_0 Gc_0 Gc_0)))\n' % \
                            (row+1, row+column+1, first_val, sec_val, row+1, row+column)
                    let_statement = let_statement.rstrip() + ')\n'
            else:
                for column in range(self.n-1):
                    let_statement += '(let\n(\n'
                    self.num_let += 1
                    first_val = self.partial_products[row+column+1].pop()
                    if column == 0:
                        let_statement += '(S%dx%d ((_ extract 3 2) (ha %s S%dx%d Gc_0 Gc_0 Gc_0 Gc_0)))\n' % \
                            (row+1, row+column+1, first_val, row, row+column+1)
                        let_statement += '(C%dx%d ((_ extract 1 0) (ha %s S%dx%d Gc_0 Gc_0 Gc_0 Gc_0)))\n' % \
                            (row+1, row+column+1, first_val, row, row+column+1)
                    elif column == self.n-2:
                        let_statement += '(S%dx%d ((_ extract 3 2) (fa %s C%dx%d C%dx%d Gc_0 Gc_0 Gc_0 Gc_0)))\n' % \
                            (row+1, row+column+1, first_val, row, row+column, row+1, row+column)
                        let_statement += '(C%dx%d ((_ extract 1 0) (fa %s C%dx%d C%dx%d Gc_0 Gc_0 Gc_0 Gc_0)))\n' % \
                            (row+1, row+column+1, first_val, row, row+column, row+1, row+column)
                    else:
                        let_statement += '(S%dx%d ((_ extract 3 2) (fa %s S%dx%d C%dx%d Gc_0 Gc_0 Gc_0 Gc_0)))\n' % \
                            (row+1, row+column+1, first_val, row, row+column+1, row+1, row+column)
                        let_statement += '(C%dx%d ((_ extract 1 0) (fa %s S%dx%d C%dx%d Gc_0 Gc_0 Gc_0 Gc_0)))\n' % \
                            (row+1, row+column+1, first_val, row, row+column+1, row+1, row+column)
                    let_statement = let_statement.rstrip() + ')\n'
        return let_statement

    def generate_and_d_gates(self):
        let_statement = '(let\n(\n'
        self.num_let += 1
        for row in range(self.n):
            for column in range(self.n):
                test = row + column
                let_statement += '(and{0}x{1}_d (and2 X{0}_d Y{1}_d (rail1 and{0}x{1}) (rail0 and{0}x{1})))\n'.format(row, column)
                try:
                    self.partial_products_d[test].append('and{0}x{1}_d'.format(row, column))
                except KeyError:
                    self.partial_products_d[test] = ['and{0}x{1}_d'.format(row, column)]
        let_statement = let_statement.rstrip() + ')\n'
        return let_statement

    def generate_adders_d(self):
        let_statement = '(let\n(\n(S0x0_d %s))\n' % self.partial_products_d[0].pop()
        for row in range(self.n):
            if row == 0:
                for column in range(self.n-1):
                    let_statement += '(let\n(\n'
                    self.num_let += 1
                    first_val = self.partial_products_d[row+column+1].pop()
                    sec_val = self.partial_products_d[row+column+1].pop()
                    if column == 0:
                        let_statement += '(S{0}x{1}_d ((_ extract 3 2) (ha {2} {3} (rail1 S{0}x{1}) (rail0 S{0}x{1}) \
(rail1 C{0}x{1}) (rail0 C{0}x{1}))))\n'.format(row+1, row+column+1, first_val, sec_val)
                        let_statement += '(C{0}x{1}_d ((_ extract 1 0) (ha {2} {3} (rail1 S{0}x{1}) (rail0 S{0}x{1}) \
(rail1 C{0}x{1}) (rail0 C{0}x{1}))))\n'.format(row+1, row+column+1, first_val, sec_val)
                    else:
                        let_statement += '(S{0}x{1}_d ((_ extract 3 2) (fa {2} {3} C{0}x{4}_d (rail1 S{0}x{1}) (rail0 S{0}x{1}) \
(rail1 C{0}x{1}) (rail0 C{0}x{1}))))\n'.format(row+1, row+column+1, first_val, sec_val, row+column)
                        let_statement += '(C{0}x{1}_d ((_ extract 1 0) (fa {2} {3} C{0}x{4}_d (rail1 S{0}x{1}) (rail0 S{0}x{1}) \
(rail1 C{0}x{1}) (rail0 C{0}x{1}))))\n'.format(row+1, row+column+1, first_val, sec_val, row+column)
                    let_statement = let_statement.rstrip() + ')\n'
            else:
                for column in range(self.n-1):
                    let_statement += '(let\n(\n'
                    self.num_let += 1
                    first_val = self.partial_products_d[row+column+1].pop()
                    if column == 0:
                        let_statement += '(S{0}x{1}_d ((_ extract 3 2) (ha {2} S{3}x{1}_d (rail1 S{0}x{1}) (rail0 S{0}x{1}) \
(rail1 C{0}x{1}) (rail0 C{0}x{1}))))\n'.format(row+1, row+column+1, first_val, row)
                        let_statement += '(C{0}x{1}_d ((_ extract 1 0) (ha {2} S{3}x{1}_d (rail1 S{0}x{1}) (rail0 S{0}x{1}) \
(rail1 C{0}x{1}) (rail0 C{0}x{1}))))\n'.format(row+1, row+column+1, first_val, row)
                    elif column == self.n-2:
                        let_statement += '(S{0}x{1}_d ((_ extract 3 2) (fa {2} C{3}x{4}_d C{0}x{4}_d (rail1 S{0}x{1}) (rail0 S{0}x{1}) \
(rail1 C{0}x{1}) (rail0 C{0}x{1}))))\n'.format(row+1, row+column+1, first_val, row, row+column)
                        let_statement += '(C{0}x{1}_d ((_ extract 1 0) (fa {2} C{3}x{4}_d C{0}x{4}_d (rail1 S{0}x{1}) (rail0 S{0}x{1}) \
(rail1 C{0}x{1}) (rail0 C{0}x{1}))))\n'.format(row+1, row+column+1, first_val, row, row+column)
                    else:
                        let_statement += '(S{0}x{1}_d ((_ extract 3 2) (fa {2} S{3}x{1}_d C{0}x{4}_d (rail1 S{0}x{1}) (rail0 S{0}x{1}) \
(rail1 C{0}x{1}) (rail0 C{0}x{1}))))\n'.format(row+1, row+column+1, first_val, row, row+column)
                        let_statement += '(C{0}x{1}_d ((_ extract 1 0) (fa {2} S{3}x{1}_d C{0}x{4}_d (rail1 S{0}x{1}) (rail0 S{0}x{1}) \
(rail1 C{0}x{1}) (rail0 C{0}x{1}))))\n'.format(row+1, row+column+1, first_val, row, row+column)
                    let_statement = let_statement.rstrip() + ')\n'
        return let_statement

    def generate_outputs(self):
        let_statement = '(let\n(\n'
        self.num_let += 1
        for row in range(self.n+1):
            for column in range(self.n):
                current = row + column
                if current == self.n + self.n - 1:
                    let_statement += '(Z%d C%dx%d_d)\n' % (current, row, current-1)
                elif (row == current) or (row == self.n and current > self.n):
                    let_statement += '(Z%d S%dx%d_d)\n' % (current, row, current)
        let_statement = let_statement.rstrip() + ')\n'
        return let_statement

    def generate_proof_obligations(self):
        ret_str = '(=>\n(and\n'
        ret_str += '(= (_ bv0 1) Gc_0)\n'
        for bit in range(self.n):
            ret_str += '(datap X%d)\n' % bit
            ret_str += '(datap Y%d)\n' % bit
        for bit in range(self.n):
            ret_str += '(not (= (_ bv3 2) X%d_d))\n' % bit
            ret_str += '(not (= (_ bv3 2) Y%d_d))\n' % bit
        for bit in range(self.n):
            ret_str += '(or\n'
            ret_str += '(nullp X%d_d)\n' % bit
            ret_str += '(= X%d X%d_d))\n' % (bit, bit)
        for bit in range(self.n):
            ret_str += '(or\n'
            ret_str += '(nullp Y%d_d)\n' % bit
            ret_str += '(= Y%d Y%d_d))\n' % (bit, bit)
        ret_str += '(or\n'
        for bit in range(self.n):
            ret_str += '(datap X%d_d)\n' % bit
            ret_str += '(datap Y%d_d)\n' % bit
        ret_str += '))\n'
        ret_str += '(or\n'
        for bit in range(self.n*2):
            ret_str += '(datap Z%d)\n' % bit
        ret_str += ')' * (self.num_let + 6)
        ret_str += '\n'
        return ret_str

    def generate_check_model(self):
        ret_str = '(check-sat)\n'
        ret_str += '(get-model)\n'
        return ret_str