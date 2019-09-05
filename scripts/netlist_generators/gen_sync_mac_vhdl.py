class MACVHDLGenerator:
    partial_products = dict()

    def __init__(self, bits):
        self.bits = bits

    def generate_vhdl(self):
        statement = self.generate_header()
        statement += self.generate_entity()
        statement += self.generate_architecture()
        return statement

    def generate_header(self):
        statement = 'library IEEE;\n'
        statement += 'use IEEE.STD_LOGIC_1164.all;\n'
        statement += '\n'
        return statement

    def generate_entity(self):
        statement = 'entity MAC{0}_{1}_{1} is\n'.format(2*self.bits, self.bits)
        statement += 'port(Xi, Yi: in STD_LOGIC_VECTOR({0} downto 0);\n'.format(self.bits - 1)
        statement += 'ACCi: in STD_LOGIC_VECTOR({0} downto 0);\n'.format(2*self.bits - 1)
        statement += 'rst, clk: in STD_LOGIC;\n'
        statement += 'ACCo: out STD_LOGIC_VECTOR({0} downto 0));\n'.format(2*self.bits - 1)
        statement += 'end MAC{0}_{1}_{1};\n'.format(2*self.bits, self.bits)
        statement += '\n'
        return statement

    def generate_architecture(self):
        statement = 'architecture BEHAVIORIAL of MAC{0}_{1}_{1} is\n\n'.format(2*self.bits, self.bits)
        statement += self.generate_signals()
        statement += self.generate_components()
        statement += 'begin\n\n'
        statement += self.generate_input_register()
        statement += self.generate_partial_products()
        statement += self.generate_port_map()
        statement += self.generate_product_assignments()
        statement += self.generate_accumulation()
        statement += self.generate_output_register()
        statement += 'end BEHAVIORIAL;\n'
        return statement

    def generate_signals(self):
        statement = 'type PP_ARRAY is array ({0} downto 0) of STD_LOGIC_VECTOR({0} downto 0);\n'.format(self.bits - 1)
        statement += 'signal X, Y: STD_LOGIC_VECTOR({0} downto 0);\n'.format(self.bits - 1)
        carry = ', '.join('C{0}'.format(c) for c in range(self.bits))
        statement += 'signal {0}: STD_LOGIC_VECTOR({1} downto 0);\n'.format(carry, self.bits - 1)
        summ = ', '.join('S{0}'.format(c) for c in range(self.bits))
        statement += 'signal {0}: STD_LOGIC_VECTOR({1} downto 0);\n'.format(summ, self.bits - 1)
        statement += 'signal P, Cacc, Sacc: STD_LOGIC_VECTOR({0} downto 0);\n'.format(2*self.bits - 1)
        statement += 'signal XY: PP_ARRAY;\n\n'
        return statement


    def generate_components(self):
        statement = self.generate_full_adder()
        statement += '\n'
        statement += self.generate_half_adder()
        statement += '\n'
        statement += self.generate_register()
        statement += '\n'
        return statement

    def generate_full_adder(self):
        statement = 'component FA\n'
        statement += 'port(X, Y, Cin: in STD_LOGIC;\n'
        statement += 'Sum, Cout: out STD_LOGIC);\n'
        statement += 'end component;\n'
        return statement

    def generate_half_adder(self):
        statement = 'component HA\n'
        statement += 'port(X, Y: in STD_LOGIC;\n'
        statement += 'Sum, Cout: out STD_LOGIC);\n'
        statement += 'end component;\n'
        return statement

    def generate_register(self):
        statement = 'component REG\n'
        statement += 'port(D: in STD_LOGIC;\n'
        statement += 'Rst: in STD_LOGIC;\n'
        statement += 'Clk: in STD_LOGIC;\n'
        statement += 'Q: out STD_LOGIC);\n'
        statement += 'end component;\n'
        return statement

    def generate_input_register(self):
        statement = ''
        for i in range(self.bits):
            statement += 'REGX{0}: REG port map(Xi({0}), rst, clk, X({0}));\n'.format(i)
        for i in range(self.bits):
            statement += 'REGY{0}: REG port map(Yi({0}), rst, clk, Y({0}));\n'.format(i)
        statement += '\n'
        return statement

    def generate_partial_products(self):
        statement = ''
        for x in range(self.bits):
            for y in range(self.bits):
                index = x + y
                statement += 'XY({0})({1}) <= X({0}) and Y({1});\n'.format(x, y)
                try:
                    self.partial_products[index].append('XY({0})({1})'.format(x,y))
                except KeyError:
                    self.partial_products[index] = ['XY({0})({1})'.format(x,y)]
        statement += '\n'
        return statement

    def generate_port_map(self):
        ha_count = 0
        fa_count = 0
        statement = ''
        for y in range(self.bits - 1):
            for x in range(self.bits):
                index = x + y
                if y == 0:
                    val1 = self.partial_products[index + 1].pop()
                    val2 = self.partial_products[index + 1].pop()
                    if x == 0:
                        # val1 = x, val2 = y
                        statement += 'HA{0}: HA port map({1}, {2}, S{3}({4}), C{3}({4}));\n'.format(ha_count, val1, val2, x, y)
                        ha_count += 1
                    else:
                        # val1 = x, val2 = y, carry = cin
                        carry = 'C{0}({1})'.format(x-1, y)
                        statement += 'FA{0}: FA port map({1}, {2}, {3}, S{4}({5}), C{4}({5}));\n'.format(fa_count, val1, val2, carry, x, y)
                        fa_count += 1
                else:
                    try:
                        val = self.partial_products[index + 1].pop()
                    except IndexError:
                        val = '\'0\''
                    if x == 0:
                        # val = x, summ = y
                        summ = 'S{0}({1})'.format(x+1, y-1)
                        statement += 'HA{0}: HA port map({1}, {2}, S{3}({4}), C{3}({4}));\n'.format(ha_count, val, summ, x, y)
                        ha_count += 1
                    elif x == self.bits-1:
                        # val = x, carry1 = y, carry2 = cin
                        carry1 = 'C{0}({1})'.format(x-1, y)
                        carry2 = 'C{0}({1})'.format(x, y-1)
                        statement += 'FA{0}: FA port map({1}, {2}, {3}, S{4}({5}), C{4}({5}));\n'.format(fa_count, val, carry1, carry2, x, y)
                        fa_count += 1
                    else:
                        # val = x, summ = y, carry = cin
                        summ = 'S{0}({1})'.format(x+1, y-1)
                        carry = 'C{0}({1})'.format(x-1, y)
                        statement += 'FA{0}: FA port map({1}, {2}, {3}, S{4}({5}), C{4}({5}));\n'.format(fa_count, val, summ, carry, x, y)
                        fa_count += 1
        statement += '\n'
        return statement

    def generate_product_assignments(self):
        statement = ''
        x_spot = 1
        y_spot = 0
        for index in range(2*self.bits):
            if index == 0:
                statement += 'REGP{0}: REG port map(XY(0)(0), rst, clk, P({0}));\n'.format(index)
            elif index < self.bits:
                statement += 'REGP{0}: REG port map(S{1}({2}), rst, clk, P({0}));\n'.format(index, 0, y_spot)
                y_spot += 1
            elif index == 2*self.bits - 1:
                statement += 'REGP{0}: REG port map(C{1}({2}), rst, clk, P({0}));\n'.format(index, x_spot - 1, self.bits - 2)
            else:
                statement += 'REGP{0}: REG port map(S{1}({2}), rst, clk, P({0}));\n'.format(index, x_spot, y_spot - 1)
                x_spot += 1
        statement += '\n'
        return statement

    def generate_accumulation(self):
        statement = ''
        fa_count = 0
        for i in range(2*self.bits):
            if i == 0:
                statement += 'HAA0: HA port map(P({0}), ACCi({0}), Sacc({0}), Cacc({0}));\n'.format(i)
            else:
                statement += 'FAA{0}: FA port map(P({1}), ACCi({1}), Cacc({2}), Sacc({1}), Cacc({1}));\n'.format(fa_count, i, i - 1)
                fa_count += 1
        statement += '\n'
        return statement

    def generate_output_register(self):
        statement = ''
        for i in range (2*self.bits):
            statement += 'REGACC{0}: REG port map(Sacc({0}), rst, clk, ACCo({0}));\n'.format(i)
        statement += '\n'
        return statement

def main():
    bits_list = [x for x in range(3, 4)]
    for bits in bits_list:
        x = MACVHDLGenerator(bits)

        print x.generate_vhdl()

        with open('mac{0}_{1}_{1}.vhdl'.format(2*bits, bits), 'wb') as w_file:
            w_file.write(x.generate_vhdl())

if __name__ == '__main__':
    main()
