class UMultVHDLGenerator:
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
        statement = 'entity UMULT{0} is\n'.format(self.bits)
        statement += 'port(X, Y: in bit_vector({0} downto 0);\n'.format(self.bits - 1)
        statement += 'rst, clk: in bit;\n'
        statement += 'P: out bit_vector({0} downto 0));\n'.format(2*self.bits - 1)
        statement += 'end UMULT{0};\n'.format(self.bits)
        statement += '\n'
        return statement

    def generate_architecture(self):
        statement = 'architecture BEHAVIORIAL of UMULT{0} is\n'.format(self.bits)
        statement += self.generate_signals()
        statement += self.generate_components()
        statement += 'begin\n\n'
        statement += self.generate_partial_products()
        statement += self.generate_port_map()
        statement += self.generate_output_assignments()
        statement += 'end BEHAVIORIAL;\n'
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

    def generate_output_assignments(self):
        statement = ''
        x_spot = 1
        y_spot = 0
        for index in range(2*self.bits):
            if index == 0:
                statement += 'P({0}) <= XY(0)(0);\n'.format(index)
            elif index < self.bits:
                statement += 'P({0}) <= S{1}({2});\n'.format(index, 0, y_spot)
                y_spot += 1
            elif index == 2*self.bits - 1:
                statement += 'P({0}) <= C{1}({2});\n'.format(index, x_spot - 1, self.bits - 2)
            else:

                statement += 'P({0}) <= S{1}({2});\n'.format(index, x_spot, y_spot - 1)
                x_spot += 1
        statement += '\n'
        return statement

    def generate_signals(self):
        statement = 'type PP_ARRAY is array ({0} downto 0) of bit_vector({0} downto 0);\n'.format(self.bits - 1)
        carry = ', '.join('C{0}'.format(c) for c in range(self.bits))
        statement += 'signal {0}: bit_vector({1} downto 0);\n'.format(carry, self.bits - 1)
        summ = ', '.join('S{0}'.format(c) for c in range(self.bits))
        statement += 'signal {0}: bit_vector({1} downto 0);\n'.format(summ, self.bits - 1)
        statement += 'signal XY: PP_ARRAY;\n'
        return statement

    def generate_components(self):
        statement = self.generate_full_adder()
        statement += '\n'
        statement += self.generate_half_adder()
        statement += '\n'
        return statement

    def generate_full_adder(self):
        statement = 'component FA\n'
        statement += 'port(X, Y, Cin: in bit;\n'
        statement += 'Sum, Cout: out bit);\n'
        statement += 'end component;\n'
        return statement

    def generate_half_adder(self):
        statement = 'component HA\n'
        statement += 'port(X, Y: in bit;\n'
        statement += 'Sum, Cout: out bit);\n'
        statement += 'end component;\n'
        return statement

def main():
    bits_list = [x for x in range(3, 21)]
    for bits in bits_list:
        x = UMultVHDLGenerator(bits)

        with open('umult{0}.vhdl'.format(bits), 'wb') as w_file:
            w_file.write(x.generate_vhdl())

if __name__ == '__main__':
    main()
