class NCLMACVHDLGenerator:
    partial_products = dict()

    def __init__(self, bits):
        self.bits = bits

    def generate_partial_products(self):
        statement = ''
        for x in range(self.bits):
            for y in range(self.bits):
                index = x + y
                statement += 'XY({0})({1}) <= X({0}) and Y({1});\n'.format(x, y)
                try:
                    self.partial_products[index].append('partial_products({0})({1})'.format(x,y))
                except KeyError:
                    self.partial_products[index] = ['partial_products({0})({1})'.format(x,y)]
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
                        statement += 'HAA{0}: HA2 port map({1}, {2}, sum({3})({4}), carry({3})({4}));\n'.format(ha_count, val1, val2, x, y)
                        ha_count += 1
                    else:
                        # val1 = x, val2 = y, carry = cin
                        carry = 'carry({0})({1})'.format(x-1, y)
                        statement += 'FAA{0}: FA2 port map({1}, {2}, {3}, sum({4})({5}), carry({4})({5}));\n'.format(fa_count, val1, val2, carry, x, y)
                        fa_count += 1
                else:
                    try:
                        val = self.partial_products[index + 1].pop()
                    except IndexError:
                        val = '\"01\"'
                    if x == 0:
                        # val = x, summ = y
                        summ = 'sum({0})({1})'.format(x+1, y-1)
                        statement += 'HAA{0}: HA2 port map({1}, {2}, sum({3})({4}), carry({3})({4}));\n'.format(ha_count, val, summ, x, y)
                        ha_count += 1
                    elif x == self.bits-1:
                        # val = x, carry1 = y, carry2 = cin
                        carry1 = 'carry({0})({1})'.format(x-1, y)
                        carry2 = 'carry({0})({1})'.format(x, y-1)
                        statement += 'FAA{0}: FA2 port map({1}, {2}, {3}, sum({4})({5}), carry({4})({5}));\n'.format(fa_count, val, carry1, carry2, x, y)
                        fa_count += 1
                    else:
                        # val = x, summ = y, carry = cin
                        summ = 'sum({0})({1})'.format(x+1, y-1)
                        carry = 'carry({0})({1})'.format(x-1, y)
                        statement += 'FAA{0}: FA2 port map({1}, {2}, {3}, sum({4})({5}), carry({4})({5}));\n'.format(fa_count, val, summ, carry, x, y)
                        fa_count += 1
        statement += '\n'
        return statement

if __name__ == '__main__':
    x = NCLMACVHDLGenerator(10)
    x.generate_partial_products()
    print x.generate_port_map()