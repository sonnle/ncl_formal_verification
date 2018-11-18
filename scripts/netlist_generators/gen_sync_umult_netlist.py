def main():
    bits_list = [x for x in range(3, 4)]
    for bits in bits_list:
        and2_str = 'and2'
        and2_incomplete_str = 'and2_incomplete'
        ha_str = 'ha'
        fa_str = 'fa'

        gc_0 = 'Gc_0'
        extract32 = '(_ extract 3 2)'
        extract10 = '(_ extract 1 0)'

        statement = ''

        bug_bit = None

        i = 0
        intermediate_index = 0

        partial_products = dict()

        # Generate Input List
        statement += ','.join('X{0}'.format(i) for i in range(bits))
        statement += ','
        statement += ','.join('Y{0}'.format(i) for i in range(bits))
        statement += '\n'

        # Generate Output List
        statement += ','.join('Z{0}'.format(i) for i in range(2*bits))
        statement += '\n'

        # Generate AND2 Netlist
        for row in range(bits):
            for column in range(bits):
                index = row + column
                statement += 'AND and{0}x{1} X{0} Y{1}\n'.format(row, column)
                try:
                    partial_products[index].append('and{0}x{1}'.format(row,column))
                except KeyError:
                    partial_products[index] = ['and{0}x{1}'.format(row,column)]

        # Generate HAs and FAs Netlist
        for row in range(bits):
            for column in range(bits - 1):
                index = row + column
                if row == 0:
                    val1 = partial_products[index + 1].pop()
                    val2 = partial_products[index + 1].pop()
                    if column == 0:
                        # val1 = x, val2 = y
                        statement += 'XOR S{0}x{1} {2} {3}\n'.format(row+1, index+1, val1, val2)
                        statement += 'AND C{0}x{1} {2} {3}\n'.format(row+1, index+1, val1, val2)
                    else:
                        # val1 = x, val2 = y, carry = cin
                        carry = 'C{0}x{1}'.format(row+1, index)
                        statement += 'XOR I{0} {1} {2}\n'.format(intermediate_index, val1, val2)
                        statement += 'XOR S{0}x{1} I{2} {3}\n'.format(row+1, index+1, intermediate_index, carry)
                        statement += 'AND I{0} I{1} {2}\n'.format(intermediate_index+1, intermediate_index, carry)
                        statement += 'AND I{0} {1} {2}\n'.format(intermediate_index+2, val1, val2)
                        statement += 'OR C{0}x{1} I{2} I{3}\n'.format(row+1, index+1, intermediate_index+1, intermediate_index+2)
                        intermediate_index += 3
                else:
                    val = partial_products[index + 1].pop()
                    if column == 0:
                        # val = x, summ = y
                        summ = 'S{0}x{1}'.format(row, index+1)
                        statement += 'XOR S{0}x{1} {2} {3}\n'.format(row+1, index+1, val, summ)
                        statement += 'AND C{0}x{1} {2} {3}\n'.format(row+1, index+1, val, summ)
                    elif column == bits-2:
                        # val = x, carry1 = y, carry2 = cin
                        carry1 = 'C{0}x{1}'.format(row, index)
                        carry2 = 'C{0}x{1}'.format(row+1, index)
                        statement += 'XOR I{0} {1} {2}\n'.format(intermediate_index, val, carry1)
                        statement += 'XOR S{0}x{1} I{2} {3}\n'.format(row+1, index+1, intermediate_index, carry2)
                        statement += 'AND I{0} I{1} {2}\n'.format(intermediate_index+1, intermediate_index, carry2)
                        statement += 'AND I{0} {1} {2}\n'.format(intermediate_index+2, val, carry1)
                        statement += 'OR C{0}x{1} I{2} I{3}\n'.format(row+1, index+1, intermediate_index+1, intermediate_index+2)
                        intermediate_index += 3
                    else:
                        # val = x, summ = y, carry = cin
                        summ = 'S{0}x{1}'.format(row, index+1)
                        carry = 'C{0}x{1}'.format(row+1, index)
                        statement += 'XOR I{0} {1} {2}\n'.format(intermediate_index, val, summ)
                        statement += 'XOR S{0}x{1} I{2} {3}\n'.format(row+1, index+1, intermediate_index, carry)
                        statement += 'AND I{0} I{1} {2}\n'.format(intermediate_index+1, intermediate_index, carry)
                        statement += 'AND I{0} {1} {2}\n'.format(intermediate_index+2, val, summ)
                        statement += 'OR C{0}x{1} I{2} I{3}\n'.format(row+1, index+1, intermediate_index+1, intermediate_index+2)

        # Generate Output Netlist
        for row in range(bits+1):
            for column in range(bits):
                index = row + column
                if index == (2 * bits) - 1:
                    statement = statement.replace('C{0}x{1}'.format(row, index-1), 'Z{0}'.format(index))
                elif (row == index) or (row == bits and index > bits):
                    statement = statement.replace('S{0}x{1}'.format(row, index), 'Z{0}'.format(index))

        statement = statement.replace('and0x0', 'Z0')

        with open('umult{0}.txt'.format(bits), 'wb') as w_file:
            w_file.write(statement)

if __name__ == '__main__':
    main()
