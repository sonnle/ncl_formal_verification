def main():
    write_file = open('test.txt', 'w')
    num_x_bits = 3
    num_y_bits = 3

    current_index = 0
    write_file.write('(let\n')
    write_file.write('\t(\n')

    ha_signal = []

    for partial_product in range(num_x_bits + num_y_bits - 1):
        index = partial_product
        while index >= 0:
            x_val = partial_product - index
            y_val = index
            if x_val < num_x_bits and y_val < num_y_bits:
                write_file.write('\t\t(I%d (and2 X%d Y%d Gc_0 Gc_0))\n' % (current_index, partial_product-index, index))
                current_index += 1
            index -= 1
        if partial_product <= num_x_bits:
            ha_signal.append(current_index - 1)

    print ha_signal
    write_file.write('\t)\n')

    for column in range(num_x_bits):
        for row in range(num_y_bits - 1):
            write_file.write('(let\n')
            write_file.write('\t(\n')
            if not row:
                write_file.write('\t\t(I%d ((_ extract 3 2) (ha I%d I%d Gc_0 Gc_0 Gc_0 Gc_0)))\n' % (current_index, ha_signal[column + 1], 0))
                write_file.write('\t\t(I%d ((_ extract 1 0) (ha I%d I%d Gc_0 Gc_0 Gc_0 Gc_0))))\n' % (current_index + 1, ha_signal[column + 1], 0))
            else:
                write_file.write('\t\t(I%d ((_ extract 3 2) (fa I%d I%d I%d Gc_0 Gc_0 Gc_0 Gc_0)))\n' % (current_index, 0, 0, current_index - 1))
                write_file.write('\t\t(I%d ((_ extract 1 0) (fa I%d I%d I%d Gc_0 Gc_0 Gc_0 Gc_0))))\n' % (current_index + 1, 0, 0, current_index - 1))
            current_index += 2

    write_file.close()

if __name__ == '__main__':
    main()