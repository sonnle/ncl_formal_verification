bits = 10

with open('mod{}.txt'.format(bits), 'w') as w_file:
    # for bit in range(bits):
    #     w_file.write('(X{0} Xi{0})\n'.format(bit))
    # for bit in range(bits):
    #     w_file.write('(Y{0} Yi{0})\n'.format(bit))
    # for bit in range(2 * bits):
    #     w_file.write('(ACC{0} ACCi{0})\n'.format(bit))

    # w_file.write('\n\n\n')
    # for bit in range(bits):
    #     w_file.write('(X{0} (concat (rail1 Xi{0}) (bvnot (rail1 Xi{0}))))\n'.format(bit))
    # for bit in range(bits):
    #     w_file.write('(Y{0} (concat (rail1 Yi{0}) (bvnot (rail1 Yi{0}))))\n'.format(bit))
    # for bit in range(2 * bits):
    #     w_file.write('(ACC{0} (concat (rail1 ACCi{0}) (bvnot (rail1 ACCi{0}))))\n'.format(bit))

    # w_file.write('\n\n\n')
    # for bit in range(2 * bits):
    #     w_file.write('(ACCo{0} (concat (rail1 P{0}) (bvnot (rail1 P{0}))))\n'.format(bit))

    w_file.write('\n\n\n')
    for bit in range(bits):
        w_file.write('(X{0}_1 ((_ extract 1 1) Xi{0}))\n'.format(bit))
    for bit in range(bits):
        w_file.write('(Y{0}_1 ((_ extract 1 1) Yi{0}))\n'.format(bit))
    for bit in range(2 * bits):
        w_file.write('(ACC{0}_1 ((_ extract 1 1) ACCi{0}))\n'.format(bit))

    w_file.write('\n\n\n')
    for bit in range(bits):
        w_file.write('(X{0} (concat X{0}_1 (bvnot X{0}_1)))\n'.format(bit))
    for bit in range(bits):
        w_file.write('(Y{0} (concat Y{0}_1 (bvnot Y{0}_1)))\n'.format(bit))
    for bit in range(2 * bits):
        w_file.write('(ACC{0} (concat ACC{0}_1 (bvnot ACC{0}_1)))\n'.format(bit))

    w_file.write('\n\n\n')
    for bit in range(2 * bits):
        w_file.write('(Z{0}_1 ((_ extract 1 1) S{0}x{0}))\n'.format(bit))

    w_file.write('\n\n\n')
    for bit in range(2 * bits):
        w_file.write('(Z{0} (concat Z{0}_1 (bvnot Z{0}_1)))\n'.format(bit))

    w_file.write('\n\n\n')
    for bit in range(2 * bits):
        w_file.write('(ACCo{0}_1 ((_ extract 1 1) P{0}))\n'.format(bit))

    w_file.write('\n\n\n')
    for bit in range(2 * bits - 1, -1, -1):
        w_file.write('ACCo{0}_1 '.format(bit))
    w_file.write('\n\n\n')
    for bit in range(bits - 1, -1, -1):
        w_file.write('X{0}_1 '.format(bit))
    w_file.write('\n\n\n')
    for bit in range(bits - 1, -1, -1):
        w_file.write('Y{0}_1 '.format(bit))
    w_file.write('\n\n\n')
    for bit in range(2 * bits - 1, -1, -1):
        w_file.write('ACC{0}_1 '.format(bit))
    w_file.write('\n\n\n')
    for bit in range(bits):
        for bit2 in range(bits):
            w_file.write('and{0}x{1}_1 ((_ extract 1 1)\n'.format(bit,bit2))
    w_file.write('\n\n\n')
    for bit in range(bits):
        for bit2 in range(bits):
            w_file.write('(and{0}x{1} (concat and{0}x{1}_1 (bvnot and{0}x{1}_1)))\n'.format(bit, bit2))