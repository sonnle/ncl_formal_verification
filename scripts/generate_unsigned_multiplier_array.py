n = 4
track_nums = dict()

def main():
    and_statement = generate_and_gates()
    print and_statement

    adders_statement = generate_adders()
    print adders_statement

    out_statement = generate_outputs()
    print out_statement

def generate_and_gates():
    let_statement = '(let\n\t(\n'
    for row in range(n):
        for column in range(n):
            test = row + column
            let_statement += '\t\t(and%dx%d (and2 X%d Y%d))\n' % (row, column, row, column)
            try:
                track_nums[test].append('and%dx%d' % (row, column))
            except KeyError:
                track_nums[test] = ['and%dx%d' % (row, column)]
    let_statement += '\t)\n)'
    return let_statement

def generate_adders():
    let_statement = '(let\n\t(\n\t\t(S0x0 and0x0)\n\t)\n)\n'
    for row in range(n+1):
        if row == 0:
            for column in range(n-1):
                print 'row:%d column:%d' % (row+1, column+1)
                print 'before:'
                print track_nums[row+column+1]
                let_statement += '(let\n\t(\n'
                first_val = track_nums[row+column+1].pop()
                sec_val = track_nums[row+column+1].pop()
                if column == 0:
                    let_statement += '\t\t(S%dx%d (ha %s %s))\n' % \
                        (row+1, row+column+1, first_val, sec_val)
                    let_statement += '\t\t(C%dx%d (ha %s %s))\n' % \
                        (row+1, row+column+1, first_val, sec_val)
                else:
                    let_statement += '\t\t(S%dx%d (fa %s %s C%dx%d))\n' % \
                        (row+1, row+column+1, first_val, sec_val, row+1, row+column)
                    let_statement += '\t\t(C%dx%d (fa %s %s C%dx%d))\n' % \
                        (row+1, row+column+1, first_val, sec_val, row+1, row+column)
                let_statement += '\t)\n)\n'
                print 'after:'
                print track_nums[column+1]
        elif row == n:
            pass
        else:
            for column in range(n-1):
                print 'row:%d column:%d' % (row+1, column+1)
                print track_nums[column+1]
                let_statement += '(let\n\t(\n'
                if column == 0:
                    let_statement += '\t\t(S%dx%d (ha and%dx%d S%dx%d))\n' % \
                        (row+1, row+column+1, row+column+1, 0, row, row+column+1)
                    let_statement += '\t\t(C%dx%d (ha and%dx%d S%dx%d))\n' % \
                        (row+1, row+column+1, row+column+1, 0, row, row+column+1)
                else:
                    first_val = track_nums[column+1].pop()
                    let_statement += '\t\t(S%dx%d (fa %s S%dx%d C%dx%d))\n' % \
                        (row+1, row+column+1, first_val, row, row+column+1, row+1, row+column)
                    let_statement += '\t\t(C%dx%d (fa %s S%dx%d C%dx%d))\n' % \
                        (row+1, row+column+1, first_val, row, row+column+1, row+1, row+column)
                let_statement += '\t)\n)\n'
                print 'after:'
                print track_nums[column+1]

    return let_statement


def generate_outputs():
    let_statement = '(let\n\t(\n'
    for row in range(n+1):
        for column in range(n):
            current = row + column
            if current == n + n - 1:
                let_statement += '\t\t(= Z%d C%dx%d)\n' % (current, row, current-1)
            elif (row == current) or (row == n and current > n):
                let_statement += '\t\t(= Z%d S%dx%d)\n' % (current, row, current)
    let_statement += '\t)\n)'
    return let_statement

if __name__ == '__main__':
    main()

