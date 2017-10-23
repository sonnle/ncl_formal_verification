import os
import timeit
import argparse
import subprocess

gate_used = {'th12'     : 0,
             'th13'     : 0,
             'th14'     : 0,
             'th22'     : 0,
             'th23'     : 0,
             'th23w2'   : 0,
             'th24'     : 0,
             'th24comp' : 0,
             'th24w2'   : 0,
             'th24w22'  : 0,
             'th33'     : 0,
             'th33w2'   : 0,
             'th34'     : 0,
             'th34w2'   : 0,
             'th34w22'  : 0,
             'th34w3'   : 0,
             'th34w32'  : 0,
             'th44'     : 0,
             'th44w2'   : 0,
             'th44w22'  : 0,
             'th44w3'   : 0,
             'th44w322' : 0,
             'th54w22'  : 0,
             'th54w32'  : 0,
             'th54w322' : 0,
             'thand0'   : 0,
             'thxor0'   : 0,}

def main():
    args = parse_arguments()

    with open(args.smt2, 'w') as outfile:
        generate_smt2(args.netlist, outfile)

    with open(args.results, 'w') as results_file:
        start = timeit.default_timer()
        results_file.write(subprocess.check_output('z3 -smt2 %s' % args.smt2, shell=True))
        results_file.write('\n\nTotal time: %f sec' % (timeit.default_timer() - start))

def generate_smt2(netlist, outfile):
    outfile.write('; Formal verification proof - input completeness of %s\n' % netlist)
    outfile.write('(set-logic QF_BV)\n\n')

    with open(os.path.join('..', 'templates', 'rail.smt2'), 'r') as rail_file:
        outfile.write(rail_file.read() + '\n')

    with open(netlist, 'r') as netlist_file:
        for line in netlist_file:
            (gate, wires) = line.split(' ', 1)
            if not gate_used[gate]:
                gate_used[gate] = 1
                template_path = os.path.join('..', 'templates', '%s.smt2' % gate)
                template_file = open(template_path, 'r')
                outfile.write(template_file.read() + '\n')
                template_file.close()

    outfile.write('(check-sat)\n')
    outfile.write('(get-model)\n')

def parse_arguments():
    parser = argparse.ArgumentParser(description='Process a semi-netlist of ncl circuit and provide an smt2 proof of input completeness.')
    parser.add_argument('netlist', help='semi-netlist of the ncl circuit')
    parser.add_argument('smt2', help='file for smt2 proof to be written to')
    parser.add_argument('results', help='file to print out z3 results of simulation')

    return parser.parse_args()

if __name__ == '__main__':
    main()

