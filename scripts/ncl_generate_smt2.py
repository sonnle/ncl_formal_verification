"""Main script used to generate, run, and record execution time of smt2 proofs"""

import timeit
import argparse
import subprocess
from ncl_smt import NclSmt

def main():
    """Main function"""
    args = parse_arguments()

    ncl_smt_obj = NclSmt(args.netlist, args.smt2)
    ncl_smt_obj.generate_smt2()

    with open(args.results, 'w') as results_file:
        start = timeit.default_timer()
        try:
            results_file.write(subprocess.check_output('z3 -smt2 %s' % args.smt2, shell=True))
            print 'Model returned SAT'
        except subprocess.CalledProcessError as e:
            results_file.write(e.output)
            if 'unsat' in e.output:
                print 'Model returned UNSAT'
            else:
                print 'Model has syntax errors, check results for error'

        results_file.write('\n\nTotal time: %f sec' % (timeit.default_timer() - start))

def parse_arguments():
    """Parse the arguments"""
    parser = argparse.ArgumentParser(description='Process a semi-netlist\
        of ncl circuit and provide an smt2 proof of input completeness.')
    parser.add_argument('netlist', help='semi-netlist of the ncl circuit')
    parser.add_argument('smt2', help='file for smt2 proof to be written to')
    parser.add_argument('results', help='file to print out z3 results of simulation')

    return parser.parse_args()

if __name__ == '__main__':
    main()
