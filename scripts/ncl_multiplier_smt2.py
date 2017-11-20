"""Main script used to generate, run, and record execution time of smt2 proofs"""

import timeit
import argparse
import subprocess
from NclDualRailSmt import NclDualRailSmt

def main():
    """Main function"""
    args = parse_arguments()

    ncl_smt_obj = NclDualRailSmt(args.netlist, args.smt2)
    ncl_smt_obj.generate_smt2()

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
