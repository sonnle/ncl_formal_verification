"""Main script used to generate smt2 file from converted Pchb_sync netlist """

#import timeit
#import argparse
#import subprocess
from PchbSmt import PchbSmt

def main():
    """Main function"""
#    args = parse_arguments()

    pchb_smt_obj = PchbSmt('test_netlist8x8.txt', 'conversion8x8.txt')
    pchb_smt_obj.generate_smt2()



if __name__ == '__main__':
    main()
