"""Main script used to generate smt2 file from converted Pchb_sync netlist """

#import timeit
#import argparse
#import subprocess
from PchbSmt import PchbSmt

def main():
    """Main function"""
#    args = parse_arguments()

    pchb_smt_obj = PchbSmt('test_netlistc17.txt', 'conversionc17.txt')
    pchb_smt_obj.generate_smt2()



if __name__ == '__main__':
    main()
