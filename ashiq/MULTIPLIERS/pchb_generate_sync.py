"""Main script used to generate, run, and record execution time of smt2 proofs"""

#import timeit
#import argparse
#import subprocess
from pchb_syncc import PchbSync
import sys

def main():
    """Main function"""
    print 'Print information here'
    
    pchb_sync_obj = PchbSync('test_netlist8x8.txt', 'pchbtosync8x8.txt','connection8x8.txt','graph.txt')
    
#    print pchb_sync_obj.inputs
#    print pchb_sync_obj.outputs
#    print pchb_sync_obj.comp_info[2]
##    print pchb_sync_obj.gate_info[2]
##    print pchb_sync_obj.gate_info[3]
##    print pchb_sync_obj.gate_inputs_number
##    print pchb_sync_obj.gate_info[3]
    

    pchb_sync_obj.generate_pchbtosyn()
    pchb_sync_obj.connection_file()
#    pchb_sync_obj.graph_structure()



if __name__ == '__main__':
    main()
