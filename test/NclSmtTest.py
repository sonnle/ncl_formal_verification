import os
import unittest
from NclSmt import NclSmt

class TestHelperFunctions(unittest.TestCase):
    """
    Class used to test all of the helper functions of NclSmt.
    These functions will be prepended with an underscore.
    """
    netlist_file_path = os.path.join('C:\\Users\\Sonny\\Documents\\workspace\\ncl_formal_verification\\test_files\\test_netlist.txt')
    smt2_file_path = os.path.join('C:\\Users\\Sonny\\Documents\\workspace\\ncl_formal_verification\\work\\test_file.smt2')

    ncl_smt = NclSmt(netlist_file_path, smt2_file_path)

    def test_prepend_tabs(self):
        """Method used to test the NclSmt._prepend_tab(self, str, num_tabs=1)"""
        test_str = 'This is a test string'
        for x in range(100):
            self.assertEqual('\t'*x + test_str, self.ncl_smt._prepend_tabs(test_str, x))

if __name__ == '__main__':
    unittest.main()