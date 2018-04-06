"""Main script used to generate, run, and record execution time of smt2 proofs"""
import timeit
import subprocess

from NclDualRailSmt import NclDualRailSmt
from SMT2UnsignedMultiplierNull import SMT2UnsignedMultiplierNull
from SMT2UnsignedMultiplierData import SMT2UnsignedMultiplierData

def main():
    # Will generate let-statements for n = [1 - bits_to_generate] unsigned multipliers
    bits_to_generate = 20

    for bits in range(3, bits_to_generate + 1):
        test = SMT2UnsignedMultiplierNull(bits)
        file_name = '../../examples/input_completeness/unsigned_dual_rail_multipliers/generated/unsigned_mult_%dx%d_n2d.smt2' % (bits, bits)
        with open(file_name, 'w') as w_file:
            w_file.write(test.generate_proof())

        # try:
        #     results_file = open('results.txt', 'a')
        #     results_file.write('Results for %dx%d unsigned multiplier NULL:\n' % (bits, bits))
        #     start = timeit.default_timer()
        #     results_file.write(subprocess.check_output('z3.exe -smt2 %s' % file_name, shell=True))
        #     print 'Model returned SAT'
        # except subprocess.CalledProcessError as e:
        #     results_file.write(e.output)
        #     if 'unsat' in e.output:
        #         print 'Model returned UNSAT for %dx%d unsigned multiplier NULL' % (bits, bits)
        #     else:
        #         print 'Model has syntax errors, check results for error'
        # results_file.write('Time taken: %f\n\n\n' % (timeit.default_timer() - start))
        # results_file.close()

    bits_to_generate = 20
    for bits in range(3, bits_to_generate + 1):
        test = SMT2UnsignedMultiplierData(bits)
        file_name = '../../examples/input_completeness/unsigned_dual_rail_multipliers/generated/unsigned_mult_%dx%d_d2n.smt2' % (bits, bits)
        with open(file_name, 'w') as w_file:
            w_file.write(test.generate_proof())

        # try:
        #     results_file = open('results.txt', 'a')
        #     results_file.write('Results for %dx%d unsigned multiplier DATA:\n' % (bits, bits))
        #     start = timeit.default_timer()
        #     results_file.write(subprocess.check_output('z3.exe -smt2 %s' % file_name, shell=True))
        #     print 'Model returned SAT'
        # except subprocess.CalledProcessError as e:
        #     results_file.write(e.output)
        #     if 'unsat' in e.output:
        #         print 'Model returned UNSAT for %dx%d unsigned multiplier DATA' % (bits, bits)
        #     else:
        #         print 'Model has syntax errors, check results for error'
        # results_file.write('Time taken: %f\n\n\n' % (timeit.default_timer() - start))
        # results_file.close()

if __name__ == '__main__':
    main()
