"""Main script used to generate, run, and record execution time of smt2 proofs"""
import timeit
import subprocess

from NclDualRailSmt import NclDualRailSmt
from SMT2UnsignedMultiplier import SMT2UnsignedMultiplier

def main():
    # Will generate let-statements for n = [1 - bits_to_generate] unsigned multipliers
    bits_to_generate = 20
    num = 3

    results_file = open('results.txt', 'w')

    for bits in range(3, bits_to_generate + 1):
        test = SMT2UnsignedMultiplier(bits)
        file_name = 'unsigned_mult_%dx%d.smt2' % (bits, bits)
        num += 1
        with open(file_name, 'w') as w_file:
            w_file.write(test.generate_let_statement())

        start = timeit.default_timer()
        try:
            results_file.write('Results for %dx%d unsigned multiplier:\n' % (bits, bits))
            results_file.write(subprocess.check_output('z3 -smt2 %s' % file_name, shell=True))
            print 'Model returned SAT'
        except subprocess.CalledProcessError as e:
            results_file.write(e.output)
            if 'unsat' in e.output:
                print 'Model returned UNSAT'
            else:
                print 'Model has syntax errors, check results for error'
        results_file.write('Time taken: %f\n\n\n' % (timeit.default_timer() - start))

    results_file.close()

if __name__ == '__main__':
    main()
