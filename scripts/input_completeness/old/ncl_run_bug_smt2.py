import timeit
import subprocess

def main():
    bits_to_generate = 20
    for bits in range(18, bits_to_generate + 1):
        results_file = open('results_relax.txt', 'a')

        file_name = '../../examples/input_completeness/unsigned_dual_rail_multipliers/generated/unsigned_mult_%dx%d_n2d.smt2' % (bits, bits)
        results_file.write('Results for %dx%d unsigned multiplier NULL to DATA:\n' % (bits, bits))

        try:
            start = timeit.default_timer()
            results_file.write(subprocess.check_output('z3.exe -smt2 %s' % file_name, shell=True))
            print 'Model returned SAT'
        except subprocess.CalledProcessError as e:
            if 'unsat' in e.output:
                print 'Model returned UNSAT for %dx%d unsigned multiplier NULL' % (bits, bits)
            else:
                print 'Model has syntax errors, check results for error'

        results_file.write('Time taken: %f\n\n\n' % (timeit.default_timer() - start))

        # file_name = '../../examples/input_completeness/unsigned_dual_rail_multipliers/generated/unsigned_mult_%dx%d_d2n.smt2' % (bits, bits)
        # results_file.write('Results for %dx%d unsigned multiplier DATA to NULL:\n' % (bits, bits))
        # try:
        #     start = timeit.default_timer()
        #     results_file.write(subprocess.check_output('z3.exe -smt2 %s' % file_name, shell=True))
        #     print 'Model returned SAT'
        # except subprocess.CalledProcessError as e:
        #     if 'unsat' in e.output:
        #         print 'Model returned UNSAT for %dx%d unsigned multiplier DATA' % (bits, bits)
        #     else:
        #         print 'Model has syntax errors, check results for error'

        # results_file.write('Time taken: %f\n\n\n' % (timeit.default_timer() - start))

        results_file.close()

if __name__ == '__main__':
    main()