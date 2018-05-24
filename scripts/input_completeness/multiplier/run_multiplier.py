import timeit
import subprocess

from UMultProofNull import UMultProofNull
from UMultProofData import UMultProofData

from UMultProofNullBuggy import UMultProofNullBuggy
from UMultProofDataBuggy import UMultProofDataBuggy

from UMultProofNullRelax import UMultProofNullRelax
from UMultProofDataRelax import UMultProofDataRelax

from UMultProofNullRelaxBuggy import UMultProofNullRelaxBuggy
from UMultProofDataRelaxBuggy import UMultProofDataRelaxBuggy

def main():
    start_bit = 11
    num_bits_end = 15
    num_bits = num_bits_end + 1

    test_times = [
        [],[],
        [],[],
        [],[],
        [],[],
    ]

    for bits in range(start_bit, num_bits):
        test_obj = [
            UMultProofNullBuggy(bits),
            UMultProofDataBuggy(bits),
            UMultProofNullRelaxBuggy(bits),
            UMultProofDataRelaxBuggy(bits),
            UMultProofNull(bits),
            UMultProofData(bits),
            UMultProofNullRelax(bits),
            UMultProofDataRelax(bits),
        ]

        test_smt_name = [
            'umult{0}x{0}_n2d_buggy.smt2',
            'umult{0}x{0}_d2n_buggy.smt2',
            'umult{0}x{0}_n2d_relax_buggy.smt2',
            'umult{0}x{0}_d2n_relax_buggy.smt2',
            'umult{0}x{0}_n2d.smt2',
            'umult{0}x{0}_d2n.smt2',
            'umult{0}x{0}_n2d_relax.smt2',
            'umult{0}x{0}_d2n_relax.smt2',
        ]


        for index, test in enumerate(test_obj):
            current_file_name = test_smt_name[index].format(bits)
            with open(current_file_name, 'w') as w_file:
                w_file.write(test.generate_smt_proof())

            try:
                results_file = open('results.txt', 'a')
                results_file.write('Results for {0}:\n'.format(current_file_name))
                start = timeit.default_timer()
                results_file.write(subprocess.check_output('z3.exe -smt2 {0}'.format(current_file_name), shell=True))
                print 'Model returned SAT for {0}'.format(current_file_name)
            except subprocess.CalledProcessError as e:
                results_file.write(e.output)
                if 'unsat' in e.output:
                    print 'Model returned UNSAT for {0}'.format(current_file_name)
                else:
                    print 'Model has syntax errors, check results for error'
            time_taken = timeit.default_timer() - start
            results_file.write('Time taken: %.3f\n\n' % (time_taken))
            test_times[index].append('%.3f' % (time_taken))
            results_file.close()

        for index, time_list in enumerate(test_times):
            time_file_name = 'runtime_' + test_smt_name[index].format('N').rstrip('.smt2') + '.txt'
            with open(time_file_name, 'a') as w_file:
                for time in time_list:
                    w_file.write(time + '\n')

if __name__ == '__main__':
    main()