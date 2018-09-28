import glob
import subprocess

x = glob.glob('*.smt2')
for name in x:
    with open(name, 'r') as rfile:
        y = rfile.read()
        y = y.replace('(I11_1 (th22 I8_1 I9_1 Gc_0))', '(I11_1 (bvand I8_1 I9_1))')
        y = y.replace('(I11_1 (th22 (_ bv0 1) I9_1 Gc_0))', '(I11_1 (bvand (_ bv0 1) I9_1))')
        y = y.replace('(I11_1 (th22 I8_1 (_ bv0 1) Gc_0))', '(I11_1 (bvand I8_1 (_ bv0 1)))')
        with open('mod_'+name, 'w') as wfile:
            wfile.write(y)

z = glob.glob('mod*.smt2')
for name in z:
    try:
        subprocess.check_output('~/z3 -smt2 {0}'.format(name), shell=True)
        print 'sat {0}'.format(name)
    except:
        print 'unsat {0}'.format(name)
