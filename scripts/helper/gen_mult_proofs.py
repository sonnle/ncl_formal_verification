import subprocess

for i in range(3, 21):
    subprocess.call('python prove_ic_obs_equiv.py ./ncl_umult/umult{0}.txt ./sync_umult/umult{0}.txt'.format(i), shell=True)