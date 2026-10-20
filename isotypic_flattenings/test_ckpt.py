"""python3 test_ckpt.py <empty dir>   checkpoint/resume of rankscan.compute_F: interrupt a block evaluation, resume, compare."""
import os, sys, shutil, numpy as np
CK = sys.argv[1]
shutil.rmtree(CK, ignore_errors=True)
os.environ.update(MEMCAP=str(2 ** 12), CKPT=CK, CKPT_EVERY='0', OPENBLAS_NUM_THREADS='1')
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rankscan as R
from hwv import p
n, d, SEED = 4, 6, 5
lam, g = ((3, 2, 1), (3, 2, 1), (4, 1, 1)), None
from isoflat import kronecker
g = kronecker(*lam)
rgen = R.generic_rank(n)
vecs = {r: tuple(np.random.default_rng([SEED, n, r, t]).integers(0, p, (r, n)) for t in range(3)) for r in range(1, rgen + 1)}
crng = np.random.default_rng([SEED, n, d, 0])
D = R.Direction(n, lam, g, 0, crng, vecs, rgen)
r = 6
vm = D.vm(r)
f, path, info = D.fillings[0]
calls = {'k': 0}
orig = R.execute
F_ref = R.compute_F(f, vm, D.pm, path, info)                      # no checkpoint
def boom(*a, **k):
    calls['k'] += 1
    if calls['k'] == 7:
        raise KeyboardInterrupt('simulated restart')
    return orig(*a, **k)
R.execute = boom
name = D.ckpt_name(r, 0)
try:
    R.compute_F(f, vm, D.pm, path, info, ckpt=name)
    print('no interruption?! blocks too few')
except KeyboardInterrupt:
    import json
    print('interrupted; checkpoint at block', json.load(open(name + '.json'))['next'])
R.execute = orig
F_res = R.compute_F(f, vm, D.pm, path, info, ckpt=name)
print('g', g, 'shape', F_ref.shape, 'resumed == reference:', np.array_equal(F_res, F_ref), 'nonzero', np.count_nonzero(F_ref))
# whole profile with checkpoints vs without
P1 = D.profile(r)
print('checkpoint files left after profile:', os.listdir(CK))
R.CKPT = ''
P0 = D.profile(r)
print('profile with ckpt', P1, 'without', P0, 'equal', P1 == P0)
