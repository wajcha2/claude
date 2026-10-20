"""python3 test_ckpt.py <empty dir>   checkpoint/resume of rankscan: (1) interrupt a block evaluation, resume, compare;
(2) g = 1: a restarted worker that chose another filling adopts the checkpoint's filling, same profile."""
import os, sys, shutil, numpy as np
CK = sys.argv[1]
shutil.rmtree(CK, ignore_errors=True)
os.environ.update(MEMCAP=str(2 ** 12), CKPT=CK, CKPT_EVERY='0', OPENBLAS_NUM_THREADS='1')
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rankscan as R
from hwv import p, random_fillings
from isoflat import kronecker
SEED = 5


def direction(n, d, lam, r):
    g = kronecker(*lam)
    rgen = R.generic_rank(n)
    vecs = {s: tuple(np.random.default_rng([SEED, n, s, t]).integers(0, p, (s, n)) for t in range(3)) for s in range(1, rgen + 1)}
    return R.Direction(n, lam, g, 0, np.random.default_rng([SEED, n, d, 0]), vecs, r), g


class Stop(Exception):
    pass


def interrupt_after(k):
    orig, calls = R.execute, {'k': 0}
    def boom(*a, **kw):
        calls['k'] += 1
        if calls['k'] == k:
            raise Stop()
        return orig(*a, **kw)
    R.execute = boom
    return orig


# (1) g = 4 component: interrupt, resume, compare with an uninterrupted evaluation
D, g = direction(4, 6, ((3, 2, 1), (3, 2, 1), (4, 1, 1)), 6)
r = 6
vm = D.vm(r)
f, path, info = D.fillings[0]
F_ref = R.compute_F(f, vm, D.pm, path, info)
orig = interrupt_after(7)
name = D.ckpt_name(r, 0)
try:
    R.compute_F(f, vm, D.pm, path, info, ckpt=name)
except Stop:
    pass
R.execute = orig
F_res = R.compute_F(f, vm, D.pm, path, info, ckpt=name)
print('(1) g', g, 'resumed == reference:', np.array_equal(F_res, F_ref))
P1 = D.profile(r)
print('    checkpoint files left after profile:', os.listdir(CK))
R.CKPT = ''
P0 = D.profile(r)
print('    profile with ckpt == without:', P1 == P0)
R.CKPT = CK

# (2) g = 1 component: worker A is interrupted; worker B chose another filling; B adopts A's filling and resumes
lam = ((4, 1, 1), (2, 1, 1, 1, 1), (2, 1, 1, 1, 1))
r = 8
A, g = direction(5, 6, lam, r)
R.CKPT = ''
P_ref = A.profile(r)
R.CKPT = CK
orig = interrupt_after(5)
try:
    A.profile(r)
except Stop:
    pass
R.execute = orig
print('(2) g', g, 'checkpoint after interruption:', sorted(x for x in os.listdir(CK) if x.endswith('.json')))
B, _ = direction(5, 6, lam, r)
rng = np.random.default_rng(99)
vmr = B.vm(r)
while True:                                   # another filling with a nonzero highest weight vector
    f2 = random_fillings(rng, B.lam_p)
    if R._plain(f2) != R._plain(B.fillings[0][0]) and R.compute_F(f2, vmr, B.pm).any():
        break
B.fillings[0] = [f2, None, None]
P_B = B.profile(r)
print('    profile after adopting == reference:', P_B == P_ref, P_B, 'files left:', os.listdir(CK))
