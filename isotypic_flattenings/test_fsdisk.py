"""python3 test_fsdisk.py <empty dir>   rankscan FSDISK (flattenings of a profile in an unlinked memory-mapped file):
(1) profiles equal to the in-memory ones (g >= 2, planned and block evaluation), no file left behind; (2) block mode
with checkpoints written from the mapped matrices, interrupted, resumed by a fresh worker with FSDISK: same profile."""
import os, sys, shutil, numpy as np
W = sys.argv[1]
shutil.rmtree(W, ignore_errors=True)
CK, FD = os.path.join(W, 'ckpt'), os.path.join(W, 'fsdisk')
os.makedirs(CK); os.makedirs(FD)
os.environ.update(CKPT='', OPENBLAS_NUM_THREADS='1')
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rankscan as R
from hwv import p
from isoflat import kronecker


def direction(n, d, lam, r, t=0):
    g = kronecker(*lam)
    vecs = {s: tuple(np.random.default_rng([5, n, s, u]).integers(0, p, (s, n)) for u in range(3))
            for s in range(1, R.generic_rank(n) + 1)}
    return R.Direction(n, lam, g, t, np.random.default_rng([5, n, d, 0]), vecs, r), g


class Stop(Exception):
    pass


ok = True
MEMCAP0 = R.MEMCAP
cases = [(4, 6, ((3, 2, 1), (3, 2, 1), (4, 1, 1)), 6), (5, 6, ((4, 1, 1), (2, 1, 1, 1, 1), (2, 1, 1, 1, 1)), 8),
         (4, 6, ((3, 2, 1), (4, 2), (3, 2, 1)), 6)]
for n, d, lam, r in cases:
    for memcap in (MEMCAP0, 2 ** 10):                      # planned / unblocked, and block mode
        R.MEMCAP = memcap
        R.CKPT, R.FSDISK = '', ''
        D0, g = direction(n, d, lam, r)
        P0 = D0.profile(r)
        R.FSDISK = FD
        D1, _ = direction(n, d, lam, r)
        P1 = D1.profile(r)
        left = os.listdir(FD)
        good = P0 == P1 and not left
        ok &= good
        print('%s %s g=%d MEMCAP=%d: in memory %s, FSDISK %s, files left %s -> %s' % (n, lam, g, memcap, P0, P1, left,
              'ok' if good else 'FAIL'), flush=True)
    # (2) checkpoints from the mapped matrices: block mode, a checkpoint after every block, stopped at the 3rd save
    # (reference without CKPT: a finished profile would be cached and reused instead of evaluated)
    R.MEMCAP, R.CKPT, R.FSDISK = 2 ** 10, '', ''
    R.NEWEVAL = False
    D0, g = direction(n, d, lam, r)
    P0 = D0.profile(r)
    R.CKPT, R.CKPT_EVERY = CK, 0.0
    orig, calls = R._ckpt_save, {'k': 0}

    def stop_at_3(*a, **kw):
        calls['k'] += 1
        if calls['k'] == 3:
            raise Stop()
        return orig(*a, **kw)
    R._ckpt_save = stop_at_3
    R.FSDISK = FD
    D1, _ = direction(n, d, lam, r)
    try:
        D1.profile(r)
        stopped = False
    except Stop:
        stopped = True
    R._ckpt_save = orig
    nck = len([f for f in os.listdir(CK) if f.endswith('.json')])
    R.CKPT_EVERY = 1800.0
    D2, _ = direction(n, d, lam, r)
    P2 = D2.profile(r)
    good = stopped and nck >= 1 and P2 == P0 and not os.listdir(FD)
    ok &= good
    print('%s %s: stopped %s with %d checkpoint(s), resumed with FSDISK %s vs %s -> %s' % (n, lam, stopped, nck, P2, P0,
          'ok' if good else 'FAIL'), flush=True)
    R.NEWEVAL, R.CKPT_EVERY, R.CKPT, R.FSDISK, R.MEMCAP = True, 1800.0, '', '', MEMCAP0
    for f in os.listdir(CK):
        os.remove(os.path.join(CK, f))
print('ALL OK' if ok else 'FAILURES')
