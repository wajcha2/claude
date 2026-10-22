"""python3 recheck_sep.py n d 'lam' t r1,r2,... seed1,seed2,...
Independent recheck of a separation found by rankscan.py: the profile (H_k, V_k ranks, k = 1..g) of direction t of
component lam on random rank-r tensors, with other seeds than the scan (other random tensors, evaluation points,
fillings and generic subspaces U_k).  One line per (seed, r)."""
import os, sys, time, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('CKPT', '')
import rankscan as R
from hwv import p

n, d, lam, t = int(sys.argv[1]), int(sys.argv[2]), eval(sys.argv[3]), int(sys.argv[4])
rs = [int(x) for x in sys.argv[5].split(',')]
seeds = [int(x) for x in sys.argv[6].split(',')]
allc = {l: (i, g) for i, l, g in R.components(n, d)}
li, g = allc[lam]
print('# recheck n=%d d=%d lam=%s g=%d direction %d ranks %s seeds %s (scan: seed 5)' % (n, d, lam, g, t, rs, seeds), flush=True)
for seed in seeds:
    vecs = {r: tuple(np.random.default_rng([seed, n, r, u]).integers(0, p, (r, n)) for u in range(3)) for r in rs}
    D = R.Direction(n, lam, g, t, np.random.default_rng([seed, n, d, li]), vecs, max(rs))
    print('seed %d: n1 %d n23 %d N1 %d K %d span %d (bounds H %s V %s)' % (seed, D.n1, D.n23, D.N1, D.K, D.span, D.ubH, D.ubV),
          flush=True)
    for r in rs:
        t0 = time.time()
        P = D.profile(r)
        print('seed %d r=%d H=%s V=%s  %.0fs' % (seed, r, P['H'], P['V'], time.time() - t0), flush=True)
