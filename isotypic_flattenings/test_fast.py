"""check hwv_fast.flattening_matrix_fast == hwv.flattening_matrix entry by entry (mod p) and compare timings.
usage: python3 test_fast.py n[,n2,n3] r "lam" [lam ...]"""
import sys, time, numpy as np
from hwv import *
from hwv_fast import flattening_matrix_fast
ns = tuple(int(x) for x in sys.argv[1].split(',')); ns = ns * 3 if len(ns) == 1 else ns; r = int(sys.argv[2])
rng = np.random.default_rng(11)
for lam in [eval(x) for x in sys.argv[3:]]:
    vecs = tuple(rng.integers(0, p, (r, ns[t])) for t in range(3))
    n1 = dim_schur(lam[0], ns[0]); N1 = K = n1 + 4
    gs = random_gs(rng, ns, N1, K)
    for trial in range(2):
        f = random_fillings(rng, lam)
        t0 = time.time(); F0 = flattening_matrix(lam, f, vecs, gs); t1 = time.time()
        F1, info = flattening_matrix_fast(lam, f, vecs, gs, return_info=True); t2 = time.time()
        print(lam, 'equal' if np.array_equal(F0 % p, F1 % p) else 'DIFFERENT', 'nonzero' if F0.any() else 'zero',
              'old %.2fs new %.2fs' % (t1 - t0, t2 - t1), 'flops %.2e maxint %.2e' % (float(info.opt_cost), float(info.largest_intermediate)))
        sys.stdout.flush()
