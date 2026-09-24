import numpy as np, sys, time
from hwv import *
from isoflat import modrank
n = int(sys.argv[1]); d = int(sys.argv[2]); ranks = [int(x) for x in sys.argv[3].split(',')]
lams = [eval(x) for x in sys.argv[4:]] if len(sys.argv) > 4 else None
rng = np.random.default_rng(5)
vecs = {r: tuple(rng.integers(0, p, (r, n)) for _ in range(3)) for r in ranks}
for lam in (lams or itertools.combinations_with_replacement(partitions(d, n), 3)):
    g = kronecker(*lam)
    if g == 0: continue
    t0 = time.time(); out = {}
    for r in ranks:
        rk = []
        for direction in range(3):
            perm = [direction] + [t for t in range(3) if t != direction]
            lam_p = tuple(lam[t] for t in perm); vecs_p = tuple(vecs[r][t] for t in perm)
            n1 = dim_schur(lam_p[0], n); N1, K = n1 + 4, n1 + 4
            gs = random_gs(rng, n, N1, K)
            F = np.zeros((N1, K), dtype=np.int64)
            for j in range(2 * g + 2):   # generic functional = random combination of fillings
                F = (F + int(rng.integers(1, p)) * flattening_matrix(lam_p, random_fillings(rng, lam_p), vecs_p, gs)) % p
            rk.append(modrank(F))
        out[r] = tuple(rk)
    print("lam=%s g=%d dims=%s %s  (%.1fs)" % (lam, g, tuple(dim_schur(l, n) for l in lam), ' '.join('r%d=%s' % (r, out[r]) for r in ranks), time.time() - t0)); sys.stdout.flush()
