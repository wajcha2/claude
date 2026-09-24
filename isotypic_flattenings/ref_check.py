"""python3 ref_check.py "lam" direction [ranks] [seed]
Rank of the flattening computed entirely with the reference implementation hwv.flattening_matrix (no hwv_fast),
for random tensors of the given ranks (one filling; meant for g = 1 components)."""
import sys, time, numpy as np
from hwv import p, dim_schur, random_fillings, random_gs, flattening_matrix
from isoflat import kronecker, modrank
n = 4
lam = eval(sys.argv[1]); dirn = int(sys.argv[2])
ranks = [int(x) for x in sys.argv[3].split(',')] if len(sys.argv) > 3 else [6, 7]
rng = np.random.default_rng(int(sys.argv[4]) if len(sys.argv) > 4 else 99)
perm = [dirn] + [t for t in range(3) if t != dirn]
lam_p = tuple(lam[t] for t in perm)
assert kronecker(*lam) == 1
n1 = dim_schur(lam_p[0], n); N1 = K = n1 + 4
vecs = {r: tuple(rng.integers(0, p, (r, n)) for _ in range(3)) for r in ranks}
gs = random_gs(rng, n, N1, K)
while True:
    f = random_fillings(rng, lam_p)
    if flattening_matrix(lam_p, f, vecs[ranks[-1]], tuple(G[:6] for G in gs)).any():
        break
for r in ranks:
    t0 = time.time()
    F = flattening_matrix(lam_p, f, vecs[r], gs) % p
    print('lam=%s direction %d, reference implementation, rank-%d tensor: flattening rank %d of %dx%d (%.0fs)'
          % (lam, dirn + 1, r, modrank(F), N1, K, time.time() - t0)); sys.stdout.flush()
