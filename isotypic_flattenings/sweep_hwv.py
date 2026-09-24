"""python3 sweep_hwv.py n d r_low,r_high  -- isotypic flattening ranks via HWV evaluation, all lam triples."""
import numpy as np, sys, time, itertools
from hwv import *
from isoflat import modrank
n = int(sys.argv[1]); d = int(sys.argv[2]); ranks = [int(x) for x in sys.argv[3].split(',')]
rng = np.random.default_rng(int(sys.argv[4]) if len(sys.argv) > 4 else 5)
SLICE, NSL = (int(sys.argv[5]), int(sys.argv[6])) if len(sys.argv) > 6 else (0, 1)
from specialU import chunked_F
vecs = {r: tuple(rng.integers(0, p, (r, n)) for _ in range(3)) for r in ranks}
found = []
T0 = time.time()
for li, lam in enumerate(itertools.combinations_with_replacement(partitions(d, n), 3)):
    g = kronecker(*lam)
    if g == 0 or li % NSL != SLICE: continue
    t0 = time.time(); res = {}
    for direction in range(3):
        perm = [direction] + [t for t in range(3) if t != direction]
        lam_p = tuple(lam[t] for t in perm)
        n1 = dim_schur(lam_p[0], n); N1 = n1 + 4; K = min(g * n1, dim_schur(lam_p[1], n) * dim_schur(lam_p[2], n)) + 4
        gs = random_gs(rng, n, N1, K)
        fills = []
        tries = 0
        while len(fills) < 2 * g + 2 and tries < 60 * g:
            f = random_fillings(rng, lam_p); tries += 1
            if np.any(chunked_F(lam_p, f, tuple(vecs[ranks[-1]][t] for t in perm), gs)):
                fills.append(f)
        coeffs = [int(c) for c in rng.integers(1, p, len(fills))]
        for r in ranks:
            Fs = [chunked_F(lam_p, f, tuple(vecs[r][t] for t in perm), gs) for f in fills]
            Fgen = sum(c * F for c, F in zip(coeffs, Fs)) % p
            res[(r, direction, 'gen')] = modrank(Fgen)
            if g >= 2:
                res[(r, direction, 'Vstack')] = modrank(np.vstack(Fs))
                res[(r, direction, 'Hstack')] = modrank(np.hstack(Fs))
    keys = sorted({k[1:] for k in res})
    sep = [k for k in keys if res[(ranks[0],) + k] < res[(ranks[1],) + k]]
    summary = ' '.join('%s%d:%s' % (k[1][0], k[0] + 1, '/'.join(str(res[(r,) + k]) for r in ranks)) for k in keys)
    line = "lam=%s g=%d dims=%s  %s  (%.1fs)" % (lam, g, tuple(dim_schur(l, n) for l in lam), summary, time.time() - t0)
    if sep:
        line += "  *** SEPARATES %s" % sep; found.append((lam, sep, {k: res[k] for k in res}))
    print(line); sys.stdout.flush()
print("n=%d d=%d ranks=%s total %.0fs FOUND: %s" % (n, d, ranks, time.time() - T0, [(f[0], f[1]) for f in found]))
