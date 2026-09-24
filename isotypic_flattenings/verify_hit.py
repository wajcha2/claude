"""python3 verify_hit.py "lam" direction [ranks] [trials] [prime] [seed]
Independent re-check of a separating isotypic flattening found by sweep_fast.py: for each trial draw fresh random
tensors of the given ranks (default 5,6,7,8), fresh evaluation points (N1 = n1 + 4 on the source side and
K = n1 + 4 pairs on the target side) and fresh independent fillings (g of them; the generic functional is a random
combination), and print the rank of the flattening S^{l_dir}V^* -> S^{l_i}V (x) S^{l_j}V for every rank.
Also compares an 8 x 8 block of one flattening matrix with the reference implementation hwv.flattening_matrix
(entry by entry).  Arithmetic mod `prime` (default 524287; must be < 2^19 for the exact float64 contractions)."""
import sys, time, numpy as np
lam = eval(sys.argv[1]); dirn = int(sys.argv[2])
ranks = [int(x) for x in sys.argv[3].split(',')] if len(sys.argv) > 3 else [5, 6, 7, 8]
trials = int(sys.argv[4]) if len(sys.argv) > 4 else 2
q = int(sys.argv[5]) if len(sys.argv) > 5 else 524287
seed = int(sys.argv[6]) if len(sys.argv) > 6 else 1000
assert q < 2 ** 19
import hwv, isoflat, hwv_fast
hwv.p = isoflat.p = hwv_fast.p = q
p = q
from hwv import dim_schur, random_fillings, random_gs, flattening_matrix
from hwv_fast import prepare, build_network, find_path, execute
from isoflat import kronecker, modrank
import opt_einsum as oe

n = 4
perm = [dirn] + [t for t in range(3) if t != dirn]
lam_p = tuple(lam[t] for t in perm)
g = kronecker(*lam)
n1 = dim_schur(lam_p[0], n); N1 = K = n1 + 4
print('lam=%s direction %d: S^%s V^* -> S^%s V (x) S^%s V, dims %s, g=%d, prime %d' % (
    lam, dirn + 1, lam_p[0], lam_p[1], lam_p[2], tuple(dim_schur(l, n) for l in lam_p), g, q)); sys.stdout.flush()

def flat(f, vm, pm):
    ops, out = build_network(f, vm, pm)
    path, info = find_path(ops, out, None, oe.RandomGreedy(max_repeats=64))
    return execute(ops, out, path).astype(np.int64)

rng = np.random.default_rng(seed)
for trial in range(trials):
    t0 = time.time()
    vecs = {r: tuple(rng.integers(0, p, (r, n)) for _ in range(3)) for r in ranks}
    gs = random_gs(rng, n, N1, K)
    pre = {r: prepare(tuple(vecs[r][t] for t in perm), gs) for r in ranks}
    hi = ranks[-1]
    # g fillings with independent flattenings on the highest-rank tensor
    fills, basis = [], []
    while len(fills) < g:
        f = random_fillings(rng, lam_p)
        F = flat(f, *pre[hi])
        if F.any() and modrank(np.array(basis + [F[:24, :24].ravel()])) == len(basis) + 1:
            fills.append(f); basis.append(F[:24, :24].ravel())
    coeffs = [int(c) for c in rng.integers(1, p, g)]
    out = []
    for r in ranks:
        Fs = [flat(f, *pre[r]) for f in fills]
        Fg = np.zeros((N1, K), dtype=np.int64)
        for c, F in zip(coeffs, Fs):
            Fg = (Fg + c * F) % p
        out.append('r%d:%d' % (r, modrank(Fg)))
    print('trial %d: %s  (%.0fs)' % (trial, ' '.join(out), time.time() - t0)); sys.stdout.flush()
# reference implementation on an 8 x 8 block (first filling, rank ranks[1] tensor)
r = ranks[1] if len(ranks) > 1 else ranks[0]
sub = tuple(G[:8] for G in gs)
t0 = time.time()
vp = tuple(vecs[r][t] for t in perm)
F_ref = flattening_matrix(lam_p, fills[0], vp, sub) % p
F_fast = flat(fills[0], *prepare(vp, sub))
print('reference hwv.flattening_matrix on an 8x8 block (rank %d tensor): %s (%.0fs)' % (
    r, 'EQUAL' if np.array_equal(F_ref, F_fast) else 'DIFFERENT', time.time() - t0))
