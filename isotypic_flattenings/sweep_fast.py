"""python3 sweep_fast.py n d r_low,r_high [seed] [worker nworkers] [noV]

Isotypic flattening ranks for all unordered components lam = (l1,l2,l3) of partitions of d with <= n rows and
Kronecker coefficient g > 0, all three flattening directions -- the same quantities as sweep_hwv.py, evaluated with
hwv_fast (exact mod p, entrywise the same flattening matrices as hwv.flattening_matrix):
  gN : generic functional phi on the multiplicity space M (random combination of g independent fillings);
       flattening S^{l_N}V^* -> S^{l_i}V (x) S^{l_j}V,
  HN : (g >= 2) U = M, stacked flattening S^{l_N}V^* -> U^* (x) S^{l_i}V (x) S^{l_j}V,
  VN : (g >= 2, only without noV) U (x) S^{l_N}V^* -> S^{l_i}V (x) S^{l_j}V.
Printed as 'gN:a/b' with a = rank on the random rank-r_low tensor and b = rank on the random rank-r_high tensor.

Differences with sweep_hwv.py (the evaluation scheme is the same: N1 = n_N + 4 random points g.v_{l_N} on the
source side, K = n_N + 4 random pairs (g'.v, g''.v) on the target side, or g*n_N + 4 pairs without noV):
 * exactly g fillings whose functionals are linearly independent (checked on a probe: the isotypic tensor of the
   rank-r_high tensor evaluated at PR1 x PR2 random points), instead of 2g+2 unchecked random fillings; so gN uses a
   generic element of M^* and HN is the full-M flattening.  'span=' reports the dimension reached (= g unless noted);
 * among admissible fillings the ones with the cheapest contraction path are used first;
 * HN is compressed by a random matrix with >= 8 more columns than its maximal rank before the rank computation
   (rank is preserved unless an event of probability < p^-8 occurs);
 * components are processed in increasing order of the cost proxy g * sum_i (n_i + 4)^2 and claimed dynamically
   by the workers (files in CLAIMDIR); every component has its own random stream (seed, component index), and
   the two tensors are drawn from `seed` alone, so they are the same for all workers and all runs with this seed.
Env: MEMCAP (max elements of an intermediate, default 2^25; larger contractions are split into blocks),
     MAXCOST / MAXDIM (skip components whose cost proxy / largest Weyl dimension exceeds the bound),
     RESUME=log1:log2 (skip components already present in these logs), CLAIMDIR (default claims_n<n>_d<d>).
Lines '*** SEPARATES' mark a hit; the last line prints 'FOUND: [...]'."""
import numpy as np, sys, time, itertools, os
import opt_einsum as oe
from hwv import p, dim_schur, random_fillings, random_gs
from hwv_fast import prepare, build_network, find_path, execute, matmul_mod
from isoflat import partitions, kronecker, modrank

n = int(sys.argv[1]); d = int(sys.argv[2]); ranks = [int(x) for x in sys.argv[3].split(',')]
SEED = int(sys.argv[4]) if len(sys.argv) > 4 else 5
WORKER, NWORKERS = (int(sys.argv[5]), int(sys.argv[6])) if len(sys.argv) > 6 else (0, 1)
NOV = len(sys.argv) > 7 and sys.argv[7] == 'noV'
MEMCAP = int(os.environ.get('MEMCAP', str(1 << 25)))
MAXCOST = float(os.environ.get('MAXCOST', 'inf'))
MAXDIM = float(os.environ.get('MAXDIM', 'inf'))
CLAIMDIR = os.environ.get('CLAIMDIR', 'claims_n%d_d%d' % (n, d))
PR1, PR2 = 8, 16                       # probe size (source points x target pairs)
EXTRA = 8                              # extra columns in the random compression of HN
rlo, rhi = ranks[0], ranks[-1]

def cost_proxy(lam, g):
    return g * sum((dim_schur(l, n) + 4) ** 2 for l in lam)

class Echelon:
    """incremental linear independence test mod p."""
    def __init__(self):
        self.rows, self.piv = [], []
    def add(self, v):
        v = np.array(v, dtype=np.int64) % p
        for row, c in zip(self.rows, self.piv):
            if v[c]:
                v = (v - v[c] * row) % p
        nz = np.nonzero(v)[0]
        if nz.size == 0:
            return False
        c = nz[0]
        self.rows.append((v * pow(int(v[c]), p - 2, p)) % p); self.piv.append(c)
        return True

def slice_pm(pm, ys, zs):
    return [{l: A[ys] for l, A in pm[0].items()}, {l: A[zs] for l, A in pm[1].items()}, {l: A[zs] for l, A in pm[2].items()}]

def compute_F(f, vm, pm, path=None, info=None):
    """flattening matrix F[Y, Z]; if the path's largest intermediate exceeds MEMCAP, the evaluation points are
    split into blocks (first over Z, then over Y) until every intermediate fits."""
    N1, K = pm[0][1].shape[0], pm[1][1].shape[0]
    if path is None:
        ops, out = build_network(f, vm, pm)
        path, info = find_path(ops, out, None, oe.RandomGreedy(max_repeats=128))
    if int(info.largest_intermediate) <= MEMCAP:
        ops, out = build_network(f, vm, pm)
        return execute(ops, out, path).astype(np.int64)
    yb, zb = N1, K
    while zb > 8 or yb > 8:
        if zb > 8: zb = (zb + 1) // 2
        else: yb = (yb + 1) // 2
        ops, out = build_network(f, vm, slice_pm(pm, slice(0, yb), slice(0, zb)))
        pb, ib = find_path(ops, out, None, oe.RandomGreedy(max_repeats=128))
        if int(ib.largest_intermediate) <= MEMCAP: break
    F = np.zeros((N1, K), dtype=np.int64)
    for y0 in range(0, N1, yb):
        for z0 in range(0, K, zb):
            ys, zs = slice(y0, min(N1, y0 + yb)), slice(z0, min(K, z0 + zb))
            ops, out = build_network(f, vm, slice_pm(pm, ys, zs))
            if (ys.stop - ys.start, zs.stop - zs.start) == (yb, zb):
                pth = pb
            else:
                pth = find_path(ops, out, None, oe.RandomGreedy(max_repeats=32))[0]
            F[ys, zs] = execute(ops, out, pth)
    return F

def direction(lam, g, dirn, crng):
    perm = [dirn] + [t for t in range(3) if t != dirn]
    lam_p = tuple(lam[t] for t in perm)
    n1 = dim_schur(lam_p[0], n)
    N1 = n1 + 4
    K = (n1 if NOV else min(g * n1, dim_schur(lam_p[1], n) * dim_schur(lam_p[2], n))) + 4
    gs = random_gs(crng, n, N1, K)
    gp = random_gs(crng, n, PR1, PR2)
    V = {r: tuple(vecs[r][t] for t in perm) for r in ranks}
    pre = {r: prepare(V[r], gs) for r in ranks}
    prb = prepare(V[rhi], gp)
    ech, chosen, tried = Echelon(), [], 0
    maxtry = 60 * g + 100
    while len(chosen) < g and tried < maxtry:
        batch = []
        while len(batch) < 2 * (g - len(chosen)) + 4 and tried < maxtry:
            f = random_fillings(crng, lam_p); tried += 1
            ops, out = build_network(f, *prb)
            v = execute(ops, out, find_path(ops, out, None, 'greedy')[0]).ravel()
            if v.any():
                batch.append((f, v))
        scored = []
        for f, v in batch:
            ops, out = build_network(f, *pre[rhi])
            path, info = find_path(ops, out, None, oe.RandomGreedy(max_repeats=32))
            scored.append((float(info.opt_cost), tried, f, v, path, info))
        scored.sort(key=lambda x: x[:2])
        for c, _, f, v, path, info in scored:
            if len(chosen) < g and ech.add(v):
                if c > 1e8:
                    ops, out = build_network(f, *pre[rhi])
                    path, info = find_path(ops, out, None, oe.RandomGreedy(max_repeats=128))
                chosen.append((f, path, info))
    Fs = {r: [compute_F(f, *pre[r], path, info) for f, path, info in chosen] for r in ranks}
    for F in Fs[rhi]:
        assert F.any(), 'accepted filling gives a zero flattening'
    coeffs = [int(c) for c in crng.integers(1, p, len(chosen))]
    res = {}
    R = None
    for r in ranks:
        Fgen = np.zeros((N1, K), dtype=np.int64)
        for c, F in zip(coeffs, Fs[r]):
            Fgen = (Fgen + c * F) % p
        res[(dirn, 'gen')] = res.get((dirn, 'gen'), ()) + (modrank(Fgen),)
        if g >= 2:
            H = np.hstack(Fs[r])
            if H.shape[1] > N1 + EXTRA:
                if R is None:
                    R = crng.integers(0, p, (H.shape[1], N1 + EXTRA))
                H = matmul_mod(H[None], R[None])[0]
            res[(dirn, 'Hstack')] = res.get((dirn, 'Hstack'), ()) + (modrank(H),)
            if not NOV:
                res[(dirn, 'Vstack')] = res.get((dirn, 'Vstack'), ()) + (modrank(np.vstack(Fs[r])),)
    return res, len(chosen), tried

rng = np.random.default_rng(SEED)
vecs = {r: tuple(rng.integers(0, p, (r, n)) for _ in range(3)) for r in ranks}
DONE = set()
for lf in os.environ.get('RESUME', '').split(':'):
    if lf and os.path.exists(lf):
        DONE |= {l.split(' g=')[0] for l in open(lf) if l.startswith('lam=')}
comps = []
for li, lam in enumerate(itertools.combinations_with_replacement(partitions(d, n), 3)):
    g = kronecker(*lam)
    if g:
        comps.append((cost_proxy(lam, g), li, lam, g))
comps.sort()
os.makedirs(CLAIMDIR, exist_ok=True)
print("# sweep_fast n=%d d=%d ranks=%s seed=%d worker %d/%d noV=%s p=%d MEMCAP=%d MAXCOST=%s MAXDIM=%s: %d components, %d already done"
      % (n, d, ranks, SEED, WORKER, NWORKERS, NOV, p, MEMCAP, MAXCOST, MAXDIM, len(comps), len(DONE)))
sys.stdout.flush()
found, skipped = [], []
T0 = time.time()
for cost, li, lam, g in comps:
    if cost > MAXCOST or max(dim_schur(l, n) for l in lam) > MAXDIM:
        skipped.append(lam); continue
    if ('lam=%s' % (lam,)) in DONE:
        continue
    try:
        fd = os.open(os.path.join(CLAIMDIR, str(li)), os.O_CREAT | os.O_EXCL | os.O_WRONLY)
        os.write(fd, ('%d\n' % WORKER).encode()); os.close(fd)
    except FileExistsError:
        continue
    t0 = time.time()
    crng = np.random.default_rng([SEED, li])
    res, spans = {}, []
    for dirn in range(3):
        rd, span, tried = direction(lam, g, dirn, crng)
        res.update(rd); spans.append(span)
    keys = sorted(res)
    sep = [k for k in keys if res[k][0] < res[k][-1]]
    summary = ' '.join('%s%d:%s' % (k[1][0], k[0] + 1, '/'.join(str(x) for x in res[k])) for k in keys)
    line = "lam=%s g=%d dims=%s  %s  span=%s cost=%.2e (%.1fs)" % (lam, g, tuple(dim_schur(l, n) for l in lam), summary,
                                                             ','.join(map(str, spans)), cost, time.time() - t0)
    if sep:
        line += "  *** SEPARATES %s" % sep; found.append((lam, sep))
    print(line); sys.stdout.flush()
print("NOT CHECKED (MAXCOST/MAXDIM filter): %d components: %s" % (len(skipped), skipped))
print("n=%d d=%d ranks=%s worker %d total %.0fs FOUND: %s" % (n, d, ranks, WORKER, time.time() - T0, found))
