"""python3 sweep_fast.py n d r_low,r_high [seed] [worker nworkers] [noV]      (n = 4, or n1,n2,n3 such as 4,5,5)

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
     MAXFLOPS (a component one of whose flattenings needs more than this many flops, by the path estimate, is left
       with a line 'lam=... NOT CHECKED (MAXFLOPS ...)' instead of a result; the claim is kept),
     RESUME=log1:log2 (skip components already present in these logs), CLAIMDIR (default claims_n<n>_d<d>).
Lines '*** SEPARATES' mark a hit; the last line prints 'FOUND: [...]'."""
import numpy as np
import hwv_fast, sys, time, itertools, os
import opt_einsum as oe
from hwv import p, dim_schur, random_fillings, random_gs
from hwv_fast import prepare, build_network, find_path, execute, matmul_mod
from isoflat import partitions, kronecker, modrank

ns = tuple(int(x) for x in sys.argv[1].split(','))          # dimensions of the three factors
ns = ns * 3 if len(ns) == 1 else ns
assert len(ns) == 3
d = int(sys.argv[2]); ranks = [int(x) for x in sys.argv[3].split(',')]
SEED = int(sys.argv[4]) if len(sys.argv) > 4 else 5
WORKER, NWORKERS = (int(sys.argv[5]), int(sys.argv[6])) if len(sys.argv) > 6 else (0, 1)
NOV = len(sys.argv) > 7 and sys.argv[7] == 'noV'
MEMCAP = int(os.environ.get('MEMCAP', str(1 << 25)))
DPMAX = int(os.environ.get('DPMAX', '24'))     # max number of tensors for the DynamicProgramming path fallback
MAXCOST = float(os.environ.get('MAXCOST', 'inf'))
MAXDIM = float(os.environ.get('MAXDIM', 'inf'))
MAXFLOPS = float(os.environ.get('MAXFLOPS', 'inf'))

class TooExpensive(Exception):
    """raised by compute_F before any work when the estimated flop count of one flattening exceeds MAXFLOPS"""
ROWCAP = os.environ.get('ROWCAP', '1') == '1'   # cap the number of sampled rows/columns by the rank bounds (noV only)
CLAIMDIR = os.environ.get('CLAIMDIR', 'claims_n%s_d%d' % ('x'.join(map(str, ns)) if len(set(ns)) > 1 else ns[0], d))
PR1, PR2 = 8, 16                       # probe size (source points x target pairs)
EXTRA = 8                              # extra columns in the random compression of HN
rlo, rhi = ranks[0], ranks[-1]

def dims_of(lam):
    return tuple(dim_schur(l, ns[t]) for t, l in enumerate(lam))

def cost_proxy(lam, g):
    """ordering of the components: cheapest first.  COSTMODE=rowcap (default with ROWCAP): g * N1 * K with the
    row/column caps, i.e. small targets first; otherwise the original g * sum_i (n_i + 4)^2."""
    dims = dims_of(lam)
    if ROWCAP and os.environ.get('COSTMODE', 'rowcap') == 'rowcap':
        tot = 0
        for t in range(3):
            n1 = dims[t]; n23 = dims[(t + 1) % 3] * dims[(t + 2) % 3]
            tot += (min(n1, g * n23) + 8) * (min(n1, n23) + 8)
        return g * tot
    return g * sum((x + 4) ** 2 for x in dims)

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

def best_path(ops, out, repeats=128, cheap=False):
    """flop-optimised RandomGreedy path; if its largest intermediate (exact simulation of execute()) exceeds MEMCAP,
    the size-minimising dynamic-programming path is tried and kept when smaller.  RandomGreedy is unseeded and
    occasionally returns a path with an intermediate carrying only word indices (up to r^d elements), which no
    batch splitting can shrink -- that was the cause of 13 GB OOM kills at d = 9."""
    path, info = find_path(ops, out, None, 'greedy' if cheap else oe.RandomGreedy(max_repeats=repeats))   # cheap: probes (8 x 16 points)
    big = hwv_fast.largest_intermediate(ops, out, path)
    if big > MEMCAP and len(ops) <= DPMAX:
        # the DP optimiser's subset table grows exponentially with the number of tensors: 7 GB observed for a d = 14
        # network (block loop, 2508 x 1 points); above DPMAX tensors the RandomGreedy path is kept (more block
        # splitting, identical results)
        path2, info2 = find_path(ops, out, None, oe.DynamicProgramming(minimize='size'))
        big2 = hwv_fast.largest_intermediate(ops, out, path2)
        if big2 < big:
            path, info, big = path2, info2, big2
    return path, info, big

def compute_F(f, vm, pm, path=None, info=None, cheap=False):
    """flattening matrix F[Y, Z]; if the path's largest intermediate exceeds MEMCAP, the evaluation points are
    split into blocks (first over Z, then over Y, down to single points) until every intermediate fits."""
    N1, K = next(iter(pm[0].values())).shape[0], next(iter(pm[1].values())).shape[0]
    ops, out = build_network(f, vm, pm)
    if path is None:
        path, info, big = best_path(ops, out, cheap=cheap)
    else:
        big = hwv_fast.largest_intermediate(ops, out, path)      # exact simulation of execute()
        if big > MEMCAP:
            path, info, big = best_path(ops, out)
    if big <= MEMCAP:
        if info is not None and float(info.opt_cost) > MAXFLOPS:
            raise TooExpensive(float(info.opt_cost))
        return execute(ops, out, path).astype(np.int64)
    # Block splitting.  Two halving orders are tried, Z (target pairs) first and Y (source points) first, each down
    # to the first block shape whose path fits MEMCAP, and the order with the smaller total flop count
    # (flops per block x number of blocks) is used.  The point-independent parts of the network are recomputed in
    # every block, so the total cost depends strongly on which side is cut: for ((9,4),(3,3,3,3,1),(3,3,3,3,1)) at
    # d = 13 (683 x 233 points) Z-first ends at 6 x 1 blocks with 4.2e13 flops, Y-first at 1 x 233 blocks with
    # 5.7e12.  The result F is the same (exact arithmetic, block-wise assembly).
    best = None
    for order in ('Z', 'Y'):
        yb, zb = N1, K
        while zb > 1 or yb > 1:
            if order == 'Z':
                if zb > 1: zb = (zb + 1) // 2
                else: yb = (yb + 1) // 2
            else:
                if yb > 1: yb = (yb + 1) // 2
                else: zb = (zb + 1) // 2
            ops, out = build_network(f, vm, slice_pm(pm, slice(0, yb), slice(0, zb)))
            pb, ib, bb = best_path(ops, out)
            if bb <= MEMCAP: break
        total = float(ib.opt_cost) * (-(-N1 // yb)) * (-(-K // zb))
        if best is None or total < best[0]:
            best = (total, order, yb, zb, pb, ib, bb)
    total, order, yb, zb, pb, ib, bb = best
    print("# blocks: %s-first (%d x %d) of %d x %d, %.2e flops, largest intermediate %.2e" % (order, yb, zb, N1, K, total, bb), file=sys.stderr); sys.stderr.flush()
    if total > MAXFLOPS:
        raise TooExpensive(total)
    if bb > MEMCAP:
        print("# memory: no path within MEMCAP even for 1x1 blocks (largest intermediate %.2e elements); proceeding" % bb, file=sys.stderr); sys.stderr.flush()
    F = np.zeros((N1, K), dtype=np.int64)
    for y0 in range(0, N1, yb):
        for z0 in range(0, K, zb):
            ys, zs = slice(y0, min(N1, y0 + yb)), slice(z0, min(K, z0 + zb))
            ops, out = build_network(f, vm, slice_pm(pm, ys, zs))
            # the full-block path pb is used for the partial edge blocks as well: the network is the same (only the
            # Y/Z dimensions shrink), so every intermediate is at most the full block's, i.e. <= MEMCAP.  The former
            # best_path(ops, out, 32)[0] here returned an UNCHECKED RandomGreedy path; for a d = 9 edge block of 8
            # rows it carried a word-index-only intermediate (r^d elements): 13 GB anon-rss, OOM kill (2026-10-04).
            F[ys, zs] = execute(ops, out, pb)
    return F

def direction(lam, g, dirn, crng):
    perm = [dirn] + [t for t in range(3) if t != dirn]
    lam_p = tuple(lam[t] for t in perm); ns_p = tuple(ns[t] for t in perm)
    n1 = dim_schur(lam_p[0], ns_p[0])
    n23 = dim_schur(lam_p[1], ns_p[1]) * dim_schur(lam_p[2], ns_p[2])
    if ROWCAP and NOV:
        # rank of the generic flattening <= min(n1, n23), of the H-stack <= min(n1, g*n23): sample only that many
        # generic points (+8) on each side; g*K >= min(n1, g*n23) still holds, so H is computed correctly.
        N1 = min(n1, g * n23) + 8
        K = min(n1, n23) + 8
    else:
        N1 = n1 + 4
        K = (n1 if NOV else min(g * n1, n23)) + 4
    gs = random_gs(crng, ns_p, N1, K)
    gp = random_gs(crng, ns_p, PR1, PR2)
    V = {r: tuple(vecs[r][t] for t in perm) for r in ranks}
    pre = {r: prepare(V[r], gs, lams=lam_p) for r in ranks}
    prb = prepare(V[rhi], gp, lams=lam_p)
    ech, chosen, tried = Echelon(), [], 0
    maxtry = 60 * g + 100
    while len(chosen) < g and tried < maxtry:
        batch = []
        while len(batch) < 2 * (g - len(chosen)) + 4 and tried < maxtry:
            f = random_fillings(crng, lam_p); tried += 1
            ops, out = build_network(f, *prb)
            v = compute_F(f, *prb, cheap=True).ravel()      # probe through compute_F: exact memory check with DP-size fallback; plain greedy path (fast)
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
    coeffs = [int(c) for c in crng.integers(1, p, len(chosen))]
    res = {}
    R = None
    # Memory (2026-10-05): the flattenings are computed and consumed one rank at a time (compute_F draws no random
    # numbers, so the random stream is unchanged), and the compression H @ R of the g-fold stack is accumulated block
    # by block in float64 with R kept once as float64, instead of materialising the int64 stack, its float64 copy and an
    # int64 R plus its float64 copy at the same time.  For g = 4, N1 = 9458, K = 3158 (d = 14) that was > 5 GB per worker
    # (a worker was OOM-killed with four of them); the results are identical (exact arithmetic).
    for r in ranks:
        Fs_r = [compute_F(f, *pre[r], path, info) for f, path, info in chosen]
        if r == rhi:
            for F in Fs_r:
                assert F.any(), 'accepted filling gives a zero flattening'
        Fgen = np.zeros((N1, K), dtype=np.int64)
        for c, F in zip(coeffs, Fs_r):
            Fgen = (Fgen + c * F) % p
        res[(dirn, 'gen')] = res.get((dirn, 'gen'), ()) + (modrank(Fgen),)
        del Fgen
        if g >= 2:
            if g * K > N1 + EXTRA:
                if R is None:
                    R = crng.integers(0, p, (g * K, N1 + EXTRA)).astype(np.float64)
                H = None
                for j, F in enumerate(Fs_r):
                    C = hwv_fast.fmatmul((F % p).astype(np.float64)[None], R[None, j * K:(j + 1) * K])[0]
                    if H is None:
                        H = C
                    else:
                        np.add(H, C, out=H); np.fmod(H, p, out=H)
                    del C
                H = H.astype(np.int64)
            else:
                H = np.hstack(Fs_r)
            res[(dirn, 'Hstack')] = res.get((dirn, 'Hstack'), ()) + (modrank(H),)
            del H
            if not NOV:
                res[(dirn, 'Vstack')] = res.get((dirn, 'Vstack'), ()) + (modrank(np.vstack(Fs_r)),)
        del Fs_r
    return res, len(chosen), tried

rng = np.random.default_rng(SEED)
vecs = {r: tuple(rng.integers(0, p, (r, ns[t])) for t in range(3)) for r in ranks}
DONE = set()
for lf in os.environ.get('RESUME', '').split(':'):
    if lf and os.path.exists(lf):
        DONE |= {l.split(' g=')[0] for l in open(lf) if l.startswith('lam=')}
if ns[0] == ns[1] == ns[2]:
    triples = itertools.combinations_with_replacement(partitions(d, ns[0]), 3)
elif ns[1] == ns[2]:        # factors 2 and 3 interchangeable: unordered (l2, l3)
    triples = ((l1, l2, l3) for l1 in partitions(d, ns[0]) for l2, l3 in itertools.combinations_with_replacement(partitions(d, ns[1]), 2))
else:
    triples = itertools.product(*(partitions(d, nt) for nt in ns))
ONLY = None
if os.environ.get('ONLY'):        # file with one component per line, e.g. ((8, 2), (3, 2, 2, 2, 1), (3, 2, 2, 2, 1)); others are skipped
    ONLY = {tuple(tuple(x) for x in eval(l)) for l in open(os.environ['ONLY']) if l.strip()}
comps = []
for li, lam in enumerate(triples):
    if ONLY is not None and tuple(tuple(x) for x in lam) not in ONLY:
        continue                  # skip the Kronecker coefficient too (2 h for the 32509 triples at n=5, d=13); li unchanged
    g = kronecker(*lam)
    if g:
        comps.append((cost_proxy(lam, g), li, lam, g))
comps.sort()
os.makedirs(CLAIMDIR, exist_ok=True)
print("# sweep_fast n=%s d=%d ranks=%s seed=%d worker %d/%d noV=%s p=%d MEMCAP=%d MAXCOST=%s MAXDIM=%s MAXFLOPS=%s: %d components, %d already done"
      % (','.join(map(str, ns)), d, ranks, SEED, WORKER, NWORKERS, NOV, p, MEMCAP, MAXCOST, MAXDIM, MAXFLOPS, len(comps), len(DONE)))
sys.stdout.flush()
found, skipped = [], []
T0 = time.time()
for cost, li, lam, g in comps:
    if cost > MAXCOST or max(dims_of(lam)) > MAXDIM:
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
    try:
        for dirn in range(3):
            rd, span, tried = direction(lam, g, dirn, crng)
            res.update(rd); spans.append(span)
    except TooExpensive as e:
        # recorded with the 'lam=' prefix so that RESUME skips it in later runs of this stage; a later stage with a
        # larger MAXFLOPS drops these lines from its RESUME log (grep -v 'NOT CHECKED') and recomputes them
        print("lam=%s g=%d dims=%s  NOT CHECKED (MAXFLOPS %.1e): one flattening needs %.2e flops  cost=%.2e (%.1fs)"
              % (lam, g, dims_of(lam), MAXFLOPS, e.args[0], cost, time.time() - t0)); sys.stdout.flush()
        skipped.append(lam); continue
    keys = sorted(res)
    sep = [k for k in keys if res[k][0] < res[k][-1]]
    summary = ' '.join('%s%d:%s' % (k[1][0], k[0] + 1, '/'.join(str(x) for x in res[k])) for k in keys)
    line = "lam=%s g=%d dims=%s  %s  span=%s cost=%.2e (%.1fs)" % (lam, g, dims_of(lam), summary,
                                                             ','.join(map(str, spans)), cost, time.time() - t0)
    if sep:
        line += "  *** SEPARATES %s" % sep; found.append((lam, sep))
    print(line); sys.stdout.flush()
print("NOT CHECKED (MAXCOST/MAXDIM/MAXFLOPS filter): %d components: %s" % (len(skipped), skipped))
print("n=%s d=%d ranks=%s worker %d total %.0fs FOUND: %s" % (','.join(map(str, ns)), d, ranks, WORKER, time.time() - T0, found))
