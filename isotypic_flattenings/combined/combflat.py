"""combflat.py -- flattenings that COMBINE several isotypic components of T^{(x)d} (framework, exact mod p).

Setting.  T in A (x) B (x) C (dims n1, n2, n3), given by a rank-r decomposition.  In degree d
    T^{(x)d} in S^d(A (x) B (x) C) = (+)_{lam, mu, nu} S_lam A (x) S_mu B (x) S_nu C (x) M_{lam mu nu},
dim M = g = Kronecker coefficient.  An isotypic flattening uses ONE summand.  Here a flattening is a block matrix

    row blocks    i : source module  S_{lam_i} A^*  (x) X_i,   X_i = C^{k_i}   (auxiliary space)
    column blocks j : target module  S_{mu_j} B (x) S_{nu_j} C (x) Y_j,   Y_j = C^{l_j}
    block (i, j)    : sum_m Psi_ij[m, x, y] F_{ij,m}  (x in X_i, y in Y_j),

F_{ij,m} = isotypic flattening of the component (lam_i, mu_j, nu_j) with the m-th basis functional of M_ij^*
(a zero block if g_ij = 0), Psi_ij in M_ij^* (x) X_i^* (x) Y_j.  This is the flattening of the image of T^{(x)d}
under a GL(A) x GL(B) x GL(C)-equivariant linear map, so its rank is a GL-invariant, lower semicontinuous function
of T: if a general rank-r tensor has smaller rank than a general rank-(r+1) tensor, the minors give equations of
sigma_r that do not vanish on sigma_{r+1}.  Psi says on which side the Kronecker spaces sit:
    one block, k = l = 1        : gN   (one generic functional)
    one block, k = 1, l = g     : HN   (M on the target side)       k = g, l = 1 : VN (M on the source side)
    one block, k, l >= 2        : 'reshaped' (Psi a generic tensor in M^* (x) X^* (x) Y)
    one row block, many columns : fixed lam, a sum over (mu, nu) -- family A (lattice of column spaces, see below)
    one column block, many rows : fixed (mu, nu), a sum over lam -- family B (lattice of row spaces)
(The full sum over all (mu, nu) with k = 1, l_j = g_j is S_lam(T_A): S_lam A^* -> S_lam(B (x) C), rank
 dim S_lam(C^{rank T_A}) -- used as a correctness test.  Tensoring with identities is not implemented yet.)

Evaluation.  Every component is evaluated with hwv_fast (Cauchy-Binet network, exact float64 BLAS mod p), on
SHARED sample points: the rows of all blocks with source lam_i are the same N1_i points g.v of S_lam_i A^*, the
columns of all blocks with target (mu_j, nu_j) the same K_j pairs (g'.v, g''.v).  The sampled block matrix is
P M Q with P = diag(I_{k_i} (x) P_i), Q = diag(I_{l_j} (x) Q_j), and rank(P M Q) = rank M as soon as
    N1_i >= min(n1_i, sum_j l_j n23_j)   and   K_j >= min(n23_j, sum_i k_i n1_i)
(for a block column (j, y) its column space has dim <= min(n1_i, #columns), and a generic evaluation map is
injective on any fixed subspace of at most N1_i dimensions; same for rows).  Sample sizes are fixed per context:
N1 = min(n1, capA, NCAP) + 8 and K = min(n23, capB, KCAP) + 8 with capA(lam) = sum g n23, capB(mu, nu) = sum g n1;
`exact()` reports whether a configuration satisfies the bounds.  With NCAP = KCAP = inf every configuration with
k_i <= g_ij and l_j <= g_ij is exact.

Lattices.  With one source (family A) the rank is the dimension of the SUM of the column spaces of the column
blocks j (subspaces of F_p^{k N1}); with one target (family B) the dimension of the sum of the row spaces of the row
blocks.  Each block is stored once, compressed by a random matrix to a square matrix with the same column (row)
space, so the rank of any sub-sum costs one small rank computation: LatticeFamily.dims(S).

Random streams: tensors as in sweep_fast.py (np.random.default_rng(seed), then rank by rank, factor by factor), so
the same seed and rank list give the same tensors; points, fillings and Psi come from default_rng([seed, tag, ...]).
"""
import os, sys, time, itertools, hashlib
import numpy as np
_HERE = os.path.dirname(os.path.abspath(__file__))
_PARENT = os.path.dirname(_HERE)
if _PARENT not in sys.path:
    sys.path.insert(0, _PARENT)
import hwv                                      # sets isoflat.p = hwv.p = 524287
import hwv_fast
import opt_einsum as oe
from hwv import p, dim_schur, random_fillings
from hwv_fast import build_network, find_path, execute, minors_of_points, minors_of_vectors, fmatmul
from isoflat import partitions, kronecker, modrank

MEMCAP = int(os.environ.get('MEMCAP', str(1 << 25)))   # max elements of a contraction intermediate (else block splitting)
DPMAX = int(os.environ.get('DPMAX', '40'))              # max tensors for the DynamicProgramming (optimal) path; 2*(lam_1+mu_1+nu_1) operands
EXTRA = 8                                               # extra sample points / compression columns
PR1, PR2 = 8, 16                                        # probe size for the choice of independent fillings
FILLPOOL = int(os.environ.get('FILLPOOL', '1500'))      # random fillings scored per component before choosing the cheapest
FILLCHEAP = float(os.environ.get('FILLCHEAP', '1e8'))   # stop enlarging the pool once a filling this cheap (flops) is found

# ----------------------------------------------------------------------------------------------------------------
# exact modular helpers

def mulmod(A, B):
    """exact A @ B mod p for integer arrays with entries in [0, p) (float64 BLAS, chunked by hwv_fast.fmatmul)."""
    A = np.asarray(A); B = np.asarray(B)
    return fmatmul((A % p).astype(np.float64)[None], (B % p).astype(np.float64)[None])[0].astype(np.int64)

def combine(Psi, Fs):
    """sum_m Psi[m] * Fs[m] mod p; Psi (g,) ints, Fs (g, N, K)."""
    out = np.zeros(Fs.shape[1:], dtype=np.int64)
    for c, F in zip(Psi, Fs):
        out = (out + int(c) * F.astype(np.int64)) % p
    return out

def rref(M):
    """reduced row echelon form of M mod p: (R, pivots), R the nonzero rows (float64 holding residues; every update
    a - c*b with a, b, c < p stays < p^2 < 2^53, so the arithmetic is exact)."""
    A = (np.asarray(M) % p).astype(np.float64)
    rows, cols = A.shape
    piv, r = [], 0
    for c in range(cols):
        if r == rows:
            break
        nz = np.flatnonzero(A[r:, c])
        if nz.size == 0:
            continue
        i = r + nz[0]
        if i != r:
            A[[r, i]] = A[[i, r]]
        A[r] = np.mod(A[r] * float(pow(int(A[r, c]), p - 2, p)), p)
        col = A[:, c].copy(); col[r] = 0
        nzr = np.flatnonzero(col)
        if nzr.size:
            A[nzr] = np.mod(A[nzr] - np.outer(col[nzr], A[r]), p)
        piv.append(c); r += 1
    return A[:r], piv

def reduce_rows(V, R, piv):
    """V (rows) modulo the row space of the RREF basis (R, piv): V - V[:, piv] R, exact mod p (V, R may be float32)."""
    if not piv:
        return np.asarray(V, dtype=np.float64) % p
    return np.mod(np.asarray(V, dtype=np.float64) - mulmod(np.asarray(V, dtype=np.float64)[:, piv], R).astype(np.float64), p)

class Echelon:
    """incremental linear independence test mod p (as in sweep_fast.py)."""
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

# ----------------------------------------------------------------------------------------------------------------
# memory-safe evaluation of one flattening (port of sweep_fast.best_path / compute_F without the MAXFLOPS cap)

def best_path(ops, out, cheap=False, repeats=128):
    """contraction path.  2026-10-22: for up to DPMAX operands the optimal path (opt_einsum DynamicProgramming,
    minimize='flops') is tried first: on the d = 8, 9 networks of 455/555 (24..36 operands) it is found in 0.02-0.2 s and
    executes 2-6x faster than the RandomGreedy path, with smaller intermediates; the size-minimising optimum is taken when
    the flop-optimal path exceeds MEMCAP.  RandomGreedy remains the fallback (more operands, or cheap=True probes)."""
    if not cheap and len(ops) <= DPMAX:
        path, info = find_path(ops, out, None, oe.DynamicProgramming(minimize='flops'))
        big = hwv_fast.largest_intermediate(ops, out, path)
        if big > MEMCAP:
            path2, info2 = find_path(ops, out, None, oe.DynamicProgramming(minimize='size'))
            big2 = hwv_fast.largest_intermediate(ops, out, path2)
            if big2 < big:
                path, info, big = path2, info2, big2
        return path, info, big
    path, info = find_path(ops, out, None, 'greedy' if cheap else oe.RandomGreedy(max_repeats=repeats))
    big = hwv_fast.largest_intermediate(ops, out, path)
    if big > MEMCAP and len(ops) <= DPMAX:
        path2, info2 = find_path(ops, out, None, oe.DynamicProgramming(minimize='size'))
        big2 = hwv_fast.largest_intermediate(ops, out, path2)
        if big2 < big:
            path, info, big = path2, info2, big2
    return path, info, big

def _slice_pm(pm, ys, zs):
    return [{l: A[ys] for l, A in pm[0].items()}, {l: A[zs] for l, A in pm[1].items()}, {l: A[zs] for l, A in pm[2].items()}]

def eval_F(f, vm, pm, cheap=False):
    """F[Y, Z] for fillings f, vector minors vm, point minors pm; block splitting when a path exceeds MEMCAP."""
    N1 = next(iter(pm[0].values())).shape[0]; K = next(iter(pm[1].values())).shape[0]
    ops, out = build_network(f, vm, pm)
    path, info, big = best_path(ops, out, cheap=cheap)
    if big <= MEMCAP:
        return execute(ops, out, path).astype(np.int64)
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
            o2, out2 = build_network(f, vm, _slice_pm(pm, slice(0, yb), slice(0, zb)))
            pb, ib, bb = best_path(o2, out2)
            if bb <= MEMCAP:
                break
        total = float(ib.opt_cost) * (-(-N1 // yb)) * (-(-K // zb))
        if best is None or total < best[0]:
            best = (total, yb, zb, pb)
    _, yb, zb, pb = best
    F = np.zeros((N1, K), dtype=np.int64)
    for y0 in range(0, N1, yb):
        for z0 in range(0, K, zb):
            ys, zs = slice(y0, min(N1, y0 + yb)), slice(z0, min(K, z0 + zb))
            o2, out2 = build_network(f, vm, _slice_pm(pm, ys, zs))
            F[ys, zs] = execute(o2, out2, pb)          # the full block's path also fits the smaller edge blocks
    return F

# ----------------------------------------------------------------------------------------------------------------

def fmt(lam):
    return ''.join(map(str, lam)) if max(lam) < 10 else '.'.join(map(str, lam))

class Context:
    """tensors, components, shared sample points, filling bases and (disk-cached) flattening matrices for one
    format, degree, rank list and direction (source factor `dirn`, targets = the other two factors in order)."""

    def __init__(self, ns, d, ranks, seed=5, dirn=0, cache=None, ncap=None, kcap=None, auxmax=1, verbose=True,
                 only_sources=None):
        ns = (ns,) * 3 if isinstance(ns, (int, np.integer)) else tuple(ns)
        self.d, self.ranks, self.seed, self.dirn, self.verbose = d, list(ranks), seed, dirn, verbose
        rng = np.random.default_rng(seed)
        vecs = {r: tuple(rng.integers(0, p, (r, ns[t])) for t in range(3)) for r in self.ranks}
        self.perm = [dirn] + [t for t in range(3) if t != dirn]
        self.ns = tuple(ns[t] for t in self.perm)
        self.vecs = {r: tuple(vecs[r][t] for t in self.perm) for r in self.ranks}
        self.rlo, self.rhi = self.ranks[0], self.ranks[-1]
        self.parts = [partitions(d, self.ns[t]) for t in range(3)]
        self.pidx = [{lam: i for i, lam in enumerate(P)} for P in self.parts]
        # only_sources: keep only components whose source partition is in this list; the sample sizes (capB, K) are
        # then computed for these sources only, which makes targeted searches (e.g. a fixed set of sources) cheaper
        self.only_sources = None if only_sources is None else [tuple(l) for l in only_sources]
        self.g = {}
        for tri in itertools.product(*self.parts):
            if self.only_sources is not None and tri[0] not in self.only_sources:
                continue
            g = kronecker(*tri)
            if g:
                self.g[tri] = g
        self.dim = [{lam: dim_schur(lam, self.ns[t]) for lam in self.parts[t]} for t in range(3)]
        self.sources = sorted({t[0] for t in self.g}, key=lambda l: self.pidx[0][l])
        self.targets = sorted({t[1:] for t in self.g}, key=lambda mn: (self.pidx[1][mn[0]], self.pidx[2][mn[1]]))
        self.capA = {lam: 0 for lam in self.sources}
        self.capB = {mn: 0 for mn in self.targets}
        for (lam, mu, nu), g in self.g.items():
            self.capA[lam] += g * self.n23((mu, nu))
            self.capB[(mu, nu)] += g * self.n1(lam)
        self.ncap = float('inf') if ncap is None else ncap
        self.kcap = float('inf') if kcap is None else kcap
        self.N1 = {lam: int(min(self.n1(lam), self.capA[lam], self.ncap)) + EXTRA for lam in self.sources}
        # auxmax: column samples also cover min(n23, auxmax * n1) for every source of the target, so that family A
        # with a shared source space X = C^k, k <= auxmax, is exact even where k > g_ij
        n1max = {mn: max(self.n1(t[0]) for t in self.g if t[1:] == mn) for mn in self.targets}
        self.K = {mn: int(min(self.n23(mn), max(self.capB[mn], auxmax * n1max[mn]), self.kcap)) + EXTRA for mn in self.targets}
        tag = 'n%s_d%d_s%d_dir%d_r%s_nc%s_kc%s_ax%d' % ('-'.join(map(str, ns)), d, seed, dirn, '-'.join(map(str, self.ranks)),
                                                       self.ncap, self.kcap, auxmax)
        if self.only_sources is not None:
            tag += '_src' + hashlib.md5(repr(sorted(self.only_sources)).encode()).hexdigest()[:8]
        self.cache = None if cache is None else os.path.join(cache, tag)
        if self.cache:
            os.makedirs(self.cache, exist_ok=True)
        self._vm, self._pm_src, self._pm_tgt, self._basis, self._F = {}, {}, {}, {}, {}

    # sizes
    def n1(self, lam):
        return self.dim[0][lam]
    def n23(self, mn):
        return self.dim[1][mn[0]] * self.dim[2][mn[1]]
    def tri_index(self, tri):
        return [self.pidx[t][tri[t]] for t in range(3)]

    # minors of the rank-one factors and of the sample points (all column lengths 1..n_t)
    def vm(self, r):
        if r not in self._vm:
            self._vm[r] = [{l: minors_of_vectors(self.vecs[r][t], l) for l in range(1, self.ns[t] + 1)} for t in range(3)]
        return self._vm[r]
    def pm_src(self, lam):
        if lam not in self._pm_src:
            rng = np.random.default_rng([self.seed, 11, self.dirn, self.pidx[0][lam]])
            G = rng.integers(0, p, (self.N1[lam], self.ns[0], self.ns[0]))
            self._pm_src[lam] = {l: minors_of_points(G, l) for l in range(1, self.ns[0] + 1)}
        return self._pm_src[lam]
    def pm_tgt(self, mn):
        if mn not in self._pm_tgt:
            rng = np.random.default_rng([self.seed, 12, self.dirn, self.pidx[1][mn[0]], self.pidx[2][mn[1]]])
            Gs = [rng.integers(0, p, (self.K[mn], self.ns[t], self.ns[t])) for t in (1, 2)]
            self._pm_tgt[mn] = [{l: minors_of_points(G, l) for l in range(1, self.ns[t] + 1)} for G, t in zip(Gs, (1, 2))]
        return self._pm_tgt[mn]
    def pm(self, tri):
        return [self.pm_src(tri[0])] + self.pm_tgt(tri[1:])

    def basis(self, tri):
        """g fillings of the three diagrams whose functionals on M are linearly independent, chosen to make the
        contraction CHEAP: a pool of FILLPOOL random fillings is scored by the estimated contraction cost of its
        network (shapes only, greedy path, ~2 ms each; the cost varies by a factor 10..1000 between fillings of the
        same component), the fillings are then probed in order of increasing cost on small probe points and the first
        g with linearly independent functionals are kept.  The functional space spanned is the same (for g = 1 the
        matrix is the same up to a scalar), only the cost changes.  2026-10-22: before, the cheapest of 6 random
        fillings was taken; on 455/555 d = 8, 9 components that is 10x..700x more flops and up to 1000x larger
        intermediates than the cheapest of 1500.  The pool grows in chunks of 100 and stops early once the best
        estimate is below FILLCHEAP flops (small components do not pay the scoring overhead)."""
        if tri in self._basis:
            return self._basis[tri]
        g = self.g[tri]
        crng = np.random.default_rng([self.seed, 13, self.dirn] + self.tri_index(tri))
        gp = [crng.integers(0, p, (PR1 if t == 0 else PR2, self.ns[t], self.ns[t])) for t in range(3)]
        pmp = [{l: minors_of_points(gp[t], l) for l in range(1, self.ns[t] + 1)} for t in range(3)]
        vm, pm = self.vm(self.rhi), self.pm(tri)
        pool, seen = [], set()
        while len(seen) < FILLPOOL:
            for _ in range(100):
                f = random_fillings(crng, tri)
                key = repr(f)
                if key in seen:
                    continue
                seen.add(key)
                ops, out = build_network(f, vm, pm)
                path, info = find_path(ops, out, None, 'greedy')
                big = float(info.largest_intermediate)          # opt_einsum's estimate (cheap; execute() may differ slightly)
                # flops, penalised when the largest intermediate exceeds MEMCAP (block splitting)
                pool.append((float(info.opt_cost) * max(1.0, big / MEMCAP), f))
            if min(c for c, _ in pool) < FILLCHEAP:
                break
        pool.sort(key=lambda x: x[0])
        ech, chosen = Echelon(), []
        for c, f in pool:
            v = eval_F(f, vm, pmp, cheap=True).ravel()
            if v.any() and ech.add(v):
                chosen.append(f)
                if len(chosen) == g:
                    break
        tried = len(pool)
        while len(chosen) < g and tried < 60 * g + 100 + FILLPOOL:          # fallback: plain random fillings
            f = random_fillings(crng, tri); tried += 1
            v = eval_F(f, vm, pmp, cheap=True).ravel()
            if v.any() and ech.add(v):
                chosen.append(f)
        if len(chosen) < g:
            raise RuntimeError('only %d of g = %d independent fillings found for %s' % (len(chosen), g, tri))
        if self.verbose and pool:
            print('#   basis %s: pool %d, chosen cost %.1e (pool median %.1e)' % (tri, len(pool),
                  max(c for c, f in pool if any(f is ch for ch in chosen)), np.median([c for c, _ in pool])), file=sys.stderr)
        self._basis[tri] = chosen
        return chosen

    def flats(self, tri, r):
        """array (g, N1, K) of the isotypic flattenings of the component tri = (lam, mu, nu) at the shared sample
        points, one per basis functional, for the rank-r tensor (disk cache if enabled)."""
        key = (tri, r)
        if key in self._F:
            return self._F[key]
        fn = None
        if self.cache:
            fn = os.path.join(self.cache, 'r%d_%s_%s_%s.npy' % (r, fmt(tri[0]), fmt(tri[1]), fmt(tri[2])))
            if os.path.exists(fn):
                F = np.load(fn)
                self._F[key] = F
                return F
        t0 = time.time()
        F = np.stack([eval_F(f, self.vm(r), self.pm(tri)) for f in self.basis(tri)]).astype(np.uint32)
        if fn:
            tmp = '%s.%d.tmp.npy' % (fn, os.getpid())          # process-unique: parallel workers may share the cache
            np.save(tmp, F); os.replace(tmp, fn)
        if self.verbose and time.time() - t0 > 30:
            print('#   flats %s r=%d %s %.0fs' % (tri, r, F.shape, time.time() - t0), file=sys.stderr); sys.stderr.flush()
        self._F[key] = F
        return F

    def drop(self, tris=None):
        """free the in-memory flattenings (all, or those of the given components)."""
        if tris is None:
            self._F.clear()
        else:
            for k in [k for k in self._F if k[0] in tris]:
                del self._F[k]

    # random coefficient tensors Psi in M^* (x) X^* (x) Y (generic; nested in the last index when sliced)
    def psi(self, tri, k, l, tag=0):
        rng = np.random.default_rng([self.seed, 14, self.dirn, tag, k, l] + self.tri_index(tri))
        return rng.integers(1, p, (self.g[tri], k, l))

    # ------------------------------------------------------------------------------------------------------------
    # general block matrix
    def exact(self, rows, cols):
        """True if the sample sizes guarantee the exact rank of the block matrix with row blocks rows = [(lam, k)]
        and column blocks cols = [((mu, nu), l)] (see the module docstring)."""
        C = sum(l * self.n23(mn) for mn, l in cols)
        R = sum(k * self.n1(lam) for lam, k in rows)
        return (all(self.N1[lam] - EXTRA >= min(self.n1(lam), C) for lam, _ in rows) and
                all(self.K[mn] - EXTRA >= min(self.n23(mn), R) for mn, _ in cols))

    def block_matrix(self, rows, cols, r, psis=None, tag=0):
        """the sampled block matrix (sum_i k_i N1_i) x (sum_j l_j K_j) for the rank-r tensor.  psis: optional dict
        (lam, (mu, nu)) -> Psi array (g, k, l); default generic (Context.psi with `tag`)."""
        R = sum(k * self.N1[lam] for lam, k in rows); C = sum(l * self.K[mn] for mn, l in cols)
        M = np.zeros((R, C), dtype=np.int64)
        r0 = 0
        for lam, k in rows:
            c0 = 0
            for mn, l in cols:
                tri = (lam,) + tuple(mn)
                if tri in self.g:
                    Psi = psis[(lam, mn)] if psis and (lam, mn) in psis else self.psi(tri, k, l, tag)
                    Fs = self.flats(tri, r)
                    N1, K = self.N1[lam], self.K[mn]
                    for x in range(k):
                        for y in range(l):
                            M[r0 + x * N1:r0 + (x + 1) * N1, c0 + y * K:c0 + (y + 1) * K] = combine(Psi[:, x, y], Fs)
                c0 += l * self.K[mn]
            r0 += k * self.N1[lam]
        return M

    def block_rank(self, rows, cols, psis=None, tag=0, compress=True):
        """ranks of the block matrix on the rank-r tensors of self.ranks (tuple), and whether they are exact."""
        out = []
        for r in self.ranks:
            M = self.block_matrix(rows, cols, r, psis, tag)
            out.append(compressed_rank(M, np.random.default_rng([self.seed, 15, r])) if compress else modrank(M))
        return tuple(out), self.exact(rows, cols)

def compressed_rank(M, rng):
    """rank of M mod p; a very rectangular M is first multiplied by a random matrix with EXTRA more columns (rows)
    than its smaller side (rank preserved except with probability < p^-EXTRA)."""
    R, C = M.shape
    if C > R + 2 * EXTRA:
        M = mulmod(M, rng.integers(0, p, (C, R + EXTRA)))
    elif R > C + 2 * EXTRA:
        M = mulmod(rng.integers(0, p, (C + EXTRA, R)), M)
    return modrank(M)

# ----------------------------------------------------------------------------------------------------------------
# lattices: one source (family A) or one target (family B)

class LatticeFamily:
    """subspaces of a common ambient space, one per (member, level), for every rank of the context; dims(S) = the
    dimension of the sum over S = [(member, level)] for each rank.

    kind 'A': fixed source lam, aux dimension k on the source side (X = C^k shared by all members); members are the
       targets (mu, nu); level l = dim Y_j (Kronecker space on the target side when k = 1 and l = g_j).  The subspace
       is the column space of the column block j (generic Psi_j in M_j^* (x) X^* (x) C^l; nested in l).
    kind 'B': fixed target (mu, nu), aux dimension l on the target side (shared Y = C^l); members are the sources
       lam; level k = dim X_i (Kronecker space on the source side when l = 1 and k = g_i).  The subspace is the row
       space of the row block i (generic Psi_i in M_i^* (x) X_i^* (x) C^l; nested in k).
    levels: 'ends' (1 and g), 'all' (1..g) or 'full' (g only)."""

    def __init__(self, ctx, kind, key, aux=1, levels='ends', members=None, tag=0):
        self.ctx, self.kind, self.key, self.aux, self.tag = ctx, kind, key, aux, tag
        if kind == 'A':
            cand = [mn for mn in ctx.targets if (key,) + mn in ctx.g]
            self.tri = lambda m: (key,) + m
        else:
            cand = [lam for lam in ctx.sources if (lam,) + tuple(key) in ctx.g]
            self.tri = lambda m: (m,) + tuple(key)
        self.members = cand if members is None else [m for m in members if m in cand]
        self.gm = {m: ctx.g[self.tri(m)] for m in self.members}
        def lv(g):
            return {'ends': sorted({1, g}), 'all': list(range(1, g + 1)), 'full': [g]}[levels]
        self.levels = {m: lv(self.gm[m]) for m in self.members}
        if kind == 'A':
            N1 = ctx.N1[key]
            self.ambient = aux * N1
            self.rankcap = aux * (N1 - EXTRA)          # dims of sums never exceed this (n1 <= N1 - EXTRA)
            self.size = self.ambient                  # compressed matrices: ambient x ambient
        else:
            K = ctx.K[tuple(key)]
            bound = min(aux * (K - EXTRA), sum(self.gm[m] * ctx.n1(m) for m in self.members))
            self.ambient = aux * K
            self.rankcap = bound
            self.size = min(self.ambient, bound + EXTRA)
        self.mats = {r: {} for r in ctx.ranks}
        self._dims = {}
        self.R = None
        self.build()

    def build(self):
        ctx, a, sz = self.ctx, self.aux, self.size
        if self.kind == 'B' and self.size < self.ambient:
            # common right compression of the ambient F^{aux K}: Q (aux K x size)
            self.Q = np.random.default_rng([ctx.seed, 16, ctx.dirn, self.tag, a, ctx.pidx[1][self.key[0]], ctx.pidx[2][self.key[1]]]).integers(0, p, (self.ambient, sz))
        else:
            self.Q = None
        for m in self.members:
            tri = self.tri(m); g = self.gm[m]; top = max(self.levels[m])
            # generic Psi (g, k, l): family A: k = aux, l = level (nested); family B: k = level (nested), l = aux
            Psi = ctx.psi(tri, a, top, self.tag) if self.kind == 'A' else ctx.psi(tri, top, a, self.tag)
            crng = np.random.default_rng([ctx.seed, 17, ctx.dirn, self.tag, a, 0 if self.kind == 'A' else 1] + ctx.tri_index(tri))
            for r in ctx.ranks:
                Fs = ctx.flats(tri, r)
                acc = None
                for lev in range(1, top + 1):
                    if self.kind == 'A':
                        # column block (j, y = lev-1): rows x = 0..a-1 stacked; compress its columns K -> sz
                        blk = np.vstack([combine(Psi[:, x, lev - 1], Fs) for x in range(a)])          # (a N1, K)
                        G = crng.integers(0, p, (blk.shape[1], sz))
                        C = mulmod(blk, G)
                    else:
                        # row block (i, x = lev-1): columns y = 0..a-1 side by side; compress its rows N1 -> sz
                        blk = np.hstack([combine(Psi[:, lev - 1, y], Fs) for y in range(a)])          # (N1, a K)
                        if self.Q is not None:
                            blk = mulmod(blk, self.Q)
                        G = crng.integers(0, p, (sz, blk.shape[0]))
                        C = mulmod(G, blk)
                    acc = C if acc is None else (acc + C) % p
                    if lev in self.levels[m]:
                        self.mats[r][(m, lev)] = acc.astype(np.uint32)

    def dims(self, S):
        """S: iterable of (member, level).  Returns (dim on rank r_1, ..., dim on rank r_last).
        The sum has dim <= h = sum of the single dims (when known), so only the first c = h + EXTRA columns of the
        compressed matrices are summed (they are random combinations already) and the rows are compressed by the
        first c rows of a fixed random matrix: an exact c x c rank instead of size x size, except with probability
        < p^-EXTRA per subset."""
        key = tuple(sorted(S, key=repr))
        if key not in self._dims:
            h = 0
            for s in key:
                d1 = self._dims.get((s,))
                if d1 is None:
                    h = self.size; break
                h += max(d1)
            c = min(self.size, h + EXTRA)
            if c < self.size and self.R is None:
                self.R = np.random.default_rng([self.ctx.seed, 18, self.ctx.dirn, self.tag, self.aux, len(self.members)]).integers(0, p, (self.size, self.size))
            out = []
            for r in self.ctx.ranks:
                M = np.zeros((self.size, c), dtype=np.int64)
                for s in key:
                    M += self.mats[r][s][:, :c]
                M %= p
                if c < self.size:
                    M = mulmod(self.R[:c], M)
                out.append(modrank(M))
            self._dims[key] = tuple(out)
        return self._dims[key]

    def basis_rows(self, r, s):
        """RREF basis (rows in F_p^size) of the subspace of (member, level) s for the rank-r tensor (cached): the column
        space of the compressed matrix for family A, its ROW space for family B (sum over sources)."""
        if not hasattr(self, '_basis'):
            self._basis = {}
        if (r, s) not in self._basis:
            M = self.mats[r][s]
            # stored as float32: residues < p < 2^24 are exact, half the memory of float64 (the exhaustive enumeration of
            # large family-B lattices held several GB of bases per worker)
            self._basis[(r, s)] = rref(M.T if self.kind == 'A' else M)[0].astype(np.float32)
        return self._basis[(r, s)]

    def greedy(self, start, candidates, rng, score):
        """grow S from `start` by one candidate at a time, maximising score(dims) (ties: random); incremental
        (RREF basis of the current sum per rank, candidates reduced modulo it).  Returns the chain [(S, dims)]."""
        ranks = self.ctx.ranks
        cur = {r: (np.zeros((0, self.size)), []) for r in ranks}
        S = []
        for s in start:
            for r in ranks:
                cur[r] = rref(np.vstack([cur[r][0], self.basis_rows(r, s)]))
            S.append(s)
        chain, rest = [], [c for c in candidates if c not in S]
        while rest:
            best = None
            for c in rest:
                red = {r: reduce_rows(self.basis_rows(r, c), *cur[r]) for r in ranks}
                dims = tuple(len(cur[r][1]) + (modrank(red[r]) if red[r].size else 0) for r in ranks)
                key = (score(dims), rng.random())
                if best is None or key > best[0]:
                    best = (key, c, red, dims)
            _, c, red, dims = best
            for r in ranks:
                if red[r].size:
                    cur[r] = rref(np.vstack([cur[r][0], red[r]]))
            S.append(c); rest.remove(c)
            assert tuple(len(cur[r][1]) for r in ranks) == dims
            chain.append((list(S), dims))
        return chain

    def enumerate(self, level, maxmembers=12, callback=None, maxsize=None):
        """every nonempty subset of the members, each at level `level` ('full' = g_m, or an int, capped at the
        member's top level), by a depth-first walk that keeps one RREF basis per rank and adds one member at a time
        (reduce its basis modulo the current one, then back-substitute): 2^m - 1 incremental additions instead of
        2^m rank computations.  maxsize: only subsets with at most that many members.  callback(S, dims) is called
        for every subset; returns the number of subsets."""
        ms = self.members
        if len(ms) > maxmembers:
            raise ValueError('%d members > maxmembers %d' % (len(ms), maxmembers))
        sel = [(m, max(self.levels[m]) if level == 'full' else min(level, max(self.levels[m]))) for m in ms]
        sel = [s if s[1] in self.levels[s[0]] else (s[0], max(l for l in self.levels[s[0]] if l <= s[1])) for s in sel]
        ranks = self.ctx.ranks
        count = [0]
        def add(R, piv, V):
            red = reduce_rows(V, R, piv)
            if not red.size or not red.any():
                return R, piv
            Rn, pn = rref(red)
            if not pn:
                return R, piv
            if piv:
                R = np.mod(R - mulmod(R[:, pn], Rn).astype(np.float64), p)      # clear the new pivot columns
            R2 = np.vstack([R, Rn]).astype(np.float32); p2 = piv + pn       # float32: exact for residues < 2^24
            order = np.argsort(p2)
            return R2[order], [p2[i] for i in order]
        def dfs(i, cur, S):
            if maxsize is not None and len(S) >= maxsize:
                return
            for j in range(i, len(sel)):
                nxt = {r: add(*cur[r], self.basis_rows(r, sel[j])) for r in ranks}
                S2 = S + [sel[j]]
                count[0] += 1
                if callback:
                    callback(S2, tuple(len(nxt[r][1]) for r in ranks))
                dfs(j + 1, nxt, S2)
        dfs(0, {r: (np.zeros((0, self.size)), []) for r in ranks}, [])
        return count[0]

    def exact(self, S):
        """sample sizes guarantee the exact dimension of the sum over S (Context.exact of the block matrix)."""
        if self.kind == 'A':
            return self.ctx.exact([(self.key, self.aux)], [(m, lev) for m, lev in S])
        return self.ctx.exact([(m, lev) for m, lev in S], [(tuple(self.key), self.aux)])

    def full(self, m):
        return (m, max(self.levels[m]))

    def describe(self, S):
        """'[mu,nu + mu',nu':l/g]' (family A) or '[lam + lam':k/g]' (family B); ':l/g' only for a partial level."""
        def one(s):
            m, lev = s
            name = '%s,%s' % (fmt(m[0]), fmt(m[1])) if self.kind == 'A' else fmt(m)
            return name + ('' if lev == self.gm[m] else ':%d/%d' % (lev, self.gm[m]))
        return '[' + ' + '.join(one(s) for s in sorted(S, key=repr)) + ']'
