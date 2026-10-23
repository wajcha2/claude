"""python3 rankscan.py n d                      (all options through environment variables, see below)

Which tensor ranks do the isotypic flattenings of degree d separate, for C^n (x) C^n (x) C^n?

For every unordered component lam = (l1, l2, l3) of partitions of d with <= n rows and Kronecker coefficient g > 0
and every flattening direction t (two directions exchanged by a symmetry l_t = l_u of lam are computed once):
  * g fillings with linearly independent functionals give a basis F_1..F_g of the isotypic flattenings
    (selection exactly as in sweep_fast.py: probe on PR1 x PR2 random points, cheapest contraction paths first);
  * a random g x g matrix C gives generic functionals phi_j = sum_i C[j,i] F_i, and U_k = span(phi_1..phi_k) is a
    generic k-dimensional subspace of the multiplicity space M^* for every k = 1..g.  For each k:
        H_k : S^{l_t}V^* -> U_k^* (x) S^{l_u}V (x) S^{l_v}V   (blocks phi_1..phi_k side by side; rank <= min(n_t, k n_uv))
        V_k : U_k (x) S^{l_t}V^* -> S^{l_u}V (x) S^{l_v}V     (blocks stacked;             rank <= min(k n_t, n_uv))
    H_1 = V_1 is the flattening of one generic functional ('gN' of sweep_fast.py), H_g = 'HN', V_g = 'VN'.
    The ranks of all prefixes k = 1..g come from one incremental exact elimination (class RREF).
  * sampling: N1 = min(n_t, g n_uv) + 8 random source points and K = min(g n_t, n_uv) + 8 random target pairs, so
    that every H_k and V_k keeps its rank under the (generic) restriction to the sampled points.
Tensor ranks: T_r = random rank-r tensor (r = 1..r_gen, drawn from SEED and r only: the same tensors for every
component).  rho(r) = (ranks of all H_k, V_k at T_r) is non-decreasing in r (sigma_r is contained in sigma_{r+1}),
so it is evaluated only at a few r: from RLO upwards with doubling steps until every rank reaches its upper bound
min(...) above ("saturated": then rho is constant from there on) or the last needed rank, and then intervals [a, b]
with rho(a) != rho(b) are bisected.  Equal ends prove that nothing changes inside.  Only pairs (r, r+1) with r in
NEED are resolved.  'SEPARATES r' means rho_c(r) < rho_c(r+1) for some configuration c = (direction, H|V, k).
All arithmetic is exact mod p = 524287 (hwv.py), with the evaluator of hwv_fast.py (Cauchy-Binet network, exact
float64 BLAS).  Feasibility: an evaluation at rank r is skipped (status 'unknown') if a word-minor tensor
C(n, ell) * r^ell exceeds WCAP elements (that tensor cannot be split into blocks).

Output: one JSON object per component and line in OUT (default scan/n<n>_d<d>.jsonl) with the profiles at the
evaluated ranks, the separations, the unknown pairs, wall/CPU time per component and peak RSS (VmHWM, reset per
component).  A readable line per component goes to stdout.
Env: NEED (comma list of r; default 1..r_gen-1), RLO (default min NEED), SEED (5), WORKER/NWORKERS (0/1),
     LIST (file with the components to do, one repr per line, in this order; default all, cheapest first),
     CLAIMDIR (claim files; default scan/claims_n<n>_d<d>), RESUME (':'-separated jsonl files to skip),
     MEMCAP (2^25, elements of an intermediate), WCAP (2^26), DPMAX (24), VSTACK (1 = compute V_k)."""
import numpy as np, sys, os, time, json, itertools, resource
from math import comb
import opt_einsum as oe
import hwv_fast
from hwv import p, dim_schur, random_fillings, random_gs
from hwv_fast import build_network, find_path, execute, minors_of_points, minors_of_vectors
from isoflat import partitions, kronecker

MEMCAP = int(os.environ.get('MEMCAP', str(1 << 25)))
WCAP = int(os.environ.get('WCAP', str(1 << 26)))
DPMAX = int(os.environ.get('DPMAX', '24'))
VSTACK = os.environ.get('VSTACK', '1') == '1'
PR1 = 8
ENDS = float(os.environ.get('ENDS', '16'))   # resolve(): ends-first when size(top rank) <= ENDS * size(lowest rank)
EXTRA = 8
ONEROW = os.environ.get('ONEROW', '1') == '1'   # closed-form fast path for components ((d), mu, mu)
COLWEDGE = os.environ.get('COLWEDGE', '1') == '1'   # closed-form fast path for components (lam, lam^T, (1^d))
SATPROBE = int(os.environ.get('SATPROBE', '1'))           # probe the highest feasible rank when the needed ranks are not
SATPROBE_GAP = int(os.environ.get('SATPROBE_GAP', '4'))    # ... and at most this many below the lowest needed rank
CKPT = os.environ.get('CKPT', '')                         # checkpoint directory for long block evaluations ('' = off)
CKPT_EVERY = float(os.environ.get('CKPT_EVERY', '1800'))  # s between checkpoints of a block evaluation
CUT = os.environ.get('CUT', '1') == '1'                    # resolve(): adjacent ends decided on a leading block of F


def generic_rank(n):
    """generic rank of C^n (x) C^n (x) C^n (Lickteig; n = 3 is the exception: 5)."""
    return 5 if n == 3 else -(-n ** 3 // (3 * n - 2))


def col_lengths(l):
    return sorted({sum(1 for x in l if x > j) for j in range(l[0])})


# ---------------------------------------------------------------- minors by Laplace recursion
# Same arrays as hwv_fast.minors_of_points / minors_of_vectors (which expand all ell! permutations over n^ell or
# r^ell index tuples: infeasible for n >= 6), computed level by level: a k x k minor is expanded along its last
# row (vectors) or last column (points) into (k-1) x (k-1) minors.  Cost ~ sum_k k C(n,k) (B or r^k).
_sub_cache = {}


def _subsets(n, k):
    """combinations(range(n), k) in lexicographic order, and for k >= 1 the index table drop[J, b] = index of
    J minus its b-th element among the (k-1)-subsets."""
    key = (n, k)
    if key not in _sub_cache:
        S = list(itertools.combinations(range(n), k))
        if k >= 1:
            prev = {J: i for i, J in enumerate(itertools.combinations(range(n), k - 1))}
            drop = np.array([[prev[J[:b] + J[b + 1:]] for b in range(k)] for J in S], dtype=np.int64)
            elem = np.array(S, dtype=np.int64)
        else:
            drop = elem = None
        _sub_cache[key] = (S, drop, elem)
    return _sub_cache[key]


def point_minors(G, ell):
    """P[b, I] = det G[b][I, :ell] for I in combinations(range(n), ell) (float64 residues)."""
    G = np.asarray(G, dtype=np.int64) % p
    B, n, _ = G.shape
    P = np.ones((B, 1), dtype=np.int64)
    for k in range(1, ell + 1):
        S, drop, elem = _subsets(n, k)
        col = G[:, :, k - 1]                                   # (B, n)
        Q = np.zeros((B, len(S)), dtype=np.int64)
        for a in range(k):
            sgn = 1 if (a + k - 1) % 2 == 0 else -1
            Q = (Q + sgn * ((P[:, drop[:, a]] * col[:, elem[:, a]]) % p)) % p
        P = Q
    return P.astype(np.float64)


def vector_minors(V, ell):
    """M[I, s_1..s_ell] = det V[s_*, I] for I in combinations(range(n), ell), s in [r]^ell (float64 residues)."""
    V = np.asarray(V, dtype=np.int64) % p
    r, n = V.shape
    M = np.ones((1, 1), dtype=np.int64)                        # (r^(k-1), C(n,k-1))
    for k in range(1, ell + 1):
        S, drop, elem = _subsets(n, k)
        Q = np.zeros((M.shape[0], r, len(S)), dtype=np.int64)
        for b in range(k):
            sgn = 1 if (k - 1 + b) % 2 == 0 else -1
            Q = (Q + sgn * ((M[:, drop[:, b]][:, None, :] * V[:, elem[:, b]][None, :, :]) % p)) % p
        M = Q.reshape(M.shape[0] * r, len(S))
    return np.ascontiguousarray(M.T.reshape((M.shape[1],) + (r,) * ell)).astype(np.float64)


minors_of_points = point_minors        # noqa: F811  (used below instead of the hwv_fast versions)
minors_of_vectors = vector_minors       # noqa: F811


# ---------------------------------------------------------------- evaluation (as in sweep_fast.py)
def slice_pm(pm, ys, zs):
    return [{l: A[ys] for l, A in pm[0].items()}, {l: A[zs] for l, A in pm[1].items()}, {l: A[zs] for l, A in pm[2].items()}]


def best_path(ops, out, repeats=128, cheap=False, cap=None):
    """flop-optimised RandomGreedy path; if its largest intermediate exceeds the cap (default MEMCAP) the
    size-minimising DP path is tried (networks of <= DPMAX tensors) and kept when smaller (sweep_fast.best_path)."""
    cap = MEMCAP if cap is None else cap
    path, info = find_path(ops, out, None, 'greedy' if cheap else oe.RandomGreedy(max_repeats=repeats))
    big = hwv_fast.largest_intermediate(ops, out, path)
    if big > cap and len(ops) <= DPMAX:
        path2, info2 = find_path(ops, out, None, oe.DynamicProgramming(minimize='size'))
        big2 = hwv_fast.largest_intermediate(ops, out, path2)
        if big2 < big:
            path, info, big = path2, info2, big2
    return path, info, big


class Infeasible(Exception):
    pass


def _ckpt_load(path):
    """(F, yb, zb, next block) from a checkpoint of compute_F's block loop, or None."""
    try:
        meta = json.load(open(path + '.json'))
        F = np.load(path + '.npy')
        return F, meta['yb'], meta['zb'], meta['next']
    except (OSError, ValueError, KeyError):
        return None


def _plain(f):
    """a filling as plain nested lists of ints (JSON, and a repr that does not depend on numpy's int types)."""
    return json.loads(json.dumps(f, default=int))


def _ckpt_save(path, F, yb, zb, nxt, f=None):
    """atomically (rename) write the matrix, the position of the block loop and the filling it belongs to."""
    np.save(path + '.tmp.npy', F)
    json.dump({'yb': yb, 'zb': zb, 'next': nxt, 't': time.time(), 'filling': _plain(f) if f is not None else None},
              open(path + '.tmp.json', 'w'))
    os.replace(path + '.tmp.npy', path + '.npy')
    os.replace(path + '.tmp.json', path + '.json')


def compute_F(f, vm, pm, path=None, info=None, cheap=False, ckpt=None, dest=None):
    """flattening matrix F[Y, Z] (sweep_fast.compute_F: block splitting when an intermediate exceeds MEMCAP, both
    halving orders tried, the full block's checked path reused for edge blocks).  Raises Infeasible if no block
    shape fits 4 * MEMCAP.  ckpt: file prefix; the block loop then saves F and its position every CKPT_EVERY s
    and resumes from such a checkpoint (same block shape; the caller makes the prefix unique for its inputs).
    dest: an (N1, K) array (float32: residues < p < 2^24 are exact) that receives F block by block instead of a
    float64 matrix of its own (2026-10-23: half the memory of the evaluation phase)."""
    N1, K = next(iter(pm[0].values())).shape[0], next(iter(pm[1].values())).shape[0]
    ops, out = build_network(f, vm, pm)
    # the word-minor inputs do not depend on the points: when one of them is already larger than MEMCAP (allowed up
    # to WCAP), splitting the points cannot bring the largest intermediate below it -- it only multiplies the work
    # (a 7x7x7 probe was cut into 128 blocks of 1 x 1 points, 400 s instead of 3 s).  So the cap is at least the
    # largest input.
    cap = max(MEMCAP, max(A.size for _, A in ops))
    if path is None:
        path, info, big = best_path(ops, out, cheap=cheap, cap=cap)
    else:
        big = hwv_fast.largest_intermediate(ops, out, path)
        if big > cap:
            path, info, big = best_path(ops, out, cap=cap)
    if big <= cap:
        if dest is None:
            return execute(ops, out, path)
        dest[...] = execute(ops, out, path)
        return dest
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
            pb, ib, bb = best_path(ops, out, cap=cap)
            if bb <= cap: break
        total = float(ib.opt_cost) * (-(-N1 // yb)) * (-(-K // zb))
        if best is None or total < best[0]:
            best = (total, order, yb, zb, pb, ib, bb)
    total, order, yb, zb, pb, ib, bb = best
    if bb > 4 * cap:
        raise Infeasible('no block path within 4*cap (largest intermediate %.2e, cap %.2e)' % (bb, cap))
    st = _ckpt_load(ckpt) if ckpt else None
    if st is not None and st[0].shape == (N1, K):
        F, yb_s, zb_s, start = st
        if dest is not None:                  # (checkpoints written before 2026-10-23 hold float64)
            dest[...] = F
            F = dest
        if (yb_s, zb_s) != (yb, zb):          # the path search is randomised: resume with the saved block shape
            yb, zb = yb_s, zb_s
            ops, out = build_network(f, vm, slice_pm(pm, slice(0, yb), slice(0, zb)))
            pb, ib, bb = best_path(ops, out, cap=cap)
        print('  . resumed block evaluation at block %d of %d (%s)' % (start, (-(-N1 // yb)) * (-(-K // zb)),
                                                                        os.path.basename(ckpt)), flush=True)
    else:
        F, start = (np.zeros((N1, K), dtype=np.float64) if dest is None else dest), 0
    nbz = -(-K // zb)
    nblocks = (-(-N1 // yb)) * nbz
    last = time.time()
    for idx in range(start, nblocks):         # row-major over (Y blocks, Z blocks), as before
        y0, z0 = (idx // nbz) * yb, (idx % nbz) * zb
        ys, zs = slice(y0, min(N1, y0 + yb)), slice(z0, min(K, z0 + zb))
        ops, out = build_network(f, vm, slice_pm(pm, ys, zs))
        F[ys, zs] = execute(ops, out, pb)
        if ckpt and time.time() - last > CKPT_EVERY and idx + 1 < nblocks:
            _ckpt_save(ckpt, F, yb, zb, idx + 1, f)
            last = time.time()
    if ckpt and os.path.exists(ckpt + '.json'):   # a long evaluation (it was checkpointed): keep the finished matrix
        _ckpt_save(ckpt, F, yb, zb, nblocks, f)    # until the profile is done (a later filling may still be cut)
    return F


class Echelon:
    """incremental linear independence test mod p (small vectors: filling probes)."""
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


# ---------------------------------------------------------------- exact incremental rank (float64 BLAS, mod p)
def _mm(A, B):
    return hwv_fast.fmatmul(np.ascontiguousarray(A)[None], np.ascontiguousarray(B)[None])[0]


def _sub(A, B):
    """(A - B) mod p for arrays of residues in [0, p)."""
    D = A - B
    D[D < 0] += p
    return D


class RREF:
    """reduced row echelon basis of a growing set of vectors of length N over F_p (residues; the basis is stored as
    float32 since 2026-10-23 -- exact below 2^24 > p -- and every product is formed in float64 by fmatmul).
    add(X) adds the rows of X and returns the new rank; cost is dominated by BLAS products.
    The basis is kept in blocks of at most BLK rows that are updated in place, so the memory is the basis itself
    plus one block-sized temporary (the former single array was re-allocated on every growth and every update made
    two full-size temporaries: 4.8 GB peaks for V-stacks with vectors of length 12608)."""
    CH = 128
    BLK = 1024

    def __init__(self, N):
        self.N = N
        self.blocks = []          # [array (BLK x N), rows used, pivot columns (list)]
        self._rank = 0

    @property
    def rank(self):
        return self._rank

    @property
    def B(self):
        return np.vstack([b[0][:b[1]] for b in self.blocks]) if self.blocks else np.zeros((0, self.N))

    @property
    def piv(self):
        return np.array([c for b in self.blocks for c in b[2]], dtype=np.int64)

    def add(self, X):
        for s in range(0, X.shape[0], self.CH):
            if self._rank == self.N:
                break
            Y = np.array(X[s:s + self.CH], dtype=np.float64)
            for Bb, m, pv in self.blocks:            # RREF: reducing block by block = reducing by the whole basis
                Y = _sub(Y, _mm(Y[:, pv], Bb[:m]))
            R, newpiv = self._gauss_jordan(Y)
            if not len(newpiv):
                continue
            for blk in self.blocks:                  # eliminate the new pivot columns from the old rows, in place
                Bb, m = blk[0], blk[1]
                U = _mm(Bb[:m][:, newpiv], R)
                Bb[:m] -= U
                np.add(Bb[:m], p, out=Bb[:m], where=Bb[:m] < 0)
                del U
            for row, c in zip(R, newpiv):            # append the new rows
                if not self.blocks or self.blocks[-1][1] == self.blocks[-1][0].shape[0]:
                    self.blocks.append([np.empty((min(self.BLK, self.N), self.N), dtype=np.float32), 0, []])
                blk = self.blocks[-1]
                blk[0][blk[1]] = row; blk[1] += 1; blk[2].append(int(c))
            self._rank += len(newpiv)
        return self._rank

    @staticmethod
    def _gauss_jordan(Y):
        R = np.zeros((0, Y.shape[1])); piv = []
        for i in range(Y.shape[0]):
            y = Y[i]
            nz = np.flatnonzero(y)
            if nz.size == 0:
                continue
            c = nz[0]
            y = np.fmod(y * float(pow(int(y[c]), p - 2, p)), p)
            if i + 1 < Y.shape[0]:
                f = Y[i + 1:, c].copy()
                if f.any():
                    Y[i + 1:] = _sub(Y[i + 1:], np.fmod(np.outer(f, y), p))
            if R.shape[0]:
                f = R[:, c].copy()
                if f.any():
                    R = _sub(R, np.fmod(np.outer(f, y), p))
            R = np.vstack([R, y[None]]); piv.append(c)
        return R, np.array(piv, dtype=np.int64)


def prefix_ranks(blocks, N, cap, g):
    """ranks of the row-stacks blocks[0..k-1] for k = 1..g (blocks: callable k -> array with rows of length N);
    stops early once the rank reaches `cap` (the rank bound for all k)."""
    E = RREF(N); out = []
    for k in range(g):
        if E.rank >= cap:
            out.append(E.rank); continue
        out.append(E.add(blocks(k)))
    return out


# ---------------------------------------------------------------- one component, one direction
def peak_rss_mb():
    try:
        for l in open('/proc/self/status'):
            if l.startswith('VmHWM'):
                return int(l.split()[1]) / 1024.0
    except OSError:
        pass
    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024.0


def reset_peak_rss():
    try:
        with open('/proc/self/clear_refs', 'w') as fh:
            fh.write('5')
    except OSError:
        pass


def word_minor_size(lam_p, n, r):
    return max(comb(n, L) * r ** L for l in lam_p for L in col_lengths(l))


class Direction:
    def __init__(self, n, lam, g, t, crng, vecs, rmax_feasible):
        self.n, self.g, self.t = n, g, t
        perm = [t] + [u for u in range(3) if u != t]
        self.perm = perm
        self.lam_p = tuple(lam[u] for u in perm)
        self.n1 = dim_schur(self.lam_p[0], n)
        self.n23 = dim_schur(self.lam_p[1], n) * dim_schur(self.lam_p[2], n)
        self.N1 = min(self.n1, g * self.n23) + EXTRA
        self.K = min(g * self.n1, self.n23) + EXTRA if VSTACK else min(self.n1, self.n23) + EXTRA
        self.vecs = vecs
        self.crng = crng
        gs = random_gs(crng, n, self.N1, self.K)
        self.gs = gs
        self.pm = [{L: minors_of_points(gs[u], L) for L in col_lengths(self.lam_p[u])} for u in range(3)]
        self.rprobe = rmax_feasible
        self.choose_fillings()
        self.C = crng.integers(0, p, (self.span, self.span)).astype(np.float64)
        self.ubH = [min(self.n1, k * self.n23) for k in range(1, self.span + 1)]
        self.ubV = [min(k * self.n1, self.n23) for k in range(1, self.span + 1)]
        self.times = {}
        self.cuts = {}                # r -> cut of a profile evaluated on the leading cut x cut block only
        self.prof_files = []          # cached profile results to delete once the component is written

    def vm(self, r):
        V = tuple(self.vecs[r][u] for u in self.perm)
        return [{L: minors_of_vectors(V[u], L) for L in col_lengths(self.lam_p[u])} for u in range(3)]

    def choose_fillings(self):
        g = self.g
        PR2 = max(16, -(-(2 * g + 16) // PR1))
        gp = random_gs(self.crng, self.n, PR1, PR2)
        pmp = [{L: minors_of_points(gp[u], L) for L in col_lengths(self.lam_p[u])} for u in range(3)]
        vmr = self.vm(self.rprobe)
        ech, chosen, tried = Echelon(), [], 0
        maxtry = 60 * g + 100
        while len(chosen) < g and tried < maxtry:
            batch = []
            while len(batch) < 2 * (g - len(chosen)) + 4 and tried < maxtry:
                f = random_fillings(self.crng, self.lam_p); tried += 1
                v = compute_F(f, vmr, pmp, cheap=True).ravel()
                if v.any():
                    batch.append((f, v))
            scored = []
            for f, v in batch:
                ops, out = build_network(f, vmr, self.pm)
                path, info = find_path(ops, out, None, oe.RandomGreedy(max_repeats=32))
                scored.append((float(info.opt_cost), len(scored), f, v, path, info))
            scored.sort(key=lambda x: x[:2])
            for c, _, f, v, path, info in scored:
                if len(chosen) < g and ech.add(v.astype(np.int64)):
                    chosen.append([f, path, info])
        self.fillings = chosen
        self.span = len(chosen)
        self.tried = tried

    def profile(self, r, cut=None):
        """{'H': [rank H_k], 'V': [rank V_k]} at the random rank-r tensor.  cut (g = 1): evaluate only the leading
        cut x cut block of F (the first cut random points on each side); its rank is min(cut, rank F) with the same
        probability argument as the EXTRA margin, so with cut = rank at r - 1 + EXTRA it decides whether the rank
        exceeds that one (resolve(): adjacent end points), at (cut / N1)^2 of the cost."""
        pc = self.prof_cache_name(r, cut) if CKPT else None
        if pc and os.path.exists(pc):
            try:
                rec = json.load(open(pc))
                self.times[r] = tuple(rec['times'])
                if cut:
                    self.cuts[r] = cut
                self.prof_files.append(pc)
                print('  . %s dir %d r=%d H=%s V=%s (finished earlier, %s)' % (self.lam_p, self.t, r, rec['H'], rec['V'],
                                                                                os.path.basename(pc)), flush=True)
                return {'H': rec['H'], 'V': rec['V']}
            except (OSError, ValueError, KeyError):
                pass
        t0 = time.time()
        vm = self.vm(r)
        g, N1, K = self.span, self.N1, self.K
        pm = self.pm
        if cut:
            assert g == 1 and cut < min(N1, K)
            N1 = K = cut
            pm = slice_pm(self.pm, slice(0, cut), slice(0, cut))
            self.cuts[r] = cut
        Fs = np.empty((g, N1, K), dtype=np.float32)       # residues < p < 2^24: exact (float64 up to 2026-10-23)
        if CKPT and g == 1:
            self.adopt_ckpt_filling(r)
        cks = [self.ckpt_name(r, i) + ('_c%d' % cut if cut else '') for i in range(g)] if CKPT else [None] * g
        for i, fl in enumerate(self.fillings):
            compute_F(fl[0], vm, pm, fl[1], fl[2], ckpt=cks[i], dest=Fs[i])
        del vm                                 # the word minors are not needed for the elimination
        t1 = time.time()
        cache = {}

        def phi(j):
            """sum_i C[j, i] F_i mod p, accumulated exactly in float64 on row chunks, stored as float32."""
            if j not in cache:
                cache.clear()
                A = np.empty((N1, K), dtype=np.float32)
                rs = max(1, (1 << 22) // K)
                for s0 in range(0, N1, rs):
                    T = np.zeros((min(rs, N1 - s0), K))
                    for i in range(g):
                        T += self.C[j, i] * Fs[i, s0:s0 + rs].astype(np.float64)
                    A[s0:s0 + rs] = np.fmod(T, p, out=T)
                cache[j] = A
            return cache[j]
        # H_k: vectors = columns of phi_j (length N1); V_k: vectors = rows of phi_j (length K)
        if VSTACK:
            EH, EV = RREF(N1), RREF(K)
            H, V = [], []
            for k in range(g):
                P = None
                if EH.rank < self.n1:
                    P = phi(k); EH.add(P.T)
                H.append(EH.rank)
                if EV.rank < self.n23:
                    P = phi(k) if P is None else P; EV.add(P)
                V.append(EV.rank)
        else:
            H = prefix_ranks(lambda k: phi(k).T, N1, self.n1, g); V = H[:1]
        self.times[r] = (round(t1 - t0, 2), round(time.time() - t1, 2))
        del Fs
        if pc:                                # keep the result until the component is written (a restarted worker
            tmp = pc + '.tmp'                 # would otherwise evaluate this rank again: 28 h for the 8x8x8 hook)
            json.dump({'H': H, 'V': V, 'times': self.times[r], 'cut': cut, 't': time.time()}, open(tmp, 'w'))
            os.replace(tmp, pc)
            self.prof_files.append(pc)
        stale = [self.ckpt_name(r, i) for i in range(g)] if CKPT and cut else []   # a full-size block loop of this
        for c in cks + stale:                 # rank cut short; the profile is done: its checkpoints are no longer needed
            for ext in ('.npy', '.json'):
                if c and os.path.exists(c + ext):
                    os.remove(c + ext)
        # progress line (one per evaluated rank: shows where a long component spends its time)
        print('  . %s dir %d r=%d H=%s V=%s eval %.0fs rref %.0fs%s' % (self.lam_p, self.t, r, H, V, t1 - t0, time.time() - t1,
              ' (leading %dx%d block of %dx%d: rank capped at %d)' % (cut, cut, self.N1, self.K, cut) if cut else ''),
              flush=True)
        return {'H': H, 'V': V}

    def prof_cache_name(self, r, cut=None):
        """file of a finished profile(r) (kept until the component's record is written).  g > 1: the ranks of the
        stacked flattenings depend on the chosen fillings, so their hash is part of the name."""
        import hashlib
        fh = '' if self.span == 1 else '_' + hashlib.sha1(json.dumps(_plain([f[0] for f in self.fillings])).encode()).hexdigest()[:8]
        return self.ckpt_base(r, 0) + '_prof' + fh + ('_c%d' % cut if cut else '') + '.json'

    def ckpt_base(self, r, i):
        """checkpoint prefix of filling slot i at rank r without the filling: a hash of the evaluation points, the
        rank-r tensor, the prime and the sizes."""
        import hashlib
        h = hashlib.sha1()
        h.update(repr((self.n, self.lam_p, self.t, r, i, self.N1, self.K, p)).encode())
        for a in self.gs:
            h.update(np.ascontiguousarray(a).tobytes())
        for a in self.vecs[r]:
            h.update(np.ascontiguousarray(a).tobytes())
        os.makedirs(CKPT, exist_ok=True)
        return os.path.join(CKPT, 'n%d_t%d_r%d_f%d_%s' % (self.n, self.t, r, i, h.hexdigest()[:16]))

    def ckpt_name(self, r, i):
        """checkpoint prefix: ckpt_base + a hash of the filling, so a checkpoint is only ever resumed by the
        identical computation."""
        import hashlib
        fh = hashlib.sha1(json.dumps(_plain(self.fillings[i][0])).encode()).hexdigest()[:8]
        return self.ckpt_base(r, i) + '_' + fh

    def adopt_ckpt_filling(self, r):
        """g = 1: every filling with a nonzero highest weight vector gives the same flattening up to a nonzero
        scalar, so the rank does not depend on which one is used.  The choice among candidates goes through a
        path-cost ranking whose ties depend on the process (string hashing), so a restarted worker may pick another
        filling than the one a checkpoint was written with (2026-10-20: the 8x8x8 hook rerun lost 13 h that way).
        If a checkpoint of this slot exists with another filling, use that filling (the furthest one)."""
        import glob
        best = None
        for jf in glob.glob(self.ckpt_base(r, 0) + '_*.json'):
            try:
                meta = json.load(open(jf))
            except (OSError, ValueError):
                continue
            if meta.get('filling') is not None and (best is None or meta.get('next', 0) > best[0]):
                best = (meta.get('next', 0), meta['filling'])
        if best is not None and _plain(self.fillings[0][0]) != best[1]:
            self.fillings[0] = [best[1], None, None]     # path searched again by compute_F
            print('  . adopted the filling of an existing checkpoint (block %d)' % best[0], flush=True)

    def saturated(self, P):
        return all(h >= u for h, u in zip(P['H'], self.ubH)) and (not VSTACK or all(v >= u for v, u in zip(P['V'], self.ubV)))


class OnerowDirection:
    """fast path for the components ((d), mu, mu) (g = 1): the flattening entries are products of leading minors of
    g'^T T(alpha) g'' (onerow_family.py, validated against this file's evaluator on 122 values); same interface as
    Direction (profile, saturated), direction t = 0 (source S^d) or t = 1 (source S^mu), same random tensors."""
    def __init__(self, n, lam, t, crng, vecs):
        from onerow_family import flat_rank
        self.flat_rank = flat_rank
        self.n, self.t, self.crng, self.vecs = n, t, crng, vecs
        self.mu = tuple(lam[1]); d = sum(self.mu)
        nd, nm = comb(n + d - 1, d), dim_schur(self.mu, n)
        self.n1, self.n23 = (nd, nm * nm) if t == 0 else (nm, nd * nm)
        self.N1 = self.K = min(self.n1, self.n23) + EXTRA
        self.span, self.tried = 1, 0
        self.ubH = self.ubV = [min(self.n1, self.n23)]
        self.lam_p = (lam[t],) + tuple(lam[u] for u in range(3) if u != t)
        self.times = {}

    def profile(self, r):
        t0 = time.time()
        A, B, C = self.vecs[r]
        rk, _ = self.flat_rank(self.n, self.mu, A, B, C, 1 if self.t == 0 else 2, self.crng)
        self.times[r] = (round(time.time() - t0, 2), 0.0)
        return {'H': [rk], 'V': [rk]}

    def saturated(self, P):
        return P['H'][0] >= self.ubH[0]


class ColwedgeDirection:
    """fast path for the components (lam, lam^T, (1^d)) (g = 1): every flattening entry is one d x d determinant
    (Cauchy-Binet over the d-subsets of the rank-one terms, colwedge_family.py; validated against this file's network
    evaluator on identical tensors, scan/colwedge_check.log).  No word-minor tensor, so no WCAP limit.  Same interface
    as Direction; t indexes lam as given."""
    def __init__(self, n, lam, t, crng, vecs):
        from colwedge_family import flat_rank
        self.flat_rank = flat_rank
        self.n, self.t, self.crng, self.vecs, self.lam = n, t, crng, vecs, lam
        dims = [dim_schur(tuple(l), n) for l in lam]
        self.n1 = dims[t]
        self.n23 = dims[0] * dims[1] * dims[2] // dims[t]
        self.N1 = self.K = min(self.n1, self.n23) + EXTRA
        self.span, self.tried = 1, 0
        self.ubH = self.ubV = [min(self.n1, self.n23)]
        self.lam_p = (lam[t],) + tuple(lam[u] for u in range(3) if u != t)
        self.times = {}

    def profile(self, r):
        t0 = time.time()
        rk, _ = self.flat_rank(self.n, self.lam, list(self.vecs[r]), self.t, self.crng)
        self.times[r] = (round(time.time() - t0, 2), 0.0)
        print('  . %s dir %d r=%d H=[%d] colwedge %.0fs' % (self.lam_p, self.t, r, rk, time.time() - t0), flush=True)
        return {'H': [rk], 'V': [rk]}

    def saturated(self, P):
        return P['H'][0] >= self.ubH[0]


def colwedge_ok(lam):
    from colwedge_family import is_colwedge
    return is_colwedge(lam)


def is_onerow(lam):
    return len(lam[0]) == 1 and tuple(lam[1]) == tuple(lam[2])


def resolve(D, need, rlo, rmax_feasible):
    """evaluate D.profile at few ranks; returns (profiles {r: P}, sep {r: [config strings]}, unknown [r],
    saturated_from r or None)."""
    prof = {}

    def get(r, cut=None):
        if r not in prof:
            prof[r] = D.profile(r, cut) if cut else D.profile(r)
        return prof[r]
    need = sorted(x for x in need if x >= rlo)
    if not need:
        return prof, {}, [], None
    top = max(need) + 1                       # largest rank needed
    hi = min(top, rmax_feasible)
    sat_from = None
    pts = [rlo]
    get(rlo)
    if D.saturated(prof[rlo]):
        sat_from = rlo
    elif hi > rlo and word_minor_size(D.lam_p, D.n, hi) <= ENDS * word_minor_size(D.lam_p, D.n, rlo):
        # the top rank costs about as much as the lowest: evaluate both ends first (equal ends settle the whole
        # interval with 2 evaluations; a doubling search needed 4 for 6x6x6, ranks 10..14), bisect if they differ.
        # Adjacent ends (hi = rlo + 1, g = 1): only "rank at hi > rank at rlo?" is asked, which the leading
        # (rank at rlo + EXTRA)-square block of F answers (2026-10-21: the 8x8x8 hook rerun, 6216^2 of 10304^2)
        cut = None
        if CUT and hi == rlo + 1 and isinstance(D, Direction) and D.span == 1:
            c = max(prof[rlo]['H'] + prof[rlo]['V']) + EXTRA
            cut = c if c < min(D.N1, D.K) else None
        get(hi, cut); pts.append(hi)
    else:
        # the top rank is much more expensive (large n): doubling steps from rlo, stop at saturation
        step, a = 1, rlo
        while a < hi:
            b = min(a + step, hi)
            get(b); pts.append(b)
            if D.saturated(prof[b]):
                sat_from = b; break
            a, step = b, step * 2
    # bisect between consecutive evaluated points
    stack = list(zip(pts[:-1], pts[1:]))
    while stack:
        a, b = stack.pop()
        if b - a < 2 or prof[a] == prof[b] or not any(a <= x < b for x in need):
            continue
        m = (a + b) // 2
        get(m)
        stack += [(a, m), (m, b)]
    # read off the jumps
    ev = sorted(prof)
    sep, unknown = {}, []
    for x in need:
        if sat_from is not None and x >= sat_from:
            continue
        lo_pts = [y for y in ev if y <= x]
        hi_pts = [y for y in ev if y >= x + 1]
        if not lo_pts or not hi_pts:
            unknown.append(x); continue
        a, b = max(lo_pts), min(hi_pts)
        Pa, Pb = prof[a], prof[b]
        if b == x + 1 and a == x:
            cfg = ['H%d' % (k + 1) for k in range(len(Pa['H'])) if Pa['H'][k] < Pb['H'][k]]
            cfg += ['V%d' % (k + 1) for k in range(1, len(Pa['V'])) if Pa['V'][k] < Pb['V'][k]]
            if cfg:
                sep[x] = cfg
        elif Pa != Pb:
            unknown.append(x)        # should not happen (bisection resolves every needed pair)
    return prof, sep, unknown, sat_from


# ---------------------------------------------------------------- main
def components(n, d):
    out = []
    for li, lam in enumerate(itertools.combinations_with_replacement(partitions(d, n), 3)):
        g = kronecker(*lam)
        if g:
            out.append((li, lam, g))
    return out


def cost_proxy(n, lam, g):
    dims = [dim_schur(l, n) for l in lam]
    tot = 0
    for t in distinct_dirs(lam):
        n1 = dims[t]; n23 = dims[(t + 1) % 3] * dims[(t + 2) % 3]
        tot += (min(n1, g * n23) + EXTRA) * ((min(g * n1, n23) if VSTACK else min(n1, n23)) + EXTRA)
    return g * tot


def distinct_dirs(lam):
    out = []
    for t in range(3):
        if all(lam[u] != lam[t] for u in out):
            out.append(t)
    return out


def main():
    n, d = int(sys.argv[1]), int(sys.argv[2])
    rgen = generic_rank(n)
    SEED = int(os.environ.get('SEED', '5'))
    WORKER, NWORKERS = int(os.environ.get('WORKER', '0')), int(os.environ.get('NWORKERS', '1'))
    need = [int(x) for x in os.environ['NEED'].split(',')] if os.environ.get('NEED') else list(range(1, rgen))
    rlo = int(os.environ.get('RLO', str(min(need))))
    os.makedirs('scan', exist_ok=True)
    OUT = os.environ.get('OUT', 'scan/n%d_d%d.jsonl' % (n, d))
    CLAIMDIR = os.environ.get('CLAIMDIR', 'scan/claims_n%d_d%d' % (n, d))
    os.makedirs(CLAIMDIR, exist_ok=True)
    rng = np.random.default_rng([SEED, n])
    vecs = {r: tuple(np.random.default_rng([SEED, n, r, t]).integers(0, p, (r, n)) for t in range(3)) for r in range(1, rgen + 1)}
    done = set()
    for lf in os.environ.get('RESUME', '').split(':'):
        if lf and os.path.exists(lf):
            for l in open(lf):
                try:
                    done.add(tuple(tuple(x) for x in json.loads(l)['lam']))
                except Exception:
                    pass
    allc = {lam: (li, g) for li, lam, g in components(n, d)}
    if os.environ.get('LIST'):
        order = [tuple(tuple(x) for x in eval(l)) for l in open(os.environ['LIST']) if l.strip()]
    else:
        order = sorted(allc, key=lambda lam: cost_proxy(n, lam, allc[lam][1]))
    print('# rankscan n=%d d=%d r_gen=%d need=%s rlo=%d seed=%d worker %d/%d VSTACK=%s MEMCAP=%d WCAP=%d: %d components in list'
          % (n, d, rgen, need, rlo, SEED, WORKER, NWORKERS, VSTACK, MEMCAP, WCAP, len(order)), flush=True)
    T0 = time.time()
    MAXCOMP = int(os.environ.get('MAXCOMP', '0'))      # > 0: exit after that many components (the runner sets 1, so
    ncomp_done = 0                                      # that it can re-apply its job priorities after every component)
    for lam in order:
        li, g = allc[lam]
        if lam in done:
            continue
        if MAXCOMP and ncomp_done >= MAXCOMP:
            break
        try:
            fd = os.open(os.path.join(CLAIMDIR, str(li)), os.O_CREAT | os.O_EXCL | os.O_WRONLY)
            os.write(fd, ('%d %d\n' % (WORKER, os.getpid())).encode()); os.close(fd)
        except FileExistsError:
            continue
        ncomp_done += 1
        reset_peak_rss()
        t0, c0 = time.time(), time.process_time()
        crng = np.random.default_rng([SEED, n, d, li])
        dims = [dim_schur(l, n) for l in lam]
        rec = {'n': n, 'd': d, 'lam': lam, 'g': g, 'dims': dims, 'need': need, 'rlo': rlo, 'seed': SEED,
               'cost': cost_proxy(n, lam, g), 'dirs': [], 'sep': {}, 'unknown': [], 'worker': WORKER}
        status = 'ok'
        pfiles = []                     # cached profiles (Direction.prof_files) of this component
        for t in distinct_dirs(lam):
            perm_lam = tuple(lam[u] for u in [t] + [u for u in range(3) if u != t])
            onerow = ONEROW and is_onerow(lam)
            colw = not onerow and COLWEDGE and colwedge_ok(lam)
            rmax = rgen if (onerow or colw) else max([r for r in range(1, rgen + 1) if word_minor_size(perm_lam, n, r) <= WCAP] or [0])
            if rmax < max(rlo, 1):
                # the needed ranks are beyond the word-minor limit; probe the highest feasible rank rmax instead: if
                # the flattening is already at its bounds there, it stays there for every r >= rmax (rank is monotone
                # in r), so this direction separates none of the needed ranks (env SATPROBE=0 disables)
                if SATPROBE and rmax >= max(2, rlo - SATPROBE_GAP):
                    try:
                        D = Direction(n, lam, g, t, crng, vecs, rmax)
                        P = D.profile(rmax)
                        pfiles += D.prof_files
                        if D.saturated(P):
                            rec['dirs'].append({'t': t, 'method': 'network', 'n1': D.n1, 'n23': D.n23, 'N1': D.N1, 'K': D.K,
                                                'span': D.span, 'tried': D.tried, 'rmax': rmax, 'sat_from': rmax,
                                                'probe': True, 'prof': {str(rmax): P},
                                                'times': {str(r): v for r, v in sorted(D.times.items())}})
                            continue
                        rec['dirs'].append({'t': t, 'status': 'infeasible', 'rmax': rmax, 'probe_prof': {str(rmax): P}})
                        rec['unknown'] = sorted(set(rec['unknown']) | set(need)); status = 'partial'
                        continue
                    except Exception:            # any trouble in the probe: fall back to 'infeasible' (unknown)
                        pass
                rec['dirs'].append({'t': t, 'status': 'infeasible', 'rmax': rmax})
                rec['unknown'] = sorted(set(rec['unknown']) | set(need)); status = 'partial'
                continue
            try:
                D = OnerowDirection(n, lam, t, crng, vecs) if onerow else \
                    ColwedgeDirection(n, lam, t, crng, vecs) if colw else Direction(n, lam, g, t, crng, vecs, min(rmax, rgen))
                prof, sep, unknown, sat = resolve(D, need, rlo, min(rmax, rgen))
                pfiles += getattr(D, 'prof_files', [])
            except (Infeasible, MemoryError) as e:
                rec['dirs'].append({'t': t, 'status': 'infeasible', 'why': str(e)[:200]})
                rec['unknown'] = sorted(set(rec['unknown']) | set(need)); status = 'partial'
                continue
            rec['dirs'].append({'t': t, 'method': 'onerow' if onerow else 'colwedge' if colw else 'network', 'n1': D.n1, 'n23': D.n23, 'N1': D.N1, 'K': D.K, 'span': D.span,
                                'tried': D.tried, 'rmax': rmax, 'sat_from': sat,
                                'prof': {str(r): P for r, P in sorted(prof.items())},
                                'times': {str(r): v for r, v in sorted(D.times.items())}})
            if getattr(D, 'cuts', None):       # ranks evaluated on a leading block only: min(cut, rank) there
                rec['dirs'][-1]['cut'] = {str(r): c for r, c in sorted(D.cuts.items())}
            for x, cfg in sep.items():
                rec['sep'].setdefault(str(x), []).extend('%d%s' % (t + 1, c) for c in cfg)
            rec['unknown'] = sorted(set(rec['unknown']) | set(unknown))
            if unknown:
                status = 'partial'
        rec['status'] = status
        rec['wall'] = round(time.time() - t0, 2)
        rec['cpu'] = round(time.process_time() - c0, 2)
        rec['rss_peak_mb'] = round(peak_rss_mb(), 1)
        rec['ts'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
        with open(OUT, 'a') as fh:
            fh.write(json.dumps(rec) + '\n')
        for pf in pfiles:
            if os.path.exists(pf):
                os.remove(pf)
        sepstr = ' '.join('r%s:%s' % (x, ','.join(c)) for x, c in sorted(rec['sep'].items(), key=lambda kv: int(kv[0])))
        prof_str = ' | '.join('d%d %s' % (D_['t'] + 1, ' '.join('r%s:%s/%s' % (r, P['H'], P['V'][1:] if len(P['V']) > 1 else '')
                                                               for r, P in D_.get('prof', {}).items()))
                              for D_ in rec['dirs'])
        print('lam=%s g=%d dims=%s %s  wall=%.1fs rss=%.0fMB%s%s' % (lam, g, dims, status, rec['wall'], rec['rss_peak_mb'],
              ('  *** SEPARATES ' + sepstr) if sepstr else '', ('  unknown=%s' % rec['unknown']) if rec['unknown'] else ''), flush=True)
        if os.environ.get('VERBOSE'):
            print('   ', prof_str, flush=True)
    print('# worker %d done, %.0fs' % (WORKER, time.time() - T0), flush=True)


if __name__ == '__main__':
    main()
