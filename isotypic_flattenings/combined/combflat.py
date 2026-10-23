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
blocks.  Each block's subspace is stored once as a thin matrix (about dim + 8 rows, on the first sum-of-dims + 8
generic coordinates; see LatticeFamily), so the rank of any sub-sum costs one small rank computation:
LatticeFamily.dims(S).

Memory (2026-10-23).  A flattening evaluation keeps at most about EVALMEM float64 elements alive (blocks of sample
points, block-independent part computed once; eval_F), flattenings go straight into uint32 and, when a disk cache is
used, leave memory once their lattice block is stored (Context.release).

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
from hwv_fast import build_network, find_path, minors_of_points, minors_of_vectors, fmatmul, _fmod, single_reduce
from isoflat import partitions, kronecker, modrank

MEMCAP = int(os.environ.get('MEMCAP', str(1 << 25)))   # max elements of a contraction intermediate (else block splitting)
DPMAX = int(os.environ.get('DPMAX', '40'))              # max tensors for the DynamicProgramming (optimal) path; 2*(lam_1+mu_1+nu_1) operands
EXTRA = 8                                               # extra sample points / compression columns
PR1, PR2 = 8, 16                                        # probe size for the choice of independent fillings
FILLPOOL = int(os.environ.get('FILLPOOL', '1500'))      # random fillings scored per component before choosing the cheapest
FILLCHEAP = float(os.environ.get('FILLCHEAP', '1e8'))   # stop enlarging the pool once a filling this cheap (flops) is found
EVALMEM = int(float(os.environ.get('EVALMEM', str(1 << 23))))  # max float64 elements (64 MB) alive in one flattening evaluation (simulated), else blocks
STEPCOST = float(os.environ.get('STEPCOST', '2e5'))     # cost (flops) charged per block-dependent pairwise contraction and block
CHUNK = 1 << 23                                         # elements (float64) of a row chunk when lattice blocks are built

# ----------------------------------------------------------------------------------------------------------------
# exact modular helpers

def mulmod(A, B):
    """exact A @ B mod p for integer arrays with entries in [0, p) (float64 BLAS, chunked by hwv_fast.fmatmul)."""
    A = np.asarray(A); B = np.asarray(B)
    return fmatmul((A % p).astype(np.float64)[None], (B % p).astype(np.float64)[None])[0].astype(np.int64)

def _residues(M):
    """float64 residues of M: a float64 array is taken as already reduced (no copy), integer arrays are reduced."""
    M = np.asarray(M)
    return M if M.dtype == np.float64 else (M.astype(np.int64) % p).astype(np.float64)

def fmm(A, B):
    """exact 2-d A @ B mod p on float64 arrays of residues (hwv_fast.fmatmul)."""
    return fmatmul(A[None], B[None])[0]

def fcombine(Psi, Fs, rows=slice(None), cols=slice(None)):
    """sum_m Psi[m] * Fs[m][rows, cols] mod p as float64 residues (Psi (g,) ints, Fs (g, N, K) residues, e.g. uint32).
    Every product is < p^2 < 2^38 and at most g < 2^15 of them are added before the reduction, so float64 is exact.
    2026-10-23: replaces the int64 loop of combine(), which held four full-size int64 temporaries per term."""
    out = tmp = None
    for c, F in zip(Psi, Fs):
        c = float(int(c) % p)
        if out is None:
            out = np.multiply(F[rows, cols], c, dtype=np.float64)
        else:
            if tmp is None:
                tmp = np.empty_like(out)
            np.multiply(F[rows, cols], c, out=tmp, dtype=np.float64)
            out += tmp
    return np.fmod(out, p, out=out)

def combine(Psi, Fs):
    """sum_m Psi[m] * Fs[m] mod p; Psi (g,) ints, Fs (g, N, K); int64 (see fcombine)."""
    return fcombine(Psi, Fs).astype(np.int64)

def rref(M):
    """reduced row echelon form of M mod p: (R, pivots).  2026-10-23: blocked Gauss-Jordan (rref_fast, BLAS panel
    updates), 10-20x faster than the unblocked rref_ref on 1000 x 1200 and larger, output identical (the RREF is unique;
    checked entrywise on random, rank-deficient, structured and sparse matrices).  RREF_OLD=1 restores rref_ref."""
    return rref_ref(M) if RREF_OLD else rref_fast(M)

RREF_OLD = os.environ.get('RREF_OLD', '0') == '1'

def rref_ref(M):
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

RREF_BLOCK = int(os.environ.get('RREF_BLOCK', '64'))
def _mm(A, B):
    """exact (A @ B) mod p for float64 arrays with entries in [0, p) and inner dimension <= RREF_BLOCK."""
    return np.mod(A @ B, p)

def rref_fast(M, block=RREF_BLOCK):
    """reduced row echelon form of M mod p: (R, pivots), R the nonzero rows as float64 residues.  Same output as the
    unblocked rref (the RREF is unique).  Blocked Gauss-Jordan: each panel of `block` columns is eliminated unblocked on
    the panel only (pivot rows below the current rank, leftmost pivots first), then the whole trailing matrix gets the
    panel's row operations at once: pivot rows W = Bk^-1 A[piv rows], every other row A_i -= A_i[piv cols] W (one
    BLAS matmul, inner dimension k <= block, so float64 sums of products < p^2 stay exact)."""
    A = (np.asarray(M) % p).astype(np.float64)
    n, m = A.shape
    piv, r = [], 0
    for c0 in range(0, m, block):
        if r == n:
            break
        c1 = min(m, c0 + block)
        P = A[r:, c0:c1].copy()                 # panel rows r.. (rows < r are pivot rows of earlier panels)
        prow, pcol, k = [], [], 0               # pivot rows (indices into P after swaps), panel columns
        perm = np.arange(n - r)
        for j in range(c1 - c0):
            if k == P.shape[0]:
                break
            nz = np.flatnonzero(P[k:, j])
            if nz.size == 0:
                continue
            i = k + nz[0]
            if i != k:
                P[[k, i]] = P[[i, k]]; perm[[k, i]] = perm[[i, k]]
            P[k] = np.mod(P[k] * float(pow(int(P[k, j]), p - 2, p)), p)
            col = P[:, j].copy(); col[k] = 0
            nzr = np.flatnonzero(col)
            if nzr.size:
                P[nzr] = np.mod(P[nzr] - np.outer(col[nzr], P[k]), p)
            pcol.append(c0 + j); k += 1
        if k == 0:
            continue
        # apply the row permutation of the panel to rows r.. of A
        A[r:] = A[r:][perm]
        cols = np.array(pcol)
        # Bk = original pivot block (rows r..r+k-1, pivot columns); W = Bk^-1 A[r:r+k, c0:]
        Bk = A[r:r + k][:, cols]
        Binv = _inv_small(Bk)
        T = A[r:r + k, c0:]
        W = np.zeros_like(T)
        for s in range(0, k, block):
            W = np.mod(W + _mm(Binv[:, s:s + block], T[s:s + block]), p)
        others = np.r_[0:r, r + k:n]
        step = max(1, (1 << 22) // max(1, m - c0))     # row chunks: temporaries of <= 2^22 entries
        for i0 in range(0, others.size, step):
            idx = others[i0:i0 + step]
            X = A[idx][:, cols]                 # multipliers
            if not X.any():
                continue
            U = A[idx, c0:]
            for s in range(0, k, block):
                U = np.mod(U - _mm(X[:, s:s + block], W[s:s + block]), p)
            A[idx, c0:] = U
        A[r:r + k, c0:] = W
        piv += pcol; r += k
    return A[:r], piv

def _inv_small(B):
    """inverse of a k x k invertible matrix mod p (unblocked Gauss-Jordan on [B | I]; k <= block)."""
    k = B.shape[0]
    A = np.hstack([np.mod(B, p), np.eye(k)])
    for c in range(k):
        i = c + np.flatnonzero(A[c:, c])[0]
        if i != c:
            A[[c, i]] = A[[i, c]]
        A[c] = np.mod(A[c] * float(pow(int(A[c, c]), p - 2, p)), p)
        col = A[:, c].copy(); col[c] = 0
        nzr = np.flatnonzero(col)
        if nzr.size:
            A[nzr] = np.mod(A[nzr] - np.outer(col[nzr], A[c]), p)
    return A[:, k:]

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

def _contract(pair, keep):
    """hwv_fast.pair_contract for pair = [(ia, A), (ib, B)], which is emptied first: the operands are released as soon as
    their transposed copies exist and the copies as soon as the product exists (2026-10-23: before, both operands, both
    copies and the product were alive together, and the last operand of a step stayed referenced into the next step)."""
    (ia, A), (ib, B) = pair
    pair.clear()
    for idx in list(ia):
        if idx not in ib and idx not in keep:
            A = _fmod(A.sum(axis=ia.index(idx))); ia = ia.replace(idx, '')
    for idx in list(ib):
        if idx not in ia and idx not in keep:
            B = _fmod(B.sum(axis=ib.index(idx))); ib = ib.replace(idx, '')
    batch = [i for i in ia if i in ib and i in keep]
    contr = [i for i in ia if i in ib and i not in keep]
    fa = [i for i in ia if i not in ib]; fb = [i for i in ib if i not in ia]
    dims = dict(zip(ia, A.shape)); dims.update(zip(ib, B.shape))
    size = lambda idx: int(np.prod([dims[i] for i in idx])) if idx else 1
    nb, na, nc, nbb = size(batch), size(fa), size(contr), size(fb)
    A = np.ascontiguousarray(np.transpose(A, [ia.index(i) for i in batch + fa + contr])).reshape(nb, na, nc)
    B = np.ascontiguousarray(np.transpose(B, [ib.index(i) for i in batch + contr + fb])).reshape(nb, nc, nbb)
    R = fmatmul(A, B)
    del A, B
    res_idx = ''.join(batch + fa + fb)
    R = R.reshape([dims[i] for i in res_idx])
    return np.transpose(R, [res_idx.index(i) for i in keep])

def _step_out(idxs, rest):
    """index string of the result of one path step on operands with index strings idxs, as execute() forms it."""
    t = list(idxs)
    while len(t) > 1:
        others = rest | set(''.join(t[:-2]))
        ia, ib = t.pop(), t.pop()
        t.append(''.join(dict.fromkeys(i for i in ia + ib if i in others)))
    return ''.join(dict.fromkeys(i for i in t[0] if i in rest))

def execute(ops, out, path, reuse=None):
    """hwv_fast.execute (same pairwise contractions, same result) with the operands of every pairwise contraction released
    early (see _contract).  reuse: dict(axis, frontier, vals, first) when F is evaluated in blocks along the output index
    `axis`: a step whose operands do not contain `axis` does not depend on the block, so it is computed in the first
    block only (first = True), the results of the `frontier` steps (those consumed by a block-dependent step) are kept in
    vals, and the later blocks skip every block-independent step."""
    ops = list(ops)
    for si, step in enumerate(path):
        step = sorted(step, reverse=True)
        taken = [ops.pop(k) for k in step]
        rest = set(''.join(i for i, _ in ops)) | set(out)
        ind = reuse is not None and not any(reuse['axis'] in i for i, _ in taken)
        if ind and not reuse['first']:
            ops.append((_step_out([i for i, _ in taken], rest), reuse['vals'].get(si)))
            del taken
            continue
        while len(taken) > 1:
            others = rest | set(''.join(i for i, _ in taken[:-2]))
            ia, ib = taken[-1][0], taken[-2][0]
            keep = ''.join(dict.fromkeys(i for i in ia + ib if i in others))
            pair = [taken.pop(), taken.pop()]
            taken.append((keep, _contract(pair, keep)))
        ia, A = taken.pop()
        keep = ''.join(dict.fromkeys(i for i in ia if i in rest))
        if keep != ia:
            A = single_reduce(ia, A, keep); ia = keep
        if ind and si in reuse['frontier']:
            reuse['vals'][si] = A
        ops.append((ia, A))
        del A
    assert len(ops) == 1
    ia, A = ops.pop()
    return single_reduce(ia, A, out)

def slice_plan(ops, out, path, axis=None, b=None):
    """symbolic run of execute() along `path` (index strings and shapes only), optionally in blocks of length b of the
    output index `axis` (Y: source points, Z: target points; b = None: the whole index).  A tensor depends on the block
    iff its index string contains `axis` (output indices are never summed).  Returns a dict:
      peak      largest number of float64 elements alive at once in the FIRST block (which also computes the
                block-independent part): every intermediate still needed, the transposed copies of both operands and the
                product of each pairwise contraction, the kept frontier tensors (leaves, i.e. the minors, not counted);
      frontier  block-independent steps consumed by a dependent one (execute(reuse) keeps them for the later blocks);
      fl_dep, fl_ind  flops (product of the dimensions of each pairwise contraction) of dependent / independent steps,
                at block length b;  ndep: number of dependent pairwise contractions;  big: largest tensor."""
    dims = {}
    for i, A in ops:
        dims.update(zip(i, A.shape))
    if axis is not None and b is not None:
        dims[axis] = min(dims[axis], b)
    sz = lambda s: float(np.prod([dims[c] for c in s])) if s else 1.0
    dep_of = lambda s: axis is not None and axis in s
    # first pass: which steps form the frontier
    idxs = [i for i, _ in ops]; made = [None] * len(idxs); frontier = set()
    for si, step in enumerate(path):
        step = sorted(step, reverse=True)
        taken = [(idxs.pop(k), made.pop(k)) for k in step]
        rest = set(''.join(idxs)) | set(out)
        if any(dep_of(i) for i, _ in taken):
            frontier |= {m for i, m in taken if m is not None and not dep_of(i)}
        idxs.append(_step_out([i for i, _ in taken], rest)); made.append(si)
    # second pass: live memory and flops; ops entries (idx, size or 0 for a leaf, step that made it)
    live = [(i, 0.0, None) for i, _ in ops]
    res = dict(peak=0.0, frontier=frontier, fl_dep=0.0, fl_ind=0.0, ndep=0, big=0.0)
    kept = 0.0                                                  # frontier tensors made so far (kept to the end)
    for si, step in enumerate(path):
        step = sorted(step, reverse=True)
        taken = [live.pop(k) for k in step]
        rest = set(''.join(i for i, _, _ in live)) | set(out)
        dep = any(dep_of(i) for i, _, _ in taken)
        while len(taken) > 1:
            base = sum(s for _, s, m in live if m not in frontier) + sum(s for _, s, m in taken[:-2] if m not in frontier) + kept
            others = rest | set(''.join(i for i, _, _ in taken[:-2]))
            (ia, sa, ma), (ib, sb, mb) = taken.pop(), taken.pop()
            keep = ''.join(dict.fromkeys(i for i in ia + ib if i in others))
            ca, cb, cr = sz(ia), sz(ib), sz(keep)
            fa = 0.0 if ma in frontier else sa                  # operands freed after their copy (unless kept)
            fb = 0.0 if mb in frontier else sb
            res['peak'] = max(res['peak'], base + fa + fb + ca, base + fb + ca + cb, base + ca + cb + cr)
            res['big'] = max(res['big'], ca, cb, cr)
            res['fl_dep' if dep else 'fl_ind'] += sz(''.join(dict.fromkeys(ia + ib)))
            res['ndep'] += dep
            taken.append((keep, cr, -1))
        ia, s, _ = taken.pop()
        o = ''.join(dict.fromkeys(i for i in ia if i in rest))
        if o != ia:
            s = sz(o)
        if si in frontier:
            kept += s
        live.append((o, s, si))
    res['peak'] = max(res['peak'], kept + sum(s for _, s, m in live if m not in frontier))
    return res

def eval_F(f, vm, pm, cheap=False, out=None):
    """F[Y, Z] for fillings f, vector minors vm, point minors pm, evaluated in blocks when the contraction needs more than
    EVALMEM float64 elements at once.  out: optional (N1, K) array (e.g. a uint32 slice of the flats array) that receives F
    directly, without the int64 copy; returned.

    Blocks (2026-10-23).  The memory of a block is the simulated peak of execute() (slice_plan: live intermediates,
    transposed copies, products), not only the largest intermediate.  Candidates: (a) the optimal path of the whole
    network, run in blocks of source points (Y) or of target points (Z), the block-independent part computed once
    (execute(reuse)); (b) only if (a) cannot fit EVALMEM: as before, paths of halved block shapes (one DP search per
    halving, up to minutes on d = 10 networks), with that reuse when one index is split.  Cost =
    flops + STEPCOST per block-dependent pairwise contraction and block.  Before, every block recomputed the
    block-independent part, which made small blocks slow (555 d=10 (82 | 61111, 61111): 0.22 s of a 0.69 s block), and
    blocks were sized by the largest intermediate (<= MEMCAP) only, so one evaluation could hold 3-5 MEMCAP."""
    N1 = next(iter(pm[0].values())).shape[0]; K = next(iter(pm[1].values())).shape[0]
    ops, outi = build_network(f, vm, pm)
    path, info, big = best_path(ops, outi, cheap=cheap)
    if slice_plan(ops, outi, path)['peak'] <= EVALMEM:
        R = execute(ops, outi, path)
        if out is None:
            return R.astype(np.int64)
        np.copyto(out, R, casting='unsafe')
        return out
    Y, Z = oe.get_symbol(0), oe.get_symbol(1)
    cands = []
    def fit(o, outx, pth, axis, n):
        """largest block length along axis whose first block fits EVALMEM (binary search; 0 if none)."""
        lo, hi = 0, n
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if slice_plan(o, outx, pth, axis, mid)['peak'] <= EVALMEM:
                lo = mid
            else:
                hi = mid - 1
        return lo
    for axis, n in ((Y, N1), (Z, K)):                          # (a) the whole network's path in blocks
        bl = fit(ops, outi, path, axis, n)
        if bl >= 1:
            a = slice_plan(ops, outi, path, axis, bl)
            nbk = -(-n // bl)
            cands.append((a['fl_ind'] + (a['fl_dep'] + STEPCOST * a['ndep']) * nbk,
                          bl if axis == Y else N1, bl if axis == Z else K, path, axis, a['frontier']))
    for order in (() if cands else ('Z', 'Y')):                 # (b) only if (a) cannot fit: paths of smaller block shapes
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
            axis = Y if zb == K else Z if yb == N1 else None
            a = slice_plan(o2, out2, pb, axis)
            if a['peak'] <= EVALMEM:
                break
        nbk = (-(-N1 // yb)) * (-(-K // zb))
        cands.append((a['fl_ind'] + (a['fl_dep'] + STEPCOST * a['ndep']) * nbk if axis is not None else
                      (a['fl_ind'] + STEPCOST * len(pb)) * nbk, yb, zb, pb, axis, a['frontier'] if axis is not None else None))
    _, yb, zb, pb, axis, frontier = min(cands, key=lambda c: c[0])
    reuse = None if axis is None else dict(axis=axis, frontier=frontier, vals={}, first=True)
    F = np.zeros((N1, K), dtype=np.int64) if out is None else out
    for y0 in range(0, N1, yb):
        for z0 in range(0, K, zb):
            ys, zs = slice(y0, min(N1, y0 + yb)), slice(z0, min(K, z0 + zb))
            o2, out2 = build_network(f, vm, _slice_pm(pm, ys, zs))
            np.copyto(F[ys, zs], execute(o2, out2, pb, reuse), casting='unsafe')   # the block's path also fits the smaller edge blocks
            if reuse:
                reuse['first'] = False
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
        fills = self.basis(tri)
        F = np.empty((len(fills), self.N1[tri[0]], self.K[tri[1:]]), dtype=np.uint32)   # filled in place (no int64 stack)
        for i, f in enumerate(fills):
            eval_F(f, self.vm(r), self.pm(tri), out=F[i])
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

    def release(self, tri, r):
        """free the in-memory flattening of (tri, r) if the disk cache holds it (a later flats() call reloads it);
        without a disk cache it stays in memory, as before."""
        if self.cache and (tri, r) in self._F and os.path.exists(
                os.path.join(self.cache, 'r%d_%s_%s_%s.npy' % (r, fmt(tri[0]), fmt(tri[1]), fmt(tri[2])))):
            del self._F[(tri, r)]

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
        (lam, (mu, nu)) -> Psi array (g, k, l); default generic (Context.psi with `tag`).  float64 residues."""
        R = sum(k * self.N1[lam] for lam, k in rows); C = sum(l * self.K[mn] for mn, l in cols)
        M = np.zeros((R, C), dtype=np.float64)
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
                            M[r0 + x * N1:r0 + (x + 1) * N1, c0 + y * K:c0 + (y + 1) * K] = fcombine(Psi[:, x, y], Fs)
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
        M = fmm(_residues(M), rng.integers(0, p, (C, R + EXTRA)).astype(np.float64))
    elif R > C + 2 * EXTRA:
        M = fmm(rng.integers(0, p, (C + EXTRA, R)).astype(np.float64), _residues(M))
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
            self.size = self.ambient                  # coordinates kept: all of the ambient space
        else:
            K = ctx.K[tuple(key)]
            bound = min(aux * (K - EXTRA), sum(self.gm[m] * ctx.n1(m) for m in self.members))
            self.ambient = aux * K
            self.rankcap = bound
            self.size = min(self.ambient, bound + EXTRA)
        self.mats = {r: {} for r in ctx.ranks}
        self._dims = {}
        self.build()

    # Storage (2026-10-23, replaces one size x size compressed matrix per member, level and rank, which made the family-B
    # lattices of 555 at d = 9, 10 (size 12000..14000) hold 5..10 GB).  Each subspace V_s, s = (member, level), of the
    # ambient space is kept as a THIN matrix mats[r][s] (float32 residues, u_s x ncols) whose rows span its image under a
    # fixed projection pi of the ambient space onto its first ncols "generic" coordinates, u_s <= dim V_s + EXTRA:
    #   * coordinates: aux = 1: the sample points themselves (target points for B, source points for A) -- the same
    #     generic coordinates whose prefixes the old dims() used ([:, :c]); aux >= 2: random combinations W (ambient x t,
    #     lazily generated column blocks, so that every prefix is the same projection);
    #   * rows: the rows of the level blocks of the member (B: source points x level; A: target points x level, i.e. the
    #     columns of the column block), or u_s = dim V_s + EXTRA random combinations of them when there are more;
    #   * dim V_s (the single dims) is found first on sketches with t = 512, 1024, ... coordinates, until it is at most
    #     t - EXTRA (a prefix of t generic coordinates is injective on a space of dim <= t - EXTRA, as in the old dims());
    #   * ncols = min(size, sum over members of the top-level dim + EXTRA): no sum of subspaces is larger, so the
    #     projection onto ncols generic coordinates is injective on every sum.
    # dims(S) is then the rank of the stacked thin matrices (about h x h, h = sum of the single dims), the same number as
    # the old c x c rank of R[:c] (sum mats[:, :c]); the single dims need no extra rank.  Memory: sum_s u_s x ncols
    # float32 per rank instead of (number of member levels) x size^2 uint32 plus size^2 int64 temporaries.

    def _proj(self, t):
        """W[:, :t]: ambient x t random projection (aux >= 2), generated in column blocks of 512 with their own seeds."""
        have = 0 if self._W is None else self._W.shape[1]
        if t > have:
            ctx = self.ctx
            kid = [0, ctx.pidx[0][self.key]] if self.kind == 'A' else [1, ctx.pidx[1][self.key[0]], ctx.pidx[2][self.key[1]]]
            blocks = [] if self._W is None else [self._W]
            for j in range(have // 512, -(-t // 512)):
                rng = np.random.default_rng([ctx.seed, 16, ctx.dirn, self.tag, self.aux, j] + kid)
                blocks.append(rng.integers(0, p, (self.ambient, 512)).astype(np.float64))
            self._W = np.hstack(blocks) if len(blocks) > 1 else blocks[0]
        return self._W[:, :t]

    def _block(self, Fs, Psi, lev, span, t):
        """rows `span` of the level-lev increment of a member's spanning set (B: source points of row block x = lev - 1;
        A: target points of column block y = lev - 1), on the first t projected coordinates: float64 (len(span), t)."""
        def inc(a2, coords):
            if self.kind == 'B':
                return fcombine(Psi[:, lev - 1, a2], Fs, span, coords)              # source points x target points
            return fcombine(Psi[:, a2, lev - 1], Fs, coords, span).T                # target points x source points
        if self.aux == 1:
            return inc(0, slice(0, t))
        if t >= self.ambient:
            return np.hstack([inc(a2, slice(None)) for a2 in range(self.aux)])
        W = self._proj(t); L = self.ambient // self.aux
        acc = None
        for a2 in range(self.aux):
            part = fmm(np.ascontiguousarray(inc(a2, slice(None))), W[a2 * L:(a2 + 1) * L])
            acc = part if acc is None else _fmod(acc + part)
        return acc

    def _member(self, m, r, Psi, crng):
        """single dims {level: dim V_(m, level)} and thin matrices {level: (u x cap) float32} of member m, rank r."""
        ctx, levs = self.ctx, self.levels[m]
        top = max(levs)
        Fs = ctx.flats(self.tri(m), r)
        R = ctx.N1[m] if self.kind == 'B' else ctx.K[m]          # spanning rows per level
        def spans(t):
            ch = max(1, CHUNK // max(t, self.ambient if self.aux > 1 else 1))
            return [slice(i, min(R, i + ch)) for i in range(0, R, ch)]
        def rand(u, n):
            return crng.integers(0, p, (u, n)).astype(np.float64)
        # 1. single dims on sketches of t coordinates (rows: raw while at most t of them, then t random combinations)
        t = min(self.cap, self._t0.get(m, 512))
        while True:
            d, raw, acc = {}, [], None
            for lev in range(1, top + 1):
                for sp in spans(t):
                    B = self._block(Fs, Psi, lev, sp, t)
                    if acc is None and sum(x.shape[0] for x in raw) + B.shape[0] <= t:
                        raw.append(B); continue
                    if acc is None:
                        acc = np.zeros((t, t))
                        for Bo in raw:
                            acc += fmm(rand(t, Bo.shape[0]), Bo)
                            np.fmod(acc, p, out=acc)
                        raw = None
                    acc += fmm(rand(t, B.shape[0]), B)
                    np.fmod(acc, p, out=acc)
                if lev in levs:
                    d[lev] = modrank(acc if acc is not None else np.vstack(raw))
            if d[top] <= t - EXTRA or t >= self.cap:
                break
            t = min(self.cap, 2 * t)
        self._t0[m] = t                                         # dims grow with the rank: start the next rank here
        # 2. thin matrices on all cap coordinates
        need = {lev: d[lev] + EXTRA for lev in levs}
        rawlev = [lev for lev in levs if lev * R <= need[lev]]  # few rows: keep them all (exact, no combinations)
        U = max([need[lev] for lev in levs if lev not in rawlev], default=0)
        raw, acc, out = [], (np.zeros((U, self.cap)) if U else None), {}
        for lev in range(1, top + 1):
            for sp in spans(self.cap):
                B = self._block(Fs, Psi, lev, sp, self.cap)
                if rawlev and lev <= max(rawlev):
                    raw.append(B.astype(np.float32))
                if U:
                    acc += fmm(rand(U, B.shape[0]), B)
                    np.fmod(acc, p, out=acc)
                del B
            if lev in levs:
                out[lev] = np.vstack(raw) if lev in rawlev else acc[:need[lev]].astype(np.float32)
        ctx.release(self.tri(m), r)
        return d, out

    def build(self):
        ctx, a = self.ctx, self.aux
        # coordinates kept until all single dims are known: aux = 1: the first `size` sample points; aux >= 2: all
        # (raw) ambient coordinates, projected by W once ncols is known
        self.cap = self.size if a == 1 else self.ambient
        self._W, self._t0 = None, {}
        sd = {r: {} for r in ctx.ranks}
        for m in self.members:
            tri = self.tri(m); top = max(self.levels[m])
            # generic Psi (g, k, l): family A: k = aux, l = level (nested); family B: k = level (nested), l = aux
            Psi = ctx.psi(tri, a, top, self.tag) if self.kind == 'A' else ctx.psi(tri, top, a, self.tag)
            crng = np.random.default_rng([ctx.seed, 17, ctx.dirn, self.tag, a, 0 if self.kind == 'A' else 1] + ctx.tri_index(tri))
            for r in ctx.ranks:
                d, thin = self._member(m, r, Psi, crng)
                for lev in self.levels[m]:
                    sd[r][(m, lev)] = d[lev]
                    self.mats[r][(m, lev)] = thin[lev]
        for m in self.members:
            for lev in self.levels[m]:
                self._dims[((m, lev),)] = tuple(sd[r][(m, lev)] for r in ctx.ranks)
        H = max([sum(sd[r][(m, max(self.levels[m]))] for m in self.members) for r in ctx.ranks], default=0)
        self.ncols = min(self.size, H + EXTRA)
        if self.ncols < self.cap:
            for r in ctx.ranks:
                for s, Z in self.mats[r].items():
                    self.mats[r][s] = (np.ascontiguousarray(Z[:, :self.ncols]) if a == 1 else
                                       fmm(Z.astype(np.float64), self._proj(self.ncols)).astype(np.float32))
        self._W = None

    def dims(self, S):
        """S: iterable of (member, level).  Returns (dim on rank r_1, ..., dim on rank r_last).
        The sum has dim <= h = sum of the single dims, so the first c = h + EXTRA (generic) coordinates are injective on
        it: rank of the stacked thin matrices restricted to c columns (about h x h), exact except with probability
        < p^-EXTRA per subset (as before, when the c x c matrix R[:c] (sum of size x c slices) was ranked)."""
        key = tuple(sorted(S, key=repr))
        if key not in self._dims:
            c = min(self.ncols, sum(max(self._dims[(s,)]) for s in key) + EXTRA)
            self._dims[key] = tuple(modrank(np.vstack([self.mats[r][s][:, :c] for s in key])) for r in self.ctx.ranks)
        return self._dims[key]

    def basis_rows(self, r, s):
        """RREF basis (rows in F_p^ncols, the projected coordinates) of the subspace of (member, level) s for the rank-r
        tensor (cached): the column space of the column block for family A, the row space of the row block for B."""
        if not hasattr(self, '_basis'):
            self._basis = {}
        if (r, s) not in self._basis:
            # stored as float32: residues < p < 2^24 are exact, half the memory of float64 (the exhaustive enumeration of
            # large family-B lattices held several GB of bases per worker)
            self._basis[(r, s)] = rref(self.mats[r][s])[0].astype(np.float32)
        return self._basis[(r, s)]

    def greedy(self, start, candidates, rng, score):
        """grow S from `start` by one candidate at a time, maximising score(dims) (ties: random); incremental
        (RREF basis of the current sum per rank, candidates reduced modulo it).  Returns the chain [(S, dims)]."""
        ranks = self.ctx.ranks
        cur = {r: (np.zeros((0, self.ncols)), []) for r in ranks}
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
        dfs(0, {r: (np.zeros((0, self.ncols)), []) for r in ranks}, [])
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
