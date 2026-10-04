"""Shared helpers for comparing isotypic flattening ranks of M2 (2x2 matrix multiplication) with random rank-6 / rank-7
tensors in C^4 (x) C^4 (x) C^4 on the 4-way isotypic tensor Phi(T) in S^{l1}V (x) S^{l2}V (x) S^{l3}V (x) M.
Evaluation as in hwv_fast/flatlib (exact mod p, HWV spanning sets): F_j[Y, Z] = <Phi_{phi_j}(T), y_Y (x) z_Z> with N1
random source points y and K random target pairs z; phi_1..phi_g = functionals of g random Young fillings whose isotypic
tensors (on a random rank-7 tensor) are linearly independent, i.e. a basis of M^*.
For a k-dim U = span of the rows of C (k x g) in M^*:
  H_k(U) = rank of [G_1 | ... | G_k] (N1 x kK)   = n1 - dim of the common kernel  (stack S^{l1}V^* -> U^* (x) rest)
  V_k(U) = rank of [G_1; ...; G_k]  (kN1 x K)   = dim of the sum of the images     (U (x) S^{l1}V^* -> rest)
  with G_i = sum_j C_ij F_j.  Ranks are exact lower bounds of the true ranks (sampled matrix, rank mod p <= rank over Q);
  they equal the true ranks when N1, K exceed them (random points)."""
import os, sys, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hwv, isoflat, hwv_fast
p = hwv.p
from hwv import dim_schur, random_fillings, random_gs
from isoflat import kronecker
import flatlib

E4 = np.eye(4, dtype=np.int64)
def _ij(i, j): return E4[2 * i + j]

def m2_terms(kind='strassen'):
    """rank-one decomposition (A, B, C) of M2 = sum_{ijk} e_ij (x) e_jk (x) e_ki: 'naive' (8 terms) or 'strassen' (7)."""
    if kind == 'naive':
        t = [(_ij(i, j), _ij(j, k), _ij(k, i)) for i in range(2) for j in range(2) for k in range(2)]
    else:
        a11, a12, a21, a22 = _ij(0, 0), _ij(0, 1), _ij(1, 0), _ij(1, 1)
        b11, b12, b21, b22 = a11, a12, a21, a22
        c11, c12, c21, c22 = _ij(0, 0), _ij(1, 0), _ij(0, 1), _ij(1, 1)
        t = [(a11 + a22, b11 + b22, c11 + c22), (a21 + a22, b11, c21 - c22), (a11, b12 - b22, c12 + c22),
             (a22, b21 - b11, c11 + c21), (a11 + a12, b22, c12 - c11), (a21 - a11, b11 + b12, c22),
             (a12 - a22, b21 + b22, c11)]
    return tuple(np.array([x[s] for x in t], dtype=np.int64) % p for s in range(3))

def full_tensor(v):
    return np.einsum('ri,rj,rk->ijk', *[x.astype(object) for x in v]) % p

assert (full_tensor(m2_terms('naive')) == full_tensor(m2_terms('strassen'))).all()

def frank(M, b=64):
    """rank mod p via panel-blocked Gaussian elimination; trailing updates as exact float64 matmuls (inner dim <= b)."""
    A = np.fmod(np.array(M, dtype=np.float64), p)
    A[A < 0] += p
    if A.size == 0: return 0
    if A.shape[0] > A.shape[1]: A = np.ascontiguousarray(A.T)
    rank = 0
    while A.shape[0] > 0 and A.shape[1] > 0:
        m, n = A.shape
        bw = min(b, n)
        P = A[:, :bw].copy()
        Mul = np.zeros((m, bw)); ispiv = np.zeros(m, dtype=bool); piv = []
        for j in range(bw):
            cand = np.flatnonzero((P[:, j] != 0) & ~ispiv)
            if cand.size == 0: continue
            i = cand[0]; ispiv[i] = True; piv.append((i, j))
            inv = float(pow(int(P[i, j]), p - 2, p))
            others = np.flatnonzero(~ispiv & (P[:, j] != 0))
            if others.size:
                mult = np.fmod(P[others, j] * inv, p)
                Mul[others, j] = mult
                P[others, j:] = np.fmod(P[others, j:] - np.fmod(np.outer(mult, P[i, j:]), p) + p, p)
        s = len(piv); rank += s
        rest = np.flatnonzero(~ispiv)
        if bw == n or rest.size == 0: break
        T = A[:, bw:]
        if s == 0:
            A = np.ascontiguousarray(T); continue
        Tp = np.empty((s, n - bw))
        for a, (i, j) in enumerate(piv):
            v = T[i].copy()
            for a2 in range(a):
                mlt = Mul[i, piv[a2][1]]
                if mlt: v = np.fmod(v - np.fmod(mlt * Tp[a2], p) + p, p)
            Tp[a] = v
        Mr = Mul[rest][:, [j for _, j in piv]]
        A = np.fmod(T[rest] - np.fmod(Mr @ Tp, p) + p, p)
    return rank

def compress_cols(M, ncol, rng):
    """M @ R with R random (M.shape[1] x ncol); rank preserved w.h.p. when ncol >= rank."""
    if M.shape[1] <= ncol: return M
    R = rng.integers(0, p, (M.shape[1], ncol))
    return hwv_fast.matmul_mod(M[None], R[None])[0]

def choose_fillings(lam_p, g, probe_vecs, rng, npr=(8, 16), maxtry=None):
    """g fillings whose functionals are independent on the probe tensor (evaluated at npr random points)."""
    gp = random_gs(rng, 4, *npr)
    pre = prep_all(probe_vecs, gp)
    rows, fills = [], []
    maxtry = maxtry or 300 * g + 500
    for _ in range(maxtry):
        f = random_fillings(rng, lam_p)
        v = flat_pre(f, pre).ravel() % p
        if not v.any(): continue
        if frank(np.array(rows + [v])) == len(rows) + 1:
            rows.append(v); fills.append(f)
            if len(fills) == g: return fills
    raise RuntimeError('could not find %d independent fillings' % g)

def rand_tensor(rng, r): return tuple(rng.integers(0, p, (r, 4)) for _ in range(3))

def Hrank(Gs, rng):
    H = np.hstack(Gs); return frank(compress_cols(H, H.shape[0] + 8, rng))

def Vrank(Gs, rng):
    V = np.vstack(Gs); return frank(compress_cols(V.T, V.shape[1] + 8, rng))

def combine(Fs, c):
    out = np.zeros(Fs[0].shape, dtype=np.int64)
    for x, F in zip(c, Fs):
        out = (out + int(x) * F.astype(np.int64)) % p
    return out


def prefix_ranks(A, bounds, b=64):
    """ranks mod p of A[:, :c] for every c in `bounds` (increasing column counts), one left-to-right panel elimination
    (columns are never reordered; rows are, freely).  Same exact float64 scheme as frank."""
    A = np.fmod(np.array(A, dtype=np.float64), p)
    A[A < 0] += p
    out, rank, col = [], 0, 0
    bounds = list(bounds); bi = 0
    while bi < len(bounds) and bounds[bi] <= 0:
        out.append(0); bi += 1
    while A.shape[0] > 0 and A.shape[1] > 0 and bi < len(bounds):
        m, n = A.shape
        bw = min(b, n, bounds[bi] - col)
        P = A[:, :bw].copy()
        Mul = np.zeros((m, bw)); ispiv = np.zeros(m, dtype=bool); piv = []
        for j in range(bw):
            cand = np.flatnonzero((P[:, j] != 0) & ~ispiv)
            if cand.size == 0: continue
            i = cand[0]; ispiv[i] = True; piv.append((i, j))
            inv = float(pow(int(P[i, j]), p - 2, p))
            others = np.flatnonzero(~ispiv & (P[:, j] != 0))
            if others.size:
                mult = np.fmod(P[others, j] * inv, p)
                Mul[others, j] = mult
                P[others, j:] = np.fmod(P[others, j:] - np.fmod(np.outer(mult, P[i, j:]), p) + p, p)
        s = len(piv); rank += s; col += bw
        while bi < len(bounds) and bounds[bi] <= col:
            out.append(rank); bi += 1
        rest = np.flatnonzero(~ispiv)
        if bw == n or rest.size == 0:
            break
        T = A[:, bw:]
        if s == 0:
            A = np.ascontiguousarray(T); continue
        Tp = np.empty((s, n - bw))
        for a, (i, j) in enumerate(piv):
            v = T[i].copy()
            for a2 in range(a):
                mlt = Mul[i, piv[a2][1]]
                if mlt: v = np.fmod(v - np.fmod(mlt * Tp[a2], p) + p, p)
            Tp[a] = v
        Mr = Mul[rest][:, [j for _, j in piv]]
        A = np.fmod(T[rest] - np.fmod(Mr @ Tp, p) + p, p)
    while len(out) < len(bounds): out.append(rank)
    return out


# ---------------------------------------------------------------- faster evaluation (same numbers as flatlib.flat)
# (1) exact reduction mod p by floor-division instead of np.fmod (libm fmod is ~5x slower); values are integers < 2^53
_INVP = 1.0 / p
def _fmod_fast(A):
    if not (isinstance(A, np.ndarray) and A.dtype == np.float64):
        return np.fmod(A, p)
    q = np.multiply(A, _INVP); np.floor(q, out=q); q *= p; A -= q
    np.add(A, p, out=A, where=A < 0)
    np.subtract(A, p, out=A, where=A >= p)
    return A
hwv_fast._fmod = _fmod_fast            # used by hwv_fast.fmatmul / pair_contract / single_reduce (this process only)

import opt_einsum as _oe
from hwv_fast import prepare as _prepare, build_network as _build, find_path as _find_path, execute as _execute
_paths2 = {}
def prep_all(vecs, gs):
    """minors for all column lengths 1..4 once per tensor (flatlib recomputes them for every filling)."""
    return _prepare(vecs, gs, ells=[1, 2, 3, 4])

def flat_pre(f, pre, memcap=1 << 24, repeats=12):
    """flatlib.flat with precomputed minors `pre` = prep_all(vecs, gs); identical matrix."""
    vm, pm = pre
    N1 = next(iter(pm[0].values())).shape[0]; K = next(iter(pm[1].values())).shape[0]
    shp = tuple(vm[0][1].shape[1:2]) + (N1, K)
    k0 = (tuple(tuple(tuple(int(x) for x in col) for col in cols) for cols in f), shp)
    def sl(ys, zs):
        return [{l: A[ys] for l, A in pm[0].items()}, {l: A[zs] for l, A in pm[1].items()}, {l: A[zs] for l, A in pm[2].items()}]
    if k0 not in _paths2:
        yb, zb = N1, K
        while True:
            ops, out = _build(f, vm, sl(slice(0, yb), slice(0, zb)))
            path, info = _find_path(ops, out, None, _oe.RandomGreedy(max_repeats=repeats))
            big = int(info.largest_intermediate)
            if big > memcap and len(ops) <= 24:
                # size-minimising path (the RandomGreedy path can keep a word-index-only intermediate)
                p2, i2 = _find_path(ops, out, None, _oe.DynamicProgramming(minimize='size'))
                if int(i2.largest_intermediate) < big:
                    path, info, big = p2, i2, int(i2.largest_intermediate)
            if big <= memcap: break
            if zb <= 1 and yb <= 1:
                if big <= 8 * memcap: break           # proceed with a larger intermediate (<= 1 GB) rather than fail
                raise MemoryError('no block split keeps intermediates below 8*memcap (%d)' % big)
            if zb > 1: zb = (zb + 1) // 2
            else: yb = (yb + 1) // 2
        _paths2[k0] = (yb, zb, path)
    yb, zb, path = _paths2[k0]
    F = np.zeros((N1, K), dtype=np.int64)
    for y0 in range(0, N1, yb):
        for z0 in range(0, K, zb):
            ys, zs = slice(y0, min(N1, y0 + yb)), slice(z0, min(K, z0 + zb))
            ops, out = _build(f, vm, sl(ys, zs))
            F[ys, zs] = _execute(ops, out, path)
    return F
