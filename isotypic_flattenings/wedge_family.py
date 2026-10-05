"""python3 wedge_family.py n d r1,r2,...     exact ranks of the component ((d),(1^d),(1^d)) on random rank-r tensors.

For lam = ((d), (1^d), (1^d)) (Kronecker coefficient 1) every word with a repeated letter is killed by the
antisymmetrisation in the second factor, and an injective word w (an ordering of a d-set S) contributes
a_S (x) sgn(w) wedge b_S (x) sgn(w) wedge c_S.  So, up to the factor d! (a unit mod p for d < p), the isotypic tensor of
T = sum_{i<=r} a_i (x) b_i (x) c_i is
        X_T = sum_{S in binom([r], d)}  a_S (x) (wedge_{i in S} b_i) (x) (wedge_{i in S} c_i),     a_S = prod_{i in S} a_i,
and its flattenings are products of small matrices: with E[S, y] = prod_{i in S} <a_i, x_y> (x_y random points; the
powers x_y^d span S^d), Bm[S, J] = det B[S, J], Cm[S, K] = det C[S, K] (J, K in binom([n], d)):
    direction 1  S^d A^* -> wedge^d B (x) wedge^d C :  rank of E^T (Bm * Cm)   (row-wise Kronecker product),
    direction 2  wedge^d B^* -> S^d A (x) wedge^d C :  rank of Bm^T (E * Cm)    (direction 3 is the same by symmetry).
No word-minor tensor of size C(n,d) r^d is formed, so ranks far beyond rankscan.py's WCAP limit are cheap.
Columns are compressed by a random matrix with 8 more columns than the rank bound (exact mod p = 524287)."""
import sys, itertools, numpy as np
from math import comb
from hwv import p
import hwv_fast
from rankscan import RREF, vector_minors, generic_rank


def mm(A, B):
    return hwv_fast.fmatmul(np.ascontiguousarray(A, dtype=np.float64)[None], np.ascontiguousarray(B, dtype=np.float64)[None])[0]


def rank_of(M):
    E = RREF(M.shape[1])
    return E.add(M)


def batch_det(M):
    """determinants mod p of a batch of d x d matrices M (..., d, d) of residues (Gaussian elimination, exact)."""
    M = np.array(M, dtype=np.int64) % p
    sh = M.shape[:-2]; d = M.shape[-1]
    M = M.reshape(-1, d, d); det = np.ones(M.shape[0], dtype=np.int64)
    for c in range(d):
        nz = M[:, c:, c] != 0
        has = nz.any(axis=1)
        det[~has] = 0
        piv = c + np.argmax(nz, axis=1)
        swap = (piv != c) & has
        if swap.any():
            ii = np.nonzero(swap)[0]
            tmp = M[ii, c].copy(); M[ii, c] = M[ii, piv[ii]]; M[ii, piv[ii]] = tmp
            det[ii] = (-det[ii]) % p
        pv = M[:, c, c].copy(); pv[~has] = 1
        det = (det * pv) % p
        inv = np.array([pow(int(x), p - 2, p) for x in pv], dtype=np.int64)
        f = (M[:, c + 1:, c] * inv[:, None]) % p
        M[:, c + 1:, c:] = (M[:, c + 1:, c:] - (f[:, :, None] * M[:, None, c, c:]) % p) % p
    return det.reshape(sh)


def minors_by_subset(V, d, subsets, chunk=4096):
    """Bm[S, J] = det V[S, J] for the row subsets S (sorted) and all J in binom([n], d) -- only these
    C(r,d) x C(n,d) minors are formed (vector_minors would build all r^d words)."""
    n = V.shape[1]
    Js = np.array(list(itertools.combinations(range(n), d)))
    Ss = np.array(subsets)
    out = np.zeros((len(Ss), len(Js)))
    for s0 in range(0, len(Ss), chunk):
        rows = V[Ss[s0:s0 + chunk]]                      # (c, d, n)
        sub = rows[:, :, Js]                              # (c, d, nJ, d)
        out[s0:s0 + chunk] = batch_det(np.transpose(sub, (0, 2, 1, 3)))
    return out


def ranks(n, d, r, seed=1, verbose=False):
    rng = np.random.default_rng([seed, n, d, r])
    A, B, C = (rng.integers(0, p, (r, n)) for _ in range(3))
    subsets = list(itertools.combinations(range(r), d))
    nS = len(subsets)
    dimS = comb(n + d - 1, d); dimW = comb(n, d)
    X = rng.integers(0, p, (dimS + 8, n))         # points x_y
    AX = mm(A, X.T)                               # (r, Y): <a_i, x_y>
    E = np.ones((nS, X.shape[0]))
    for k in range(d):
        rows = [S[k] for S in subsets]
        E = np.fmod(E * AX[rows], p)
    Bm = minors_by_subset(B, d, subsets); Cm = minors_by_subset(C, d, subsets)
    # direction 1: E^T (Bm * Cm), compress the dimW^2 columns
    m1 = min(dimS, dimW * dimW, nS) + 8
    R1 = rng.integers(0, p, (dimW, dimW, m1)).astype(np.float64)
    # (Bm * Cm) R1 without forming the Kronecker product: sum_J Bm[S, J] * (Cm @ R1[J])[S]
    W = np.zeros((nS, m1))
    for J in range(dimW):
        W = np.fmod(W + np.fmod(Bm[:, J:J + 1] * mm(Cm, R1[J]), p), p)
    r1 = rank_of(mm(E.T, W))
    # direction 2: Bm^T (E * Cm), compress the dimS*dimW columns
    m2 = min(dimW, dimS * dimW, nS) + 8
    R2 = rng.integers(0, p, (dimW, m2)).astype(np.float64)
    CR = mm(Cm, R2)                               # (nS, m2)
    Q = np.zeros((nS, m2))
    G = rng.integers(0, p, (X.shape[0], m2)).astype(np.float64)
    # E * Cm compressed by a random (Y x K) -> m2 map of the form sum_y,K E[S,y] Cm[S,K] G[y,j] R2[K,j]
    EG = mm(E, G)                                 # (nS, m2)
    Q = np.fmod(EG * CR, p)
    r2 = rank_of(mm(Bm.T, Q))
    return r1, r2, min(dimS, dimW * dimW), min(dimW, dimS * dimW)


if __name__ == '__main__':
    n, d = int(sys.argv[1]), int(sys.argv[2])
    rs = [int(x) for x in sys.argv[3].split(',')] if len(sys.argv) > 3 else list(range(d, generic_rank(n) + 1))
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    print('# ((%d),(1^%d),(1^%d)) on C^%d: dims S^d = %d, wedge^d = %d, terms C(r,%d)' % (d, d, d, n, comb(n + d - 1, d), comb(n, d), d))
    prev = None
    for r in rs:
        r1, r2, b1, b2 = ranks(n, d, r, seed)
        sep = '' if prev is None or (prev[0] >= r1 and prev[1] >= r2) else '   <- rank %d separated from %d' % (r - 1, r)
        print('r=%2d  dir1 %d (bound %d)  dir2/3 %d (bound %d)%s' % (r, r1, b1, r2, b2, sep), flush=True)
        prev = (r1, r2)
