"""python3 onerow_family.py n "mu" r1,r2,...       exact flattening ranks of the component ((d), mu, mu), d = |mu|.

Components with a one-row partition (d) have Kronecker coefficient g = delta(mu, nu), so ((d), mu, mu) is the only
kind (g = 1).  Evaluated at a power alpha^d (the highest weight vector of S^d translated by a group element) the
isotypic tensor of T = sum a_i (x) b_i (x) c_i becomes the S^mu-part of T(alpha)^{(x) d}, T(alpha) = sum_i <a_i, alpha>
b_i c_i^T = B^T diag(A alpha) C, and its value at (g' v_mu) (x) (g'' v_mu) is the highest-weight matrix coefficient
of S^mu at g'^T T(alpha) g'':
        F = prod_{columns j of mu} Delta_{mu'_j}(g'^T T(alpha) g''),    Delta_k = leading principal k x k minor.
So the flattening matrices are products of small determinants, O(n^3) per entry, no word-minor tensor:
    direction 1  S^d V^* -> S^mu V (x) S^mu V : rows alpha_y, columns pairs (g'_z, g''_z);
    direction 2  S^mu V^* -> S^d V (x) S^mu V : rows g'_y, columns pairs (alpha_z, g''_z)   (= direction 3).
Leading minors from pivot-free elimination (random g', g'' make the pivots nonzero unless the minor vanishes
identically; after a zero pivot all larger leading minors are set to 0, which is exact up to probability ~ 1/p).
Exact mod p = 524287; validated against rankscan.py (see the validation run in scan/onerow_check.log)."""
import sys, itertools, numpy as np
from math import comb
from hwv import p, dim_schur
from rankscan import RREF, generic_rank


def leading_minors(G, ks):
    """G: (N, n, n) int64 residues; returns {k: Delta_k(G)} for k in ks.  Pivot-free elimination; an entry whose
    pivot vanishes before the last needed size (identically, or by accident with probability ~1/p per pivot) gets
    its larger leading minors recomputed exactly with a pivoting determinant (wedge_family.batch_det)."""
    from wedge_family import batch_det
    G0 = G % p
    G = G0.copy()
    N, n, _ = G.shape
    kmax = max(ks)
    out = {}
    delta = np.ones(N, dtype=np.int64)
    alive = np.ones(N, dtype=bool)
    zero_at = np.full(N, kmax + 1)
    for i in range(kmax):
        piv = G[:, i, i].copy()
        z = (piv == 0) & alive
        zero_at[z] = i + 1
        alive &= ~z
        delta = np.where(alive, (delta * piv) % p, 0)
        if i + 1 in ks:
            out[i + 1] = delta.copy()
        if i + 1 == kmax:
            break
        pv = np.where(alive, piv, 1)
        inv = np.ones(N, dtype=np.int64)
        e, base = p - 2, pv % p                      # vectorised Fermat inverse
        while e:
            if e & 1:
                inv = (inv * base) % p
            base = (base * base) % p; e >>= 1
        f = (G[:, i + 1:, i] * inv[:, None]) % p
        G[:, i + 1:, i:] = (G[:, i + 1:, i:] - (f[:, :, None] * G[:, None, i, i:]) % p) % p
    fix = np.nonzero(zero_at <= kmax)[0]
    for k in ks:
        idx = fix[zero_at[fix] < k]                    # Delta_k unknown after a zero pivot at a smaller size
        if idx.size:
            out[k][idx] = batch_det(G0[idx, :k, :k])
    return out


def tmat(A, B, C, alphas):
    """T(alpha) = B^T diag(A alpha) C for a batch of alphas (N, n) -> (N, n, n)."""
    w = (alphas @ A.T) % p                             # (N, r)
    BW = (B.T[None, :, :] * w[:, None, :]) % p         # (N, n, r)
    return np.einsum('nir,rj->nij', BW, C) % p


def values(T, gp, gpp, cols):
    """prod_j Delta_{cols_j}(gp^T T gpp) for aligned batches T (N,n,n), gp, gpp (N,n,n)."""
    G = np.einsum('nki,nkl->nil', gp, np.einsum('nkl,nlj->nkj', T, gpp) % p) % p
    D = leading_minors(G, sorted(set(cols)))
    v = np.ones(T.shape[0], dtype=np.int64)
    for c in cols:
        v = (v * D[c]) % p
    return v


def rank_of(F):
    E = RREF(F.shape[1])
    return E.add(F.astype(np.float64))


def flat_rank(n, mu, A, B, C, direction, rng, chunk=200000):
    """rank of the direction-1 (source S^d) or direction-2 (source S^mu) flattening of ((d), mu, mu) at the tensor
    sum_i A[i] (x) B[i] (x) C[i]; returns (rank, rank bound min(n1, n23))."""
    d = sum(mu)
    cols = [sum(1 for x in mu if x > j) for j in range(mu[0])]
    nd, nm = comb(n + d - 1, d), dim_schur(tuple(mu), n)
    n1, n23 = (nd, nm * nm) if direction == 1 else (nm, nd * nm)
    N1 = min(n1, n23) + 8; K = min(n1, n23) + 8
    if direction == 1:
        alph = rng.integers(0, p, (N1, n)); gp = rng.integers(0, p, (K, n, n)); gpp = rng.integers(0, p, (K, n, n))
    else:
        gp = rng.integers(0, p, (N1, n, n)); alph = rng.integers(0, p, (K, n)); gpp = rng.integers(0, p, (K, n, n))
    T = tmat(np.asarray(A) % p, np.asarray(B) % p, np.asarray(C) % p, alph)
    F = np.zeros((N1, K), dtype=np.int64)
    step = max(1, chunk // K)
    for y0 in range(0, N1, step):
        ys = np.arange(y0, min(N1, y0 + step))
        yy = np.repeat(ys, K); zz = np.tile(np.arange(K), len(ys))
        v = values(T[yy], gp[zz], gpp[zz], cols) if direction == 1 else values(T[zz], gp[yy], gpp[zz], cols)
        F[ys] = v.reshape(len(ys), K)
    return rank_of(F), min(n1, n23)


def flat_ranks(n, mu, r, seed=1, chunk=200000):
    d = sum(mu)
    cols = [sum(1 for x in mu if x > j) for j in range(mu[0])]
    rng = np.random.default_rng([seed, n, d, r] + list(mu))
    A, B, C = (rng.integers(0, p, (r, n)) for _ in range(3))
    nd, nm = comb(n + d - 1, d), dim_schur(tuple(mu), n)
    res = []
    for direction in (1, 2):
        if direction == 1:
            n1, n23 = nd, nm * nm
        else:
            n1, n23 = nm, nd * nm
        N1 = min(n1, n23) + 8; K = min(n1, n23) + 8
        if direction == 1:
            alph = rng.integers(0, p, (N1, n)); gp = rng.integers(0, p, (K, n, n)); gpp = rng.integers(0, p, (K, n, n))
            T = tmat(A, B, C, alph)
        else:
            gp = rng.integers(0, p, (N1, n, n)); alph = rng.integers(0, p, (K, n)); gpp = rng.integers(0, p, (K, n, n))
            T = tmat(A, B, C, alph)
        F = np.zeros((N1, K), dtype=np.int64)
        step = max(1, chunk // K)
        for y0 in range(0, N1, step):
            ys = np.arange(y0, min(N1, y0 + step))
            yy = np.repeat(ys, K); zz = np.tile(np.arange(K), len(ys))
            if direction == 1:
                v = values(T[yy], gp[zz], gpp[zz], cols)
            else:
                v = values(T[zz], gp[yy], gpp[zz], cols)
            F[ys] = v.reshape(len(ys), K)
        res.append((rank_of(F), min(n1, n23)))
    return res


if __name__ == '__main__':
    n = int(sys.argv[1]); mu = tuple(eval(sys.argv[2])); d = sum(mu)
    rs = [int(x) for x in sys.argv[3].split(',')]
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    print('# ((%d), %s, %s) on C^%d: dim S^d = %d, dim S^mu = %d' % (d, mu, mu, n, comb(n + d - 1, d), dim_schur(mu, n)), flush=True)
    prev = None
    for r in rs:
        (r1, b1), (r2, b2) = flat_ranks(n, mu, r, seed)
        sep = '' if prev is None or (prev[0] >= r1 and prev[1] >= r2) else '   <- rank %d separated from %d' % (r - 1, r)
        print('r=%2d  dir1 %d (bound %d)  dir2/3 %d (bound %d)%s' % (r, r1, b1, r2, b2, sep), flush=True)
        prev = (r1, r2)
