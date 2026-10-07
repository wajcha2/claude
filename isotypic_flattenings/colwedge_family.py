"""python3 colwedge_family.py n "lam" "lam_T" r1,r2,...   exact flattening ranks of the component (lam, lam^T, (1^d)).

For a component with a one-column partition (1^d) the Kronecker coefficient is g = delta(mu, lam^T), so the only kind is
(lam, lam^T, (1^d)) (g = 1; ((d),(1^d),(1^d)) is the case lam = (d), see wedge_family.py).  Antisymmetrising the third
factor of T^{(x)d}, T = sum_i a_i (x) b_i (x) c_i, leaves (up to d!)
        X_T = sum_{S in binom([r], d)}  wedge_{i in S} (a_i (x) b_i)  (x)  wedge_{i in S} c_i     in  wedge^d(A (x) B) (x) wedge^d C,
and the (lam, lam^T) summand of wedge^d(A (x) B) (Cauchy) has highest weight vector  wedge_{boxes x of lam} e_{row x} (x) f_{col x}
(a raising operator repeats a factor, so it is killed; weight (lam, lam^T)).  Paired with the translates g' (A), g'' (B),
g''' (C) of the highest weight vectors, the S-term is det[<a_i, g'_{row x}> <b_i, g''_{col x}>]_{i in S, x} times
det[<c_i, g'''_k>]_{i in S, k <= d}, and by Cauchy-Binet the sum over S is ONE d x d determinant:
        F(g', g'', g''') = det( sum_i <a_i, g'_{row x}> <b_i, g''_{col x}> <c_i, g'''_k> )_{x in lam, k = 1..d}.
So every entry costs O(r d^2 + d^3), with no word-minor tensor (rankscan.py needs C(n, d) r^d entries for the column
(1^d)).  Direction t: rows = translates of the highest weight vector of factor t, columns = pairs for the other two
factors; N1 = K = min(n1, n23) + 8 generic points (g = 1, so H = V).  Exact mod p = 524287; validated against
rankscan.py (scan/colwedge_check.log)."""
import sys, numpy as np
from hwv import p, dim_schur
from rankscan import RREF
from onerow_family import leading_minors


def colwedge_roles(lam):
    """(u, v, w): factor u carries lam, factor v lam^T, factor w the column (1^d); None if lam is not of this kind."""
    d = sum(lam[0])
    for w in range(3):
        if tuple(lam[w]) == (1,) * d:
            u, v = [x for x in range(3) if x != w]
            a, b = tuple(lam[u]), tuple(lam[v])
            conj = tuple(sum(1 for y in a if y > j) for j in range(a[0]))
            if conj == b:
                return u, v, w
    return None


def is_colwedge(lam):
    return colwedge_roles(lam) is not None


def entry_blocks(lam, roles, vecs, pts, chunk_pairs, rows, cols):
    """yields (ys, F[ys, :]) blocks of rows for the aligned point sets: pts[f] = (P_f, n, m_f) random matrices for factor f; rows/cols say which
    factor is indexed by y (one factor) and by z (the other two).  vecs[f] = (r, n) tensor factors."""
    u, v, w = roles
    lu = tuple(lam[u]); d = sum(lu)
    rx = np.array([i for i, l in enumerate(lu) for _ in range(l)])          # row of each box
    cx = np.array([j for l in lu for j in range(l)])                          # column of each box
    # projections <vec_i, g_k> for every point: (P_f, r, m_f), residues
    proj = {f: np.einsum('ri,pik->prk', vecs[f], pts[f]) % p for f in range(3)}
    Y = proj[rows].shape[0]; Z = proj[cols[0]].shape[0]
    step = max(1, chunk_pairs // Z)
    for y0 in range(0, Y, step):
        ys = np.arange(y0, min(Y, y0 + step))
        yy = np.repeat(ys, Z); zz = np.tile(np.arange(Z), len(ys))
        idx = {rows: yy, cols[0]: zz, cols[1]: zz}
        al = proj[u][idx[u]][:, :, rx]                                        # (P, r, d)  <a_i, g'_{row x}>
        be = proj[v][idx[v]][:, :, cx]                                        # (P, r, d)  <b_i, g''_{col x}>
        ga = proj[w][idx[w]]                                                  # (P, r, d)  <c_i, g'''_k>
        ab = (al * be) % p
        G = np.fmod(np.matmul(np.transpose(ab, (0, 2, 1)).astype(np.float64), ga.astype(np.float64)), p).astype(np.int64)
        yield ys, leading_minors(G, [d])[d].reshape(len(ys), Z)


def flat_rank(n, lam, vecs, t, rng, chunk_pairs=200000):
    """rank of the direction-t flattening of (lam, lam^T, (1^d)) at the tensor sum_i vecs[0][i] (x) vecs[1][i] (x) vecs[2][i];
    returns (rank, rank bound min(n1, n23))."""
    roles = colwedge_roles(lam)
    assert roles is not None, lam
    d = sum(lam[0])
    dims = [dim_schur(tuple(l), n) for l in lam]
    n1 = dims[t]; n23 = 1
    for f in range(3):
        if f != t:
            n23 *= dims[f]
    N1 = K = min(n1, n23) + 8
    others = [f for f in range(3) if f != t]
    m = {f: d for f in range(3)}                                              # columns of g used: <= d
    pts = {t: rng.integers(0, p, (N1, n, m[t]))}
    for f in others:
        pts[f] = rng.integers(0, p, (K, n, m[f]))
    vv = [np.asarray(x, dtype=np.int64) % p for x in vecs]
    E = RREF(K)                     # rows go straight into the incremental echelon form: the N1 x K matrix is never stored
    for ys, blk in entry_blocks(lam, roles, vv, pts, chunk_pairs, t, others):
        E.add(blk.astype(np.float64))
        if E.rank >= min(n1, n23):
            break                   # at the bound: the remaining rows cannot raise the rank
    return E.rank, min(n1, n23)


if __name__ == '__main__':
    n = int(sys.argv[1]); lam = tuple(tuple(eval(x)) for x in sys.argv[2:5])
    rs = [int(x) for x in sys.argv[5].split(',')]
    seed = int(sys.argv[6]) if len(sys.argv) > 6 else 1
    print('# %s on C^%d, roles %s, dims %s' % (lam, n, colwedge_roles(lam), [dim_schur(l, n) for l in lam]), flush=True)
    for r in rs:
        rng = np.random.default_rng([seed, n, r])
        vecs = [rng.integers(0, p, (r, n)) for _ in range(3)]
        out = [flat_rank(n, lam, vecs, t, rng) for t in range(3)]
        print('r=%2d  ' % r + '  '.join('dir%d %d/%d' % (t, a, b) for t, (a, b) in enumerate(out)), flush=True)
