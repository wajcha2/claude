"""
Isotypic flattenings for T in (C^3)^{⊗3}, exact arithmetic mod a prime.

For d and partitions lam=(l1,l2,l3) of d (<=3 rows) we compute isotypic tensors
    phi( iso_lam(T^{⊗d}) ) in S^{l1}V ⊗ S^{l2}V ⊗ S^{l3}V,
phi ranging over functionals on the multiplicity space M_lam=([l1]⊗[l2]⊗[l3])^{S_d},
realised as (c_{t1} ⊗ c_{t2}·s2 ⊗ c_{t3}·s3) T^{⊗d} for permutations s2,s3 in S_d
(c_t = Young symmetrizer of the canonical tableau of shape l_i).  Since T^{⊗d} is
invariant under the diagonal S_d, s1=id is no loss, and the span of these over
(s2,s3) is the full g_lam-dimensional space of isotypic tensors (dim U = 1).
"""
import numpy as np, itertools, sys, time
from itertools import permutations
from math import factorial

n = 3
p = 1000003  # prime modulus

# ---------- partitions / characters ----------
def partitions(d, maxparts=None):
    def rec(rem, maxpart, parts):
        if rem == 0:
            yield tuple(parts); return
        if maxparts is not None and len(parts) == maxparts: return
        for q in range(min(rem, maxpart), 0, -1):
            yield from rec(rem - q, q, parts + [q])
    return list(rec(d, d, []))

def dim_schur(lam, nn=None):
    nn = n if nn is None else nn
    num = 1; den = 1
    for i, r in enumerate(lam):
        for j in range(r):
            num *= (nn + j - i)
            arm = r - j - 1
            leg = sum(1 for k in range(i + 1, len(lam)) if lam[k] > j)
            den *= (arm + leg + 1)
    return num // den

from functools import lru_cache
@lru_cache(maxsize=None)
def mn_char(lam, mu):
    mu = tuple(mu)
    lam = tuple(x for x in lam if x > 0)
    if sum(lam) == 0:
        return 1
    k = mu[0]; rest = mu[1:]
    l = len(lam)
    beta = [lam[i] + l - 1 - i for i in range(l)]
    bset = set(beta)
    total = 0
    for b in beta:
        nb = b - k
        if nb < 0 or nb in bset:
            continue
        ht = sum(1 for x in beta if nb < x < b)
        newbeta = sorted([x for x in beta if x != b] + [nb], reverse=True)
        L = len(newbeta)
        newlam = tuple(newbeta[i] - (L - 1 - i) for i in range(L))
        total += (-1) ** ht * mn_char(newlam, tuple(rest))
    return total

def kronecker(l1, l2, l3):
    d = sum(l1)
    tot = 0
    for mu in partitions(d):
        z = 1
        for i in set(mu):
            m = mu.count(i)
            z *= i ** m * factorial(m)
        tot += (factorial(d) // z) * mn_char(l1, mu) * mn_char(l2, mu) * mn_char(l3, mu)
    assert tot % factorial(d) == 0
    return tot // factorial(d)

# ---------- modular linear algebra ----------
def modrank_ref(M):
    """rank of integer matrix M over F_p by plain row elimination in int64 (reference implementation, O(rank * n * m)
    numpy passes with int64 '%': hours for the 9458 x 9466 compressed stacks of the n=5, d=14 sweep)."""
    A = np.array(M, dtype=np.int64); A %= p
    if A.size == 0:
        return 0
    rows, cols = A.shape
    r = 0
    for c in range(cols):
        if r == rows: break
        piv = np.nonzero(A[r:, c])[0]
        if piv.size == 0:
            continue
        i = r + piv[0]
        if i != r:
            A[[r, i]] = A[[i, r]]
        inv = pow(int(A[r, c]), p - 2, p)
        A[r] = (A[r] * inv) % p
        others = np.nonzero(A[:, c])[0]
        others = others[others != r]
        if others.size:
            step = max(1, (1 << 23) // cols); row = A[r]
            for s in range(0, others.size, step):
                idx = others[s:s + step]
                A[idx] = (A[idx] - np.outer(A[idx, c], row)) % p
        r += 1
    return r

MODRANK_BLOCK = 256       # panel width of modrank; must stay <= 2^15 so that block * p^2 < 2^53 (exact float64 matmul)

def modrank(M, block=MODRANK_BLOCK):
    """rank of integer matrix M over F_p (M values reduced mod p; M is not modified).

    Blocked right-looking Gaussian elimination with row pivoting (LAPACK getrf style) in exact float64 arithmetic:
    the columns are processed in panels of `block` columns; within a panel the elimination is unblocked (multipliers
    stored in place, panel columns without a pivot are skipped, so rank deficiency is handled), then the trailing
    columns get the accumulated update U12 = L11^-1 A12 (forward substitution with the unit lower triangular block of
    multipliers) and A22 -= L21 @ U12 as a BLAS matmul in float64.  All entries are kept in [0, p); every product
    a * b < p^2 < 2^38 and every matmul sum has at most `block` <= 2^15 terms (< 2^53), so float64 is exact, and
    np.mod of integer-valued float64 is exact.  2026-10-06: the int64 row elimination (modrank_ref) took 8 h for the
    9458 x 9466 compressed stacks of the n=5, d=14 sweep, longer than the flattenings themselves; this takes minutes.
    Verified against modrank_ref on random, rank-deficient, structured and tiny matrices and on the C^4 sweeps."""
    assert block <= (1 << 15)
    Mi = np.asarray(M)
    if Mi.size == 0:
        return 0
    if Mi.ndim != 2:
        Mi = np.atleast_2d(Mi)
    n, m = Mi.shape
    A = np.empty((n, m), dtype=np.float64)
    rstep = max(1, (1 << 23) // m)
    for i0 in range(0, n, rstep):                      # chunked conversion: one full-size copy, not two
        A[i0:i0 + rstep] = Mi[i0:i0 + rstep].astype(np.int64) % p
    r = 0
    for c0 in range(0, m, block):
        if r == n:
            break
        c1 = min(m, c0 + block)
        piv_cols = []
        k = 0                                            # pivots found in this panel: pivot rows r .. r+k-1
        for c in range(c0, c1):
            nz = np.flatnonzero(A[r + k:, c])
            if nz.size == 0:
                continue                                 # no pivot in this column
            i = r + k + nz[0]
            if i != r + k:
                A[[r + k, i]] = A[[i, r + k]]            # whole rows: trailing columns and stored multipliers too
            inv = float(pow(int(A[r + k, c]), p - 2, p))
            below = A[r + k + 1:, c]
            if below.size:
                np.mod(below * inv, p, out=below)        # multipliers l = a * inv mod p, stored in place
                rest = A[r + k + 1:, c + 1:c1]
                if rest.size:
                    rest -= np.outer(below, A[r + k, c + 1:c1])
                    np.mod(rest, p, out=rest)
            piv_cols.append(c); k += 1
            if r + k == n:
                break
        if k == 0:
            continue
        if c1 < m:
            L = A[r:, piv_cols]                           # (n - r) x k, unit lower triangular on top (diagonal = pivots, unused)
            U12 = A[r:r + k, c1:]
            for j in range(k - 1):                       # U12 = L11^-1 A12 (forward substitution)
                U12[j + 1:] -= np.outer(L[j + 1:k, j], U12[j])
                np.mod(U12[j + 1:], p, out=U12[j + 1:])
            L21 = L[k:]
            tstep = max(1, (1 << 23) // max(1, m - c1))  # bounded temporaries for the product
            for i0 in range(0, L21.shape[0], tstep):
                T = A[r + k + i0:r + k + i0 + tstep, c1:]
                T -= L21[i0:i0 + tstep] @ U12
                np.mod(T, p, out=T)
        r += k
    return r

def independent_rows(M):
    """indices of a maximal set of independent rows of M over F_p (greedy)."""
    A = np.array(M, dtype=np.int64) % p
    chosen = []
    basis = np.zeros((0, A.shape[1]), dtype=np.int64)
    cur = 0
    for i in range(A.shape[0]):
        cand = np.vstack([basis, A[i:i + 1]])
        rk = modrank(cand)
        if rk > cur:
            chosen.append(i); basis = cand; cur = rk
    return chosen

# ---------- S_d action on V^{⊗d} ----------
def perm_sign(q):
    s = 1
    q = list(q)
    for i in range(len(q)):
        for j in range(i + 1, len(q)):
            if q[i] > q[j]:
                s = -s
    return s

_perm_cache = {}
def perm_index(sigma, d):
    """dest with M_sigma[dest[i], i] = 1, where sigma moves tensor position j to sigma(j)."""
    key = (tuple(sigma), d)
    if key in _perm_cache:
        return _perm_cache[key]
    N = n ** d
    idx = np.arange(N)
    digits = np.array(np.unravel_index(idx, (n,) * d))
    new_digits = np.empty_like(digits)
    for j in range(d):
        new_digits[sigma[j]] = digits[j]
    dest = np.ravel_multi_index(tuple(new_digits), (n,) * d)
    _perm_cache[key] = dest
    return dest

def perm_matrix(sigma, d):
    N = n ** d
    M = np.zeros((N, N), dtype=np.int64)
    M[perm_index(sigma, d), np.arange(N)] = 1
    return M

def apply_perm_cols(P, sigma, d):
    """P @ M_sigma."""
    return P[:, perm_index(sigma, d)]

def group_perms(blocks, d):
    perms_per_block = [list(permutations(b)) for b in blocks]
    for combo in itertools.product(*perms_per_block):
        sigma = list(range(d))
        for b, pb in zip(blocks, combo):
            for x, y in zip(b, pb):
                sigma[x] = y
        yield tuple(sigma)

def young_symmetrizer(shape, d):
    rows = []; c = 0
    for r in shape:
        rows.append(list(range(c, c + r))); c += r
    cols = [[row[j] for row in rows if j < len(row)] for j in range(shape[0])]
    N = n ** d
    A = np.zeros((N, N), dtype=np.int64); B = np.zeros((N, N), dtype=np.int64)
    for q in group_perms(rows, d):
        A += perm_matrix(q, d)
    for q in group_perms(cols, d):
        B += perm_sign(q) * perm_matrix(q, d)
    return A @ B

_proj_cache = {}
def schur_projector(shape, d):
    """Integer matrix P (k x N), k = dim S^shape C^3: k independent rows of c_t.
    x -> P x is injective on Im(c_t) ≅ S^shape V, and x -> P x factors through c_t."""
    key = (tuple(shape), d)
    if key in _proj_cache:
        return _proj_cache[key]
    C = young_symmetrizer(shape, d)
    rows = independent_rows(C)
    k = len(rows)
    assert k == dim_schur(shape), (shape, k, dim_schur(shape))
    P = C[rows, :] % p
    _proj_cache[key] = P
    return P

# ---------- tensors ----------
def tensor_power(T, d):
    X = np.array(T, dtype=np.int64) % p
    for m in range(1, d):
        N = n ** m
        X = (np.einsum('IJK,ijk->IiJjKk', X, T) % p).reshape(N * n, N * n, N * n)
    return X

def rank_r_tensor(rng, r):
    a = rng.integers(0, p, size=(r, n)); b = rng.integers(0, p, size=(r, n)); c = rng.integers(0, p, size=(r, n))
    T = np.zeros((n, n, n), dtype=np.int64)
    for k in range(r):
        T = (T + (np.einsum('i,j->ij', a[k], b[k]) % p)[:, :, None] * c[k][None, None, :]) % p
    return T

def general_tensor(rng):
    return rng.integers(0, p, size=(n, n, n)).astype(np.int64)

def flattenings(Y):
    n1, n2, n3 = Y.shape
    return {
        1: Y.reshape(n1, n2 * n3),
        2: np.transpose(Y, (1, 0, 2)).reshape(n2, n1 * n3),
        3: np.transpose(Y, (2, 0, 1)).reshape(n3, n1 * n2),
    }

# ---------- isotypic tensors ----------
def isotypic_tensors(X, d, lam, pairs, Z1_cache=None):
    l1, l2, l3 = lam
    P1, P2, P3 = schur_projector(l1, d), schur_projector(l2, d), schur_projector(l3, d)
    if Z1_cache is not None and l1 in Z1_cache:
        Z1 = Z1_cache[l1]
    else:
        Z1 = np.tensordot(P1, X, axes=([1], [0])) % p   # (n1, N, N)
        if Z1_cache is not None:
            Z1_cache[l1] = Z1
    out = []
    for (s2, s3) in pairs:
        P2s = apply_perm_cols(P2, s2, d)
        P3s = apply_perm_cols(P3, s3, d)
        Y = np.tensordot(Z1, P2s, axes=([1], [1])) % p   # (n1, N, n2)
        Y = np.tensordot(Y, P3s, axes=([1], [1])) % p    # (n1, n2, n3)
        out.append(Y)
    return out

def span_dim(Ys):
    return modrank(np.array([Y.ravel() for Y in Ys]))

def stacked_flattenings(Ys):
    """Flattenings of the full isotypic component (U = M_lam):
    'h': U ⊗ S^{l_i}V^* -> rest (horizontal stack), 'v': S^{l_i}V^* -> U^* ⊗ rest (vertical stack)."""
    res = {}
    for i in (1, 2, 3):
        Fs = [flattenings(Y)[i] for Y in Ys]
        res[('h', i)] = np.hstack(Fs)
        res[('v', i)] = np.vstack(Fs)
    return res
