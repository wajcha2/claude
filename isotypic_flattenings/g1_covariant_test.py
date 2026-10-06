"""Does the closed-form covariant G1(X, Y) = (Y adj X)_0 (x) (adj X Y)_0 (X = T(alpha), Y = T(beta) the A-slices) separate?
Flattening S^{62}A^* -> sl(B) (x) sl(C): rows = source points (alpha, beta), entries = G1 (256 coordinates of gl (x) gl)."""
import sys, numpy as np
p = 524287
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
inv4 = pow(4, p - 2, p)
def det_inv(X):
    """det and inverse of a 4x4 matrix mod p (Gauss-Jordan)."""
    A = np.concatenate([X % p, np.eye(4, dtype=np.int64)], 1); d = 1
    for c in range(4):
        piv = [i for i in range(c, 4) if A[i, c]]
        if not piv: return 0, None
        i = piv[0]
        if i != c: A[[c, i]] = A[[i, c]]; d = -d
        d = d * int(A[c, c]) % p; A[c] = A[c] * pow(int(A[c, c]), p - 2, p) % p
        for r in range(4):
            if r != c and A[r, c]: A[r] = (A[r] - A[r, c] * A[c]) % p
    return d % p, A[:, 4:]
def traceless(U):
    return (U - (int(np.trace(U)) * inv4 % p) * np.eye(4, dtype=np.int64)) % p
def G1(X, Y):
    d, Xi = det_inv(X); adj = (d * Xi) % p
    U = traceless(Y @ adj % p); W = traceless(adj @ Y % p)
    return np.einsum('ab,cd->abcd', U, W).reshape(-1) % p
def rank(M):
    A = np.array(M, dtype=np.int64) % p; r = 0; m, n = A.shape
    for c in range(n):
        if r == m: break
        nz = np.nonzero(A[r:, c])[0]
        if nz.size == 0: continue
        i = r + nz[0]
        if i != r: A[[r, i]] = A[[i, r]]
        A[r] = A[r] * pow(int(A[r, c]), p - 2, p) % p
        rows = np.nonzero(A[:, c])[0]; rows = rows[rows != r]
        if rows.size: A[rows] = (A[rows] - np.outer(A[rows, c], A[r]) % p) % p
        r += 1
    return r
def flat(T, N1=420):
    a, b, c = T
    slices = lambda al: np.einsum('i,ij,ik->jk', (a @ al) % p, b, c) % p     # sum_i <al, a_i> b_i c_i^T
    rows = []
    for _ in range(N1):
        al, be = rng.integers(0, p, 4), rng.integers(0, p, 4)
        rows.append(G1(slices(al), slices(be)))
    return rank(np.array(rows))
for r in (4, 5, 6, 6, 7, 7, 8):
    T = tuple(rng.integers(0, p, (r, 4)) for _ in range(3))
    print('random rank-%d tensor: rank of the G1 flattening = %d' % (r, flat(T))); sys.stdout.flush()
