import isoflat
from isoflat import *
import sympy

CASES = [((3, 2), (3, 1, 1), (3, 1, 1)), ((3, 2), (3, 1, 1), (2, 2, 1)), ((3, 1, 1), (2, 2, 1), (2, 2, 1))]
d = 5

# (a) different prime, fresh tensors, 4 instances each, several functionals
isoflat.p = 999983; isoflat._proj_cache.clear()
rng = np.random.default_rng(2024)
gens = [general_tensor(rng) for _ in range(4)]
rk4s = [rank_r_tensor(rng, 4) for _ in range(4)]
Xg = [tensor_power(T, d) for T in gens]; X4 = [tensor_power(T, d) for T in rk4s]
pairs = [(tuple(rng.permutation(d)), tuple(rng.permutation(d))) for _ in range(6)]
coeffs = rng.integers(1, isoflat.p, size=len(pairs))
print("(a) p = %d, fresh tensors; ranks of flattening S^{lam1}V^* -> S^{lam2}V (x) S^{lam3}V, generic functional" % isoflat.p)
for lam in CASES:
    def r1(X):
        Ys = isotypic_tensors(X, d, lam, pairs)
        Y = sum(int(c) * Yj for c, Yj in zip(coeffs, Ys)) % isoflat.p
        return modrank(flattenings(Y)[1])
    print("  lam=%s  general: %s   rank-4: %s" % (lam, [r1(X) for X in Xg], [r1(X) for X in X4]))

# (b) exact rational arithmetic: small integer tensors, float64 is exact here (|entries| < 2^53), sympy rank over Q
print("(b) exact rank over Q (sympy) for one small-integer instance")
def exact_projector(shape):
    C = young_symmetrizer(shape, d)                # exact integers
    rows = independent_rows(C)
    return C[rows, :].astype(np.float64)
def exact_iso(T, lam, s2, s3):
    X = T.astype(np.float64)
    for m in range(1, d):
        N = n ** m
        X = np.einsum('IJK,ijk->IiJjKk', X, T.astype(np.float64)).reshape(N * n, N * n, N * n)
    P1, P2, P3 = (exact_projector(l) for l in lam)
    Z = np.tensordot(P1, X, axes=([1], [0]))
    Z = np.tensordot(Z, apply_perm_cols(P2, s2, d), axes=([1], [1]))
    Z = np.tensordot(Z, apply_perm_cols(P3, s3, d), axes=([1], [1]))
    assert np.all(np.abs(Z) < 2 ** 52)
    return Z
rng2 = np.random.default_rng(7)
Tg = rng2.integers(-2, 3, size=(3, 3, 3)).astype(np.int64)
a, b, c = (rng2.integers(-2, 3, size=(4, 3)) for _ in range(3))
T4 = sum(np.einsum('i,j,k->ijk', a[k], b[k], c[k]) for k in range(4)).astype(np.int64)
s2, s3 = tuple(rng2.permutation(d)), tuple(rng2.permutation(d))
for lam in CASES:
    out = []
    for T in (Tg, T4):
        Y = exact_iso(T, lam, s2, s3)
        F = flattenings(Y)[1]
        M = sympy.Matrix([[int(round(v)) for v in row] for row in F])
        out.append((M.shape, M.rank()))
    print("  lam=%s  general: %s  rank-4: %s" % (lam, out[0], out[1]))
print("rank-4 witness: a=%s b=%s c=%s" % (a.tolist(), b.tolist(), c.tolist()))
print("general witness T =", Tg.tolist())
