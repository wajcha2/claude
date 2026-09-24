import isoflat
from isoflat import *
import sympy

CASES = [((3, 2), (3, 1, 1), (3, 1, 1)), ((3, 2), (3, 1, 1), (2, 2, 1)), ((3, 1, 1), (2, 2, 1), (2, 2, 1))]
d = 5
rng = np.random.default_rng(11)

def exact_projector(shape):
    C = young_symmetrizer(shape, d)
    rows = independent_rows(C)
    return C[rows, :].astype(np.float64), C[rows, :] % isoflat.p

def tpow_float(T):
    X = T.astype(np.float64)
    for m in range(1, d):
        N = n ** m
        X = np.einsum('IJK,ijk->IiJjKk', X, T.astype(np.float64)).reshape(N * n, N * n, N * n)
    return X

def iso_both(T, lam, s2, s3):
    """exact float64 (asserted < 2^52) and mod-p versions; returns exact integer Y after cross-check."""
    Xf = tpow_float(T); Xm = tensor_power(T % isoflat.p, d)
    Pf = [exact_projector(l) for l in lam]
    Z = np.tensordot(Pf[0][0], Xf, axes=([1], [0]))
    Z = np.tensordot(Z, apply_perm_cols(Pf[1][0], s2, d), axes=([1], [1]))
    Z = np.tensordot(Z, apply_perm_cols(Pf[2][0], s3, d), axes=([1], [1]))
    assert np.all(np.abs(Z) < 2 ** 52), np.abs(Z).max()
    Zm = np.tensordot(Pf[0][1], Xm, axes=([1], [0])) % isoflat.p
    Zm = np.tensordot(Zm, apply_perm_cols(Pf[1][1], s2, d), axes=([1], [1])) % isoflat.p
    Zm = np.tensordot(Zm, apply_perm_cols(Pf[2][1], s3, d), axes=([1], [1])) % isoflat.p
    Zi = np.rint(Z).astype(np.int64)
    assert np.array_equal(Zi % isoflat.p, Zm), "float/modular mismatch"
    return Zi

# witnesses with small entries (so float64 is exact), no zero vectors
Tg = rng.integers(-2, 3, size=(3, 3, 3)).astype(np.int64)
while True:
    a, b, c = (rng.integers(-2, 3, size=(4, 3)) for _ in range(3))
    if all(np.any(v != 0) for v in list(a) + list(b) + list(c)):
        break
T4 = sum(np.einsum('i,j,k->ijk', a[k], b[k], c[k]) for k in range(4)).astype(np.int64)
print("general witness T =", Tg.tolist())
print("rank-4 witness: a=%s b=%s c=%s" % (a.tolist(), b.tolist(), c.tolist()))
print("classical flattening ranks of T4 (should be 3,3,3):", [modrank(F) for F in flattenings(T4).values()])

for lam in CASES:
    # pick a permutation pair whose functional is nonzero on the general witness
    for _ in range(50):
        s2, s3 = tuple(int(x) for x in rng.permutation(d)), tuple(int(x) for x in rng.permutation(d))
        Yg = iso_both(Tg, lam, s2, s3)
        if np.any(Yg != 0):
            break
    Y4 = iso_both(T4, lam, s2, s3)
    out = []
    for Y in (Yg, Y4):
        F = flattenings(Y)[1]
        M = sympy.Matrix(F.tolist())
        out.append(M.rank())
    print("lam=%s pair s2=%s s3=%s  matrix %s  rank over Q: general=%d  rank-4=%d" % (
        lam, s2, s3, flattenings(Yg)[1].shape, out[0], out[1]))
