"""Koszul flattenings of isotypic tensors Y in S^{l1}V (x) S^{l2}V (x) S^{l3}V, exact mod p.
Y is recovered as a 3-way array in (over-complete) spanning-set coordinates; then for each factor A we take a random
quotient A -> C^{2p+1} and form the Koszul flattening  Lambda^p A' (x) B^* -> Lambda^{p+1} A' (x) C  (p = 1, 2).
rank / binom(2p, p) is a lower bound for the border rank of Y."""
import numpy as np, sys, time, itertools
from hwv import *
from isoflat import modrank
from specialU import chunked_F, probe3, nullspace

def iso_tensor(lam, fills, coeffs, vecs, gsA, gsB, gsC, chunk=48):
    """Y[a,b,c] = <sum_j coeffs_j Y_j, g_a v1 (x) g'_b v2 (x) g''_c v3> over the full grid."""
    nb, nc = gsB.shape[0], gsC.shape[0]
    idx = np.array(list(itertools.product(range(nb), range(nc))))
    Y = 0
    for cf, f in zip(coeffs, fills):
        Y = (Y + int(cf) * chunked_F(lam, f, vecs, (gsA, gsB[idx[:, 0]], gsC[idx[:, 1]]), chunk)) % p
    return Y.reshape(gsA.shape[0], nb, nc)

def koszul_rank(Y, factor, pk, rng):
    """Koszul flattening rank after projecting `factor` to dimension 2pk+1."""
    Y = np.moveaxis(Y, factor, 0); m = 2 * pk + 1
    M = rng.integers(0, p, (m, Y.shape[0]))
    Z = np.tensordot(M, Y, axes=([1], [0])) % p              # (m, nB, nC)
    nB, nC = Z.shape[1], Z.shape[2]
    rows = list(itertools.combinations(range(m), pk)); cols = list(itertools.combinations(range(m), pk + 1))
    K = np.zeros((len(rows) * nB, len(cols) * nC), dtype=np.int64)
    for i, I in enumerate(rows):
        for j, J in enumerate(cols):
            extra = set(J) - set(I)
            if len(extra) != 1: continue
            k = extra.pop(); sign = (-1) ** sorted(J).index(k)
            K[i * nB:(i + 1) * nB, j * nC:(j + 1) * nC] = (sign * Z[k]) % p
    return modrank(K)

def analyse(lam, n, r_low, r_high, rng, pks=(1, 2), extra=2):
    g = kronecker(*lam); dims = tuple(dim_schur(l, n) for l in lam)
    G = tuple(rng.integers(0, p, (8, n, n)) for _ in range(3))
    def rvecs(r): return tuple(rng.integers(0, p, (r, n)) for _ in range(3))
    tens = {'low': rvecs(r_low), 'low2': rvecs(r_low), 'high': rvecs(r_high)}
    fills, probes, tries = [], [], 0
    while len(fills) < g and tries < 100 * g:
        f = random_fillings(rng, lam); tries += 1
        P = probe3(lam, f, tens['high'], G)
        if np.any(P) and modrank(np.array([q.ravel() for q in probes] + [P.ravel()])) == len(fills) + 1:
            fills.append(f); probes.append(P)
    assert len(fills) == g
    coeffs = rng.integers(1, p, g)
    gsA, gsB, gsC = (rng.integers(0, p, (dims[i] + extra, n, n)) for i in range(3))
    res = {}
    for k, v in tens.items():
        Y = iso_tensor(lam, fills, coeffs, v, gsA, gsB, gsC)
        flat = [modrank(np.moveaxis(Y, f, 0).reshape(Y.shape[f], -1)) for f in range(3)]
        kz = {(f, pk): koszul_rank(Y, f, pk, rng) for f in range(3) for pk in pks}
        res[k] = (flat, kz)
    sep = [key for key in res['high'][1] if res['low'][1][key] < res['high'][1][key] and res['low2'][1][key] < res['high'][1][key]]
    return "lam=%s g=%d dims=%s | flat low/high=%s/%s | koszul (factor,p): low=%s high=%s%s" % (
        lam, g, dims, res['low'][0], res['high'][0], {k: (res['low'][1][k], res['low2'][1][k]) for k in res['low'][1]}, res['high'][1],
        "  *** KOSZUL SEPARATES %s" % sep if sep else "")

if __name__ == "__main__":
    n = int(sys.argv[1]); d = int(sys.argv[2]); rl, rh = [int(x) for x in sys.argv[3].split(',')]
    maxdim = int(sys.argv[4]) if len(sys.argv) > 4 else 10 ** 9
    lams = [eval(x) for x in sys.argv[5:]] or [l for l in itertools.combinations_with_replacement(partitions(d, n), 3)
            if kronecker(*l) >= 1 and max(dim_schur(x, n) for x in l) <= maxdim]
    rng = np.random.default_rng(41)
    for lam in lams:
        t0 = time.time()
        try: line = analyse(lam, n, rl, rh, rng)
        except Exception as ex: line = "lam=%s ERROR %r" % (lam, ex)
        print(line + " (%.0fs)" % (time.time() - t0)); sys.stdout.flush()
