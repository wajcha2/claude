"""Degree-2 isotypic flattenings of the isotypic tensor Y in A(x)B(x)C  (A=S^{l1}V etc.):
components (S2,L2,L2), (L2,S2,L2), (L2,L2,S2), (S2,S2,S2) of Y^{(x)2}, each flattened out of one factor.
E.g. (S2A)^* -> L2B (x) L2C  is  S^2 of the map A^* -> B(x)C followed by the projection S^2(B(x)C) -> L2B(x)L2C."""
import numpy as np, sys, time, itertools, os
from hwv import *
from isoflat import modrank
from koszul import iso_tensor, probe3
MAXCOLS = int(os.environ.get('MAXCOLS', '4'))   # columns sampled = MAXCOLS * rows when the full matrix is too big

def pairs(n, sym):
    return [(i, j) for i in range(n) for j in range(i if sym else i + 1, n)]

def deg2_flattening(Y, kinds, rng, full_limit=3_000_000):
    """kinds = (kA, kB, kC) in {'S','L'}; rows indexed by pairs of factor 0, columns by pairs of factors 1,2.
    entry(a a', b b', c c') = sum over the 4 products Y[a,b,c]Y[a',b',c'] with signs from the antisymmetric factors."""
    nA, nB, nC = Y.shape
    PA = pairs(nA, kinds[0] == 'S'); PB = pairs(nB, kinds[1] == 'S'); PC = pairs(nC, kinds[2] == 'S')
    rows = len(PA); ncols = len(PB) * len(PC); sampled = ncols > full_limit // max(rows, 1)
    if sampled:
        K = min(ncols, MAXCOLS * rows)
        cb = rng.integers(0, len(PB), K); cc = rng.integers(0, len(PC), K)
    else:
        cb, cc = np.repeat(np.arange(len(PB)), len(PC)), np.tile(np.arange(len(PC)), len(PB))
    PA = np.array(PA); PB = np.array(PB)[cb]; PC = np.array(PC)[cc]
    a, a2 = PA[:, 0][:, None], PA[:, 1][:, None]; b, b2 = PB[:, 0][None, :], PB[:, 1][None, :]; c, c2 = PC[:, 0][None, :], PC[:, 1][None, :]
    sB = 1 if kinds[1] == 'S' else -1; sC = 1 if kinds[2] == 'S' else -1
    M = (Y[a, b, c] * Y[a2, b2, c2] + sB * Y[a, b2, c] * Y[a2, b, c2] + sC * Y[a, b, c2] * Y[a2, b2, c] + sB * sC * Y[a, b2, c2] * Y[a2, b, c]) % p
    return modrank(M), M.shape, sampled

KINDS = [('S', 'L', 'L'), ('L', 'S', 'L'), ('L', 'L', 'S'), ('S', 'S', 'S')]

def analyse(lam, n, r_low, r_high, rng, extra=1):
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
        out = {}
        for kinds in KINDS:
            for f in range(3):
                Yf = np.moveaxis(Y, f, 0); kd = (kinds[f],) + tuple(kinds[j] for j in range(3) if j != f)
                r, shape, sampled = deg2_flattening(Yf, kd, rng)
                out[(''.join(kinds), f)] = (r, shape, sampled)
        res[k] = out
    sep = [key for key in res['high'] if res['low'][key][0] < res['high'][key][0] and res['low2'][key][0] < res['high'][key][0]]
    txt = ' '.join('%s/%d:%d,%d/%d%s' % (key[0], key[1] + 1, res['low'][key][0], res['low2'][key][0], res['high'][key][0], '*' if res['high'][key][2] else '') for key in res['high'])
    return "lam=%s g=%d dims=%s | deg2 (comp/dir: low,low2/high, *=sampled cols) %s%s" % (lam, g, dims, txt, "  *** DEG2 SEPARATES %s" % sep if sep else "")

if __name__ == "__main__":
    n = int(sys.argv[1]); d = int(sys.argv[2]); rl, rh = [int(x) for x in sys.argv[3].split(',')]
    maxdim = int(sys.argv[4]) if len(sys.argv) > 4 else 10 ** 9
    lams = [eval(x) for x in sys.argv[5:]] or [l for l in itertools.combinations_with_replacement(partitions(d, n), 3)
            if kronecker(*l) >= 1 and max(dim_schur(x, n) for x in l) <= maxdim]
    rng = np.random.default_rng(51)
    for lam in lams:
        t0 = time.time()
        try: line = analyse(lam, n, rl, rh, rng)
        except Exception as ex: line = "lam=%s ERROR %r" % (lam, ex)
        print(line + " (%.0fs)" % (time.time() - t0)); sys.stdout.flush()
