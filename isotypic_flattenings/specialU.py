"""Natural special subspaces U of the multiplicity space, tested exactly mod p.
 U_k = {phi : phi(iso_lam T^{(x)d}) = 0 for all T of rank <= k}  (k = 1..6),
 eigenspaces of factor-swap symmetries when partitions repeat.
usage: python3 specialU.py n d r_low,r_high [lam ...]"""
import numpy as np, sys, time, itertools
from hwv import *
from isoflat import modrank
PR = 8  # probe size

def nullspace(M):
    """basis (rows) of {x : M x = 0} over F_p; M shape (m, g)."""
    A = np.array(M, dtype=np.int64) % p; m, g = A.shape; piv = []; r = 0
    for c in range(g):
        if r == m: break
        nz = np.nonzero(A[r:, c])[0]
        if nz.size == 0: continue
        i = r + nz[0]
        if i != r: A[[r, i]] = A[[i, r]]
        A[r] = (A[r] * pow(int(A[r, c]), p - 2, p)) % p
        rows = np.nonzero(A[:, c])[0]; rows = rows[rows != r]
        if rows.size: A[rows] = (A[rows] - np.outer(A[rows, c], A[r])) % p
        piv.append(c); r += 1
    free = [c for c in range(g) if c not in piv]
    out = []
    for f in free:
        x = np.zeros(g, dtype=np.int64); x[f] = 1
        for i, c in enumerate(piv): x[c] = (-A[i, f]) % p
        out.append(x)
    return np.array(out, dtype=np.int64).reshape(len(out), g)

def probe3(lam, fill, vecs, G):
    """P[a,b,c] = <Y, g_a v1 (x) g'_b v2 (x) g''_c v3>, a,b,c < PR."""
    idx = np.array(list(itertools.product(range(PR), range(PR))))
    F = flattening_matrix(lam, fill, vecs, (G[0], G[1][idx[:, 0]], G[2][idx[:, 1]]))
    return F.reshape(PR, PR, PR)

def chunked_F(lam, fill, vecs, gs, chunk=200):
    K = gs[1].shape[0]
    return np.hstack([flattening_matrix(lam, fill, vecs, (gs[0], gs[1][i:i + chunk], gs[2][i:i + chunk])) for i in range(0, K, chunk)])

def analyse(lam, n, r_low, r_high, rng, direction):
    perm = [direction] + [k for k in range(3) if k != direction]
    lam_p = tuple(lam[k] for k in perm); g = kronecker(*lam)
    d = sum(lam[0]); n1, n2, n3 = (dim_schur(l, n) for l in lam_p)
    G = tuple(rng.integers(0, p, (PR, n, n)) for _ in range(3))
    def rvecs(r): return tuple(rng.integers(0, p, (r, n)) for _ in range(3))
    high = rvecs(r_high)
    # basis of functionals via independent fillings (independence checked on probes of the high tensor)
    fills, probes, tries = [], [], 0
    while len(fills) < g and tries < 100 * g:
        f = random_fillings(rng, lam_p); tries += 1
        P = probe3(lam_p, f, high, G)
        if np.any(P) and modrank(np.array([q.ravel() for q in probes] + [P.ravel()])) == len(fills) + 1:
            fills.append(f); probes.append(P)
    assert len(fills) == g
    # flag U_k
    cands = {}
    for k in range(1, r_low + 1):
        rows = []
        for _ in range(2):
            v = rvecs(k); rows.append(np.array([probe3(lam_p, f, v, G).ravel() for f in fills]).T)
        Uk = nullspace(np.vstack(rows))
        if len(Uk): cands['U%d' % k] = Uk
    # swap symmetries
    names = {(1, 2): 'swap12', (0, 2): 'swap13', (0, 1): 'swap12'}  # in permuted positions
    for (i, j) in [(1, 2), (0, 1), (0, 2)]:
        if lam_p[i] != lam_p[j]: continue
        pm = [0, 1, 2]; pm[i], pm[j] = pm[j], pm[i]
        # matrix of tau on the functional basis: probe of filling with factors i,j swapped
        cols = []
        for f in fills:
            Pt = probe3(tuple(lam_p[t] for t in pm), [f[t] for t in pm], tuple(high[t] for t in pm), tuple(G[t] for t in pm))
            Pt = np.transpose(Pt, pm)  # back to (a,b,c) order
            sol = nullspace(np.array([q.ravel() for q in probes] + [Pt.ravel()]).T)
            assert len(sol) == 1 and sol[0][-1] != 0
            s = sol[0]; inv = pow(int((-s[-1]) % p), p - 2, p); cols.append((s[:-1] * inv) % p)
        Tau = np.array(cols).T % p   # Tau[:, j] = coordinates of phi_j o tau
        for sign, nm in ((1, '+'), (p - 1, '-')):
            E = nullspace((Tau - sign * np.eye(g, dtype=np.int64)) % p)
            if len(E): cands['sw%d%d%s' % (i + 1, j + 1, nm)] = E
    if not cands:
        return "lam=%s dir=%d g=%d: no natural special U" % (lam, direction + 1, g)
    # big matrices for the rank tests
    kmax = max(len(U) for U in cands.values())
    N1 = n1 + 4; K = min(kmax * n1, n2 * n3) + 4
    gs = random_gs(rng, n, N1, K)
    tens = {'low': rvecs(r_low), 'low2': rvecs(r_low), 'high': high}
    Fs = {t: [chunked_F(lam_p, f, tuple(v[k] for k in perm), gs) for f in fills] for t, v in tens.items()}
    out = []
    for name, U in cands.items():
        res = {}
        coeff = rng.integers(1, p, len(U)); phi = (coeff @ U) % p
        for t in tens:
            Fphi = sum(int(c) * F for c, F in zip(phi, Fs[t])) % p
            res[t] = [modrank(Fphi)]
            if len(U) > 1:
                blocks = [sum(int(c) * F for c, F in zip(u, Fs[t])) % p for u in U]
                res[t] += [modrank(np.hstack(blocks)), modrank(np.vstack(blocks))]
        sep = any(res['low'][i] < res['high'][i] and res['low2'][i] < res['high'][i] for i in range(len(res['low'])))
        out.append("%s(dim%d): low=%s low2=%s high=%s%s" % (name, len(U), res['low'], res['low2'], res['high'], "  *** SEPARATES" if sep else ""))
    return "lam=%s dir=%d g=%d n=(%d,%d,%d) | " % (lam, direction + 1, g, n1, n2, n3) + " ; ".join(out)

if __name__ == "__main__":
    n = int(sys.argv[1]); d = int(sys.argv[2]); rl, rh = [int(x) for x in sys.argv[3].split(',')]
    lams = [eval(x) for x in sys.argv[4:]] or [l for l in itertools.combinations_with_replacement(partitions(d, n), 3) if kronecker(*l) >= 1]
    rng = np.random.default_rng(21)
    for lam in lams:
        for direction in range(3):
            t0 = time.time()
            try:
                line = analyse(lam, n, rl, rh, rng, direction)
            except AssertionError as e:
                line = "lam=%s dir=%d FAILED %s" % (lam, direction + 1, e)
            print(line + "  (%.0fs)" % (time.time() - t0)); sys.stdout.flush()
