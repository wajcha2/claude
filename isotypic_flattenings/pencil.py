"""Special one-dimensional U for components with Kronecker coefficient 2: exact pencil analysis mod p.
F(t) = F1 + t F2.  Rank-drop points for a rank-r tensor = roots of gcd of maximal minors; the
tensor-independent ones = gcd over two independent rank-r tensors."""
import numpy as np, sympy, sys, time, itertools
from hwv import *
from isoflat import modrank
t = sympy.symbols('t')

def moddet(M):
    A = np.array(M, dtype=np.int64) % p; n = A.shape[0]; det = 1
    for c in range(n):
        piv = np.nonzero(A[c:, c])[0]
        if piv.size == 0: return 0
        i = c + piv[0]
        if i != c: A[[c, i]] = A[[i, c]]; det = -det
        det = det * int(A[c, c]) % p
        inv = pow(int(A[c, c]), p - 2, p)
        A[c] = (A[c] * inv) % p
        rows = np.nonzero(A[c + 1:, c])[0] + c + 1
        if rows.size: A[rows] = (A[rows] - np.outer(A[rows, c], A[c])) % p
    return det % p

def interp(xs, ys):
    """coefficients (low..high) of the polynomial through (xs, ys) mod p."""
    m = len(xs); V = np.array([[pow(int(x), k, p) for k in range(m)] for x in xs], dtype=np.int64)
    A = np.concatenate([V, np.array(ys, dtype=np.int64).reshape(-1, 1)], axis=1) % p
    for c in range(m):
        i = c + np.nonzero(A[c:, c])[0][0]
        if i != c: A[[c, i]] = A[[i, c]]
        A[c] = (A[c] * pow(int(A[c, c]), p - 2, p)) % p
        rows = np.nonzero(A[:, c])[0]; rows = rows[rows != c]
        if rows.size: A[rows] = (A[rows] - np.outer(A[rows, c], A[c])) % p
    return [int(v) for v in A[:, m]]

def minor_poly(F1, F2, rho, rng):
    N, K = F1.shape
    R = rng.integers(0, p, (rho, N)); S = rng.integers(0, p, (K, rho))
    xs = list(range(rho + 1))
    ys = [moddet(R @ ((F1 + x * F2) % p) % p @ S % p) for x in xs]
    return sympy.Poly(list(reversed(interp(xs, ys))), t, modulus=p)

def drop_poly(F1, F2, rho, rng):
    q1 = minor_poly(F1, F2, rho, rng); q2 = minor_poly(F1, F2, rho, rng)
    return q1.gcd(q2)

def roots_mod_p(h):
    x = h.gens[0]
    fl = sympy.factor_list(h.as_expr(), x, modulus=p)[1]
    out = []
    for f, mult in fl:
        f = sympy.Poly(f, x, modulus=p)
        if f.degree() == 1:
            a, b = [int(c) for c in f.all_coeffs()]
            out.append((-b * pow(a, p - 2, p)) % p)
    return out

def analyse(lam, n, r_low, r_high, rng, direction=0, verbose=True):
    perm = [direction] + [k for k in range(3) if k != direction]
    lam_p = tuple(lam[k] for k in perm)
    n1 = dim_schur(lam_p[0], n); N1 = n1 + 4; K = n1 + 4
    gs = random_gs(rng, n, N1, K)
    tens = {'low1': r_low, 'low2': r_low, 'high': r_high}
    vecs = {k: tuple(rng.integers(0, p, (r, n)) for _ in range(3)) for k, r in tens.items()}
    # g fillings giving independent functionals (checked on the high-rank tensor), then a random line
    g = kronecker(*lam); fills = []; tries = 0
    while len(fills) < g and tries < 100 * g:
        f = random_fillings(rng, lam_p); tries += 1
        F = flattening_matrix(lam_p, f, tuple(vecs['high'][k] for k in perm), gs)
        if np.any(F) and modrank(np.array([x[1].ravel() for x in fills] + [F.ravel()])) == len(fills) + 1:
            fills.append((f, F))
    assert len(fills) == g, "could not span multiplicity space"
    ca, cb = rng.integers(1, p, g), rng.integers(1, p, g)
    Fs = {}
    for k in tens:
        Fj = [flattening_matrix(lam_p, f, tuple(vecs[k][j] for j in perm), gs) for f, _ in fills]
        Fs[k] = [sum(int(c) * F for c, F in zip(ca, Fj)) % p, sum(int(c) * F for c, F in zip(cb, Fj)) % p]
    tr = int(rng.integers(1, p))
    rho = {k: modrank((Fs[k][0] + tr * Fs[k][1]) % p) for k in tens}
    h = {k: drop_poly(Fs[k][0], Fs[k][1], rho[k], rng) for k in ('low1', 'low2')}
    hc = h['low1'].gcd(h['low2'])
    roots = roots_mod_p(hc) if hc.degree() > 0 else []
    special = []
    for t0 in roots + ['inf']:
        rk = {k: modrank(Fs[k][1] if t0 == 'inf' else (Fs[k][0] + t0 * Fs[k][1]) % p) for k in tens}
        special.append((t0, rk['low1'], rk['low2'], rk['high']))
    if verbose:
        print("lam=%s dir=%d n1=%d generic ranks low/high=%d/%d | drop-poly degrees: T1=%d T2=%d common=%d | points (t, rk low1, low2, high): %s" % (
            lam, direction + 1, n1, rho['low1'], rho['high'], h['low1'].degree(), h['low2'].degree(), hc.degree(), special)); sys.stdout.flush()
    return rho, hc.degree(), special

if __name__ == "__main__":
    n = int(sys.argv[1]); d = int(sys.argv[2]); rl, rh = [int(x) for x in sys.argv[3].split(',')]
    lams = [eval(x) for x in sys.argv[4:]] or [l for l in itertools.combinations_with_replacement(partitions(d, n), 3) if kronecker(*l) >= 2]
    rng = np.random.default_rng(9)
    for lam in lams:
        for direction in range(3):
            t0 = time.time(); analyse(lam, n, rl, rh, rng, direction)
