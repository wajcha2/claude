"""Codimension-2 special U: intersect the rank-drop curves of two rank-r tensors on a random plane in P(K).
Exact mod p.  Complete when the Kronecker coefficient is 3."""
import numpy as np, sympy, sys, time, itertools
from hwv import *
from isoflat import modrank
from pencil import moddet, interp, roots_mod_p
from specialU import probe3, chunked_F, nullspace
s_, t_ = sympy.symbols('s t')

def line_gcd(F0, F1, rho, rng, ntry=2):
    """monic-at-0 drop polynomial (coeff list low..high) of F0 + u F1, u the line parameter."""
    N, K = F0.shape; polys = []
    for _ in range(ntry):
        R = rng.integers(0, p, (rho, N)); S = rng.integers(0, p, (K, rho))
        xs = list(range(rho + 1)); ys = [moddet(R @ ((F0 + x * F1) % p) % p @ S % p) for x in xs]
        polys.append(sympy.Poly(list(reversed(interp(xs, ys))), s_, modulus=p))
    h = polys[0]
    for q in polys[1:]: h = h.gcd(q)
    c = [int(x) % p for x in reversed(h.all_coeffs())]   # low..high
    if c[0] == 0: return None
    inv = pow(c[0], p - 2, p); return [(x * inv) % p for x in c]

def drop_curve(Fs, rho, rng, e_extra=2):
    """Fs = (F0,F1,F2): F(s,t) = F0 + s F1 + t F2.  Returns bivariate h(s,t) (sympy Poly mod p, h(0,0)=1)
    = gcd of maximal minors, via lines through the origin."""
    F0, F1, F2 = Fs
    # degree from one random line
    v = int(rng.integers(1, p)); c0 = line_gcd(F0, (F1 + v * F2) % p, rho, rng)
    if c0 is None: return None
    e = len(c0) - 1
    if e == 0: return sympy.Poly(1, s_, t_, modulus=p)
    vs = [int(x) for x in rng.choice(p - 1, e + 1, replace=False) + 1]
    coeffs = []
    for v in vs:
        c = line_gcd(F0, (F1 + v * F2) % p, rho, rng)
        if c is None or len(c) - 1 != e: return 'degree-varies'
        coeffs.append(c)
    # h_k(1, v) = coeff of u^k on line v  -> binary form of degree k
    expr = 0
    for k in range(e + 1):
        vals = [coeffs[i][k] for i in range(k + 1)]
        ck = interp(vs[:k + 1], vals)          # h_k(1,v) = sum_j ck[j] v^j  =>  c_{k-j,j} s^{k-j} t^j
        for j in range(k + 1):
            expr += ck[j] * s_ ** (k - j) * t_ ** j
    return sympy.Poly(expr, s_, t_, modulus=p)

def analyse(lam, n, r_low, r_high, rng, direction, verbose=True):
    perm = [direction] + [k for k in range(3) if k != direction]
    lam_p = tuple(lam[k] for k in perm); g = kronecker(*lam)
    n1 = dim_schur(lam_p[0], n); N1 = K = n1 + 4
    G = tuple(rng.integers(0, p, (8, n, n)) for _ in range(3)); gs = random_gs(rng, n, N1, K)
    def rvecs(r): return tuple(rng.integers(0, p, (r, n)) for _ in range(3))
    tens = {'low1': rvecs(r_low), 'low2': rvecs(r_low), 'low3': rvecs(r_low), 'high': rvecs(r_high)}
    fills, probes, tries = [], [], 0
    while len(fills) < g and tries < 100 * g:
        f = random_fillings(rng, lam_p); tries += 1
        P = probe3(lam_p, f, tens['high'], G)
        if np.any(P) and modrank(np.array([q.ravel() for q in probes] + [P.ravel()])) == len(fills) + 1:
            fills.append(f); probes.append(P)
    assert len(fills) == g
    Fj = {k: [chunked_F(lam_p, f, tuple(v[j] for j in perm), gs, 48) for f in fills] for k, v in tens.items()}
    # random plane phi = phi0 + s phi1 + t phi2
    Phi = rng.integers(1, p, (3, g))
    Fpl = {k: [sum(int(c) * F for c, F in zip(Phi[i], Fj[k])) % p for i in range(3)] for k in tens}
    rho = {k: modrank((Fpl[k][0] + 3 * Fpl[k][1] + 7 * Fpl[k][2]) % p) for k in tens}
    t0 = time.time()
    h = {k: drop_curve(Fpl[k], rho[k], rng) for k in ('low1', 'low2')}
    info = "lam=%s dir=%d g=%d n1=%d rho low/high=%d/%d curves: %s" % (lam, direction + 1, g, n1, rho['low1'], rho['high'],
            {k: (v if isinstance(v, str) or v is None else v.total_degree()) for k, v in h.items()})
    if any(isinstance(v, str) or v is None for v in h.values()) or h['low1'].total_degree() == 0 or h['low2'].total_degree() == 0:
        return info + " | no curve"
    # common curve components (already found by the line method) are divided out
    cg = h['low1'].gcd(h['low2'])
    q1, q2 = h['low1'].quo(cg), h['low2'].quo(cg)
    info += " | common curve deg %d, residual degs %d,%d" % (cg.total_degree(), q1.total_degree(), q2.total_degree())
    pts = []
    # rational points on the common curve (its intersection with a random line t = a + b s): ranks there
    curve_pts = []
    if cg.total_degree() > 0:
        a, b = int(rng.integers(1, p)), int(rng.integers(1, p))
        hl = sympy.Poly(cg.as_expr().subs(t_, a + b * s_), s_, modulus=p)
        for s0 in roots_mod_p(hl)[:4]:
            t0v = (a + b * s0) % p
            rk = {k: modrank((Fpl[k][0] + s0 * Fpl[k][1] + t0v * Fpl[k][2]) % p) for k in tens}
            curve_pts.append(((s0, t0v), rk['low1'], rk['low2'], rk['low3'], rk['high'], "SEP" if rk['high'] > max(rk['low1'], rk['low2'], rk['low3']) else ""))
        info += " | pts on common curve (s,t,rk l1,l2,l3,high): %s" % curve_pts
    if q1.total_degree() > 0 and q2.total_degree() > 0:
        Rs = sympy.Poly(sympy.resultant(q1.as_expr(), q2.as_expr(), t_), s_, modulus=p)
        if Rs.is_zero: info += " | resultant zero"
        else:
            for s0 in roots_mod_p(Rs):
                a = sympy.Poly(q1.as_expr().subs(s_, s0), t_, modulus=p); b = sympy.Poly(q2.as_expr().subs(s_, s0), t_, modulus=p)
                gg = a.gcd(b)
                for t0v in (roots_mod_p(gg) if gg.degree() > 0 else []):
                    pts.append((s0, t0v))
    # verify candidate points on a third rank-r tensor and report ranks
    out = []
    for (s0, t0v) in pts:
        rk = {k: modrank((Fpl[k][0] + s0 * Fpl[k][1] + t0v * Fpl[k][2]) % p) for k in tens}
        if rk['low3'] < rho['low3']:
            out.append(((s0, t0v), rk['low1'], rk['low2'], rk['low3'], rk['high'], "SEP" if rk['high'] > max(rk['low1'], rk['low2'], rk['low3']) else ""))
    return info + " | candidate pts %d, T-independent pts (s,t,rk l1,l2,l3,high): %s (%.0fs)" % (len(pts), out, time.time() - t0)

if __name__ == "__main__":
    n = int(sys.argv[1]); d = int(sys.argv[2]); rl, rh = [int(x) for x in sys.argv[3].split(',')]
    gmin = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    lams = [eval(x) for x in sys.argv[5:]] or [l for l in itertools.combinations_with_replacement(partitions(d, n), 3) if kronecker(*l) >= gmin]
    rng = np.random.default_rng(31)
    for lam in lams:
        for direction in range(3):
            try: line = analyse(lam, n, rl, rh, rng, direction)
            except Exception as ex: line = "lam=%s dir=%d ERROR %r" % (lam, direction + 1, ex)
            print(line); sys.stdout.flush()
