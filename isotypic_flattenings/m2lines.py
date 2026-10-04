"""python3 m2lines.py "lam" dirn [nlines]     (or LIST jobfile [nlines [worker nworkers]])
Special 1-dim U (points phi of P(M^*)) where general rank-6 tensors drop rank, and M2 there.
Along a line phi(t) = a + t b in M^* (for g = 2 the whole P^1: a, b = basis; else random a, b) the flattening is the
pencil A_T + t B_T (sampled N1 x K).  For each tensor T the rank-drop points are the roots of
   h_T(t) = gcd of two random projected rho x rho minors det(R (A + tB) S),  rho = generic rank of T on the line,
computed exactly via characteristic polynomials.  Points that matter for a GENERAL rank-6 tensor are roots of
hc = gcd(h_{R6a}, h_{R6b}) (a drop point of one rank-6 tensor that is not shared by another is tensor-dependent).
Every irreducible factor q of hc over F_p is evaluated at its root (over F_{p^e}, e = deg q <= EMAX, by the companion
matrix trick: rank over F_{p^e} = rank_Fp(A (x) I + B (x) C_q) / e), together with t = infinity.
Printed per root: ranks of R6a, R6b, R7, M2; SEP if rank6 < rank7, WIN if rank M2 > rank 6."""
import sys, os, time, numpy as np, sympy
import m2lib
from m2lib import p, dim_schur, kronecker, random_gs, frank, combine, choose_fillings, rand_tensor, m2_terms
import flatlib
EMAX = int(os.environ.get('EMAX', '4'))
X = sympy.symbols('x')

def fsolve(A, B):
    """A^{-1} B mod p (A square invertible), Gauss-Jordan on [A | B] in float64."""
    n = A.shape[0]
    M = np.fmod(np.hstack([A, B]).astype(np.float64), p)
    for c in range(n):
        nz = np.flatnonzero(M[c:, c])
        if nz.size == 0: raise ZeroDivisionError
        i = c + nz[0]
        if i != c: M[[c, i]] = M[[i, c]]
        M[c] = np.fmod(M[c] * float(pow(int(M[c, c]), p - 2, p)), p)
        rows = np.flatnonzero(M[:, c]); rows = rows[rows != c]
        if rows.size:
            M[rows] = np.fmod(M[rows] - np.fmod(np.outer(M[rows, c], M[c]), p) + p, p)
    return M[:, n:]

def fdet(A):
    n = A.shape[0]; M = np.fmod(A.astype(np.float64), p); det = 1
    for c in range(n):
        nz = np.flatnonzero(M[c:, c])
        if nz.size == 0: return 0
        i = c + nz[0]
        if i != c: M[[c, i]] = M[[i, c]]; det = -det
        det = det * int(M[c, c]) % p
        inv = float(pow(int(M[c, c]), p - 2, p))
        rows = c + 1 + np.flatnonzero(M[c + 1:, c])
        if rows.size:
            mult = np.fmod(M[rows, c] * inv, p)
            M[rows, c:] = np.fmod(M[rows, c:] - np.fmod(np.outer(mult, M[c, c:]), p) + p, p)
    return det % p

def charpoly(N):
    """coefficients c_0..c_n (low to high) of det(x I - N) mod p: Hessenberg reduction + recurrence."""
    H = np.fmod(N.astype(np.float64), p); n = H.shape[0]
    for m in range(1, n - 1):
        nz = np.flatnonzero(H[m:, m - 1])
        if nz.size == 0: continue
        i = m + nz[0]
        if i != m:
            H[[m, i]] = H[[i, m]]; H[:, [m, i]] = H[:, [i, m]]
        inv = float(pow(int(H[m, m - 1]), p - 2, p))
        rows = m + 1 + np.flatnonzero(H[m + 1:, m - 1])
        if rows.size:
            u = np.fmod(H[rows, m - 1] * inv, p)                      # row_r -= u_r row_m ; col_m += sum u_r col_r
            H[rows, :] = np.fmod(H[rows, :] - np.fmod(np.outer(u, H[m, :]), p) + p, p)
            H[:, m] = np.fmod(H[:, m] + np.fmod(H[:, rows] @ u, p), p)
    # recurrence: P_0 = 1, P_k = (x - h_kk) P_{k-1} - sum_{i<k} h_ik prod_{j=i+1}^{k} h_{j,j-1} P_{i-1}
    Hi = H.astype(np.int64)
    P = [np.array([1], dtype=object)]
    for k in range(1, n + 1):
        kk = k - 1
        cur = np.zeros(k + 1, dtype=object)
        cur[1:] += P[k - 1]; cur[:k] -= int(Hi[kk, kk]) * P[k - 1]
        prod = 1
        for i in range(k - 1, 0, -1):             # i = row index (1-based) of h_{i,k}
            prod = prod * int(Hi[i, i - 1]) % p   # h_{i+1, i} in 1-based = Hi[i, i-1]
            if prod == 0: break
            hik = int(Hi[i - 1, kk])
            if hik:
                cur[:i] -= (hik * prod % p) * P[i - 1]
        P.append(np.array([int(c) % p for c in cur], dtype=object))
    return [int(c) for c in P[n]]

def drop_poly(A, B, rho, rng):
    """gcd of two random projected rho x rho minors of A + tB, as a sympy Poly in x mod p (None if identically 0)."""
    polys = []
    for _ in range(2):
        R = rng.integers(0, p, (rho, A.shape[0])); S = rng.integers(0, p, (A.shape[1], rho))
        RA = m2lib.hwv_fast.matmul_mod(m2lib.hwv_fast.matmul_mod(R[None], A[None]), S[None])[0]
        RB = m2lib.hwv_fast.matmul_mod(m2lib.hwv_fast.matmul_mod(R[None], B[None]), S[None])[0]
        t1 = int(rng.integers(1, p))
        Ap = (RA + t1 * RB) % p                      # A + tB = Ap + u B, u = t - t1
        dA = fdet(Ap)
        if dA == 0: raise ZeroDivisionError('shifted minor singular')
        N = fsolve(Ap, RB)                           # det(Ap + u RB) = det(Ap) det(I + u N)
        c = charpoly(N)                              # det(xI - N) = sum c_k x^k ; det(I + uN) = sum_k (-1)^k c_{n-k} u^k
        n = len(c) - 1
        coeffs_u = [((-1) ** k * c[n - k]) % p for k in range(n + 1)]
        pu = sympy.Poly(list(reversed(coeffs_u)), X, modulus=p)
        pt = sympy.Poly(pu.as_expr().subs(X, X - t1), X, modulus=p)          # u = t - t1
        polys.append(pt * dA)
    h = polys[0].gcd(polys[1])
    return h

def rank_at_root(A, B, q):
    """rank over F_{p^e} of A + t0 B, t0 a root of the irreducible monic q of degree e."""
    e = q.degree()
    if e == 1:
        a, b = [int(c) % p for c in q.all_coeffs()]
        t0 = (-b * pow(a, p - 2, p)) % p
        return frank((A + t0 * B) % p), t0
    c = [int(x) % p for x in reversed(q.monic().all_coeffs())]   # c_0..c_e (c_e = 1)
    Cq = np.zeros((e, e), dtype=np.int64)
    for i in range(1, e): Cq[i, i - 1] = 1
    Cq[:, e - 1] = [(-x) % p for x in c[:e]]
    big = (np.kron(A, np.eye(e, dtype=np.int64)) + np.kron(B, Cq) % p) % p
    r = frank(big)
    assert r % e == 0
    return r // e, 'deg%d' % e

def run(lam, dirn, nlines=1, seed=None):
    seed = int(os.environ.get('SEED', '13')) if seed is None else seed
    rng = np.random.default_rng([seed] + [x for l in lam for x in l] + [dirn])
    perm = [dirn] + [t for t in range(3) if t != dirn]
    lam_p = tuple(lam[t] for t in perm)
    g = kronecker(*lam)
    n1 = dim_schur(lam_p[0], 4); n23 = dim_schur(lam_p[1], 4) * dim_schur(lam_p[2], 4)
    N1 = min(n1, n23) + 8; K = min(n1, n23) + 8
    t0 = time.time()
    tens = {'R6a': rand_tensor(rng, 6), 'R6b': rand_tensor(rng, 6), 'R7': rand_tensor(rng, 7), 'M2': m2_terms('strassen')}
    tens = {k: tuple(v[t] for t in perm) for k, v in tens.items()}
    fills = choose_fillings(lam_p, g, tens['R7'], rng)
    gs = random_gs(rng, 4, N1, K)
    F = {k: [flatlib.flat(f, v, gs) % p for f in fills] for k, v in tens.items()}
    out = []
    for li in range(nlines if g > 2 else 1):
        if g == 2:
            ca, cb = np.array([1, 0]), np.array([0, 1])
        else:
            ca, cb = rng.integers(0, p, g), rng.integers(0, p, g)
        AB = {k: (combine(F[k], ca), combine(F[k], cb)) for k in tens}
        tr = int(rng.integers(1, p))
        rho = {k: frank((AB[k][0] + tr * AB[k][1]) % p) for k in tens}
        hs = {k: drop_poly(*AB[k], rho[k], rng) for k in ('R6a', 'R6b')}
        hc = hs['R6a'].gcd(hs['R6b'])
        pts = []
        facs = sympy.factor_list(hc.as_expr(), X, modulus=p)[1] if hc.degree() > 0 else []
        for fq, mult in facs:
            q = sympy.Poly(fq, X, modulus=p)
            if q.degree() > EMAX:
                pts.append(('deg%d-skipped' % q.degree(), mult, None)); continue
            rk = {}; lab = None
            for k in tens:
                rk[k], lab = rank_at_root(*AB[k], q)
            pts.append((lab, mult, rk))
        rk = {k: frank(AB[k][1]) for k in tens}
        pts.append(('inf', 0, rk))
        desc = []
        flags = set()
        for lab, mult, rk in pts:
            if rk is None:
                desc.append('%s(x%d)' % (lab, mult)); flags.add('SKIPPED'); continue
            r6 = max(rk['R6a'], rk['R6b'])
            s = '%s(x%d):%d,%d/%d/M2=%d' % (lab, mult, rk['R6a'], rk['R6b'], rk['R7'], rk['M2'])
            if r6 < rk['R7']: s += '!'; flags.add('SEP')
            if rk['M2'] > r6: s += '!!!'; flags.add('WIN')
            desc.append(s)
        line = 'lam=%s dir%d g=%d n1=%d n23=%d line%d generic(R6a,R6b,R7,M2)=%d,%d,%d,%d deg h(R6a,R6b,common)=%d,%d,%d | %s | %s (%.0fs)' % (
            lam, dirn + 1, g, n1, n23, li, rho['R6a'], rho['R6b'], rho['R7'], rho['M2'], hs['R6a'].degree(), hs['R6b'].degree(),
            hc.degree(), ' '.join(desc), ' '.join(sorted(flags)) or '-', time.time() - t0)
        print(line); sys.stdout.flush()
        out.append(line)
    return out

if __name__ == '__main__':
    if sys.argv[1] == 'LIST':
        jobs = [l.split('|')[0].strip() for l in open(sys.argv[2]) if l.strip() and not l.startswith('#')]
        nl = int(sys.argv[3]) if len(sys.argv) > 3 else 1
        W, NW = (int(sys.argv[4]), int(sys.argv[5])) if len(sys.argv) > 5 else (0, 1)
        for i, j in enumerate(jobs):
            if i % NW != W: continue
            lam_s, dirn_s = j.rsplit(' ', 1)
            try:
                run(eval(lam_s), int(dirn_s), nl)
            except Exception as e:
                import traceback; traceback.print_exc()
                print('lam=%s dir%d ERROR %r' % (eval(lam_s), int(dirn_s) + 1, e)); sys.stdout.flush()
    else:
        run(eval(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 1)
