"""python3 m2deep.py LIST jobfile [worker nworkers]   -- structure of the V-stack kernels K(T) for R6a, R6b, R7 (and dim K(M2)).
Verdict STRUCT: K(T) = phi_0 (x) W_T for all three tensors with the same phi_0 and dim W_{R6} = dim W_{R7}.  Then for every U
(1-dim, H- or V-stack) rank_U(R6) = rank_U(R7) (the kernel meets U (x) X1^* iff phi_0 in U, in phi_0 (x) W_T), so no U separates
and none gives rank(M2) > rank(R6).  Otherwise DEEP (needs a closer look).  Coordinates as in m2kappa.py."""
import sys, os, re, numpy as np
import m2lib
from m2lib import p, dim_schur, kronecker, random_gs, frank, choose_fillings, rand_tensor, m2_terms, compress_cols
from specialU import nullspace

def kernel_mats(Fs, g, n1, rng):
    V = np.vstack(Fs)
    Kb = nullspace(compress_cols(V, V.shape[0] + 8, rng).T % p)
    return [np.array(k, dtype=np.int64).reshape(g, n1) for k in Kb]

def run(lam, dirn, seed=29):
    rng = np.random.default_rng([seed] + [x for l in lam for x in l] + [dirn])
    perm = [dirn] + [t for t in range(3) if t != dirn]
    lam_p = tuple(lam[t] for t in perm); g = kronecker(*lam)
    n1 = dim_schur(lam_p[0], 4); n23 = dim_schur(lam_p[1], 4) * dim_schur(lam_p[2], 4)
    tens = {'R6a': rand_tensor(rng, 6), 'R6b': rand_tensor(rng, 6), 'R7': rand_tensor(rng, 7), 'M2': m2_terms('strassen')}
    tens = {k: tuple(v[t] for t in perm) for k, v in tens.items()}
    fills = choose_fillings(lam_p, g, tens['R7'], rng)
    K = min(g * n1, n23) + 8
    for _ in range(5):
        gs = random_gs(rng, 4, n1, K)
        pre7 = m2lib.prep_all(tens['R7'], gs)
        F7 = [m2lib.flat_pre(f, pre7) % p for f in fills]
        if frank(np.hstack(F7)) == n1: break
    else:
        print('lam=%s dir%d source points dependent' % (lam, dirn + 1)); return
    info, sup, dims, FF = [], {}, {}, {}
    for name, v in tens.items():
        Fs = F7 if name == 'R7' else [m2lib.flat_pre(f, m2lib.prep_all(v, gs)) % p for f in fills]
        FF[name] = Fs
        mats = kernel_mats(Fs, g, n1, rng)
        dims[name] = len(mats)
        if name == 'M2':
            info.append('M2:dimK=%d' % len(mats)); continue
        S = np.hstack(mats) if mats else np.zeros((g, 0), dtype=np.int64)
        sup[name] = S
        info.append('%s:dimK=%d,supp=%d' % (name, len(mats), frank(S) if mats else 0))
    s6 = frank(np.hstack([sup['R6a'], sup['R6b']])) if dims['R6a'] else 0
    s67 = frank(np.hstack([sup['R6a'], sup['R6b'], sup['R7']])) if dims['R6a'] or dims['R7'] else 0
    struct = (dims['R6a'] == dims['R6b'] == dims['R7'] and (dims['R6a'] == 0 or (frank(sup['R6a']) == 1 and s67 == 1)))
    extra = ''
    if not struct and dims['R6a'] and s67 == frank(sup['R6a']) == 2:
        # all kernels live in S (x) X1^*, S = the same 2-dim subspace of M^*: separations can only occur at points of P(S);
        # exact pencil along S (drop points common to R6a, R6b; ranks of R6a, R6b, R7, M2 there; t = inf included)
        import sympy, m2lines
        from specialU import nullspace as ns
        Sb = np.array(ns(sup['R6a'].T % p) if False else [], dtype=np.int64)
        # basis of the column space of the support matrix
        M = sup['R6a'] % p
        cols = []
        for c in range(M.shape[1]):
            if frank(np.array(cols + [M[:, c]])) > len(cols): cols.append(M[:, c])
            if len(cols) == 2: break
        AB = {k: (m2lib.combine(FF[k], cols[0]), m2lib.combine(FF[k], cols[1])) for k in tens}
        tr = int(rng.integers(1, p))
        rho = {k: frank((AB[k][0] + tr * AB[k][1]) % p) for k in tens}
        hs = {k: m2lines.drop_poly(*AB[k], rho[k], rng) for k in ('R6a', 'R6b')}
        hc = hs['R6a'].gcd(hs['R6b'])
        pts = []
        facs = sympy.factor_list(hc.as_expr(), m2lines.X, modulus=p)[1] if hc.degree() > 0 else []
        for fq, mult in facs:
            q = sympy.Poly(fq, m2lines.X, modulus=p)
            if q.degree() > m2lines.EMAX: pts.append('deg%d-skipped' % q.degree()); continue
            rk = {}
            for k in tens: rk[k], lab = m2lines.rank_at_root(*AB[k], q)
            flag = ('!' if max(rk['R6a'], rk['R6b']) < rk['R7'] else '') + ('!!!' if rk['M2'] > max(rk['R6a'], rk['R6b']) else '')
            pts.append('%s(x%d):%d,%d/%d/M2=%d%s' % (lab, mult, rk['R6a'], rk['R6b'], rk['R7'], rk['M2'], flag))
        rk = {k: frank(AB[k][1]) for k in tens}
        pts.append('inf:%d,%d/%d/M2=%d' % (rk['R6a'], rk['R6b'], rk['R7'], rk['M2']))
        extra = ' | pencil on S: generic %d,%d/%d/M2=%d, deg h %d,%d common %d: %s' % (rho['R6a'], rho['R6b'], rho['R7'], rho['M2'],
                 hs['R6a'].degree(), hs['R6b'].degree(), hc.degree(), ' '.join(pts))
    print('lam=%s dir%d g=%d n1=%d n23=%d | %s | supp(R6a+R6b)=%d supp(all)=%d | %s%s' % (lam, dirn + 1, g, n1, n23, ' '.join(info), s6, s67,
          'STRUCT' if struct else 'DEEP', extra)); sys.stdout.flush()

if __name__ == '__main__':
    jobs = [l.strip() for l in open(sys.argv[2]) if l.strip()]
    W, NW = (int(sys.argv[3]), int(sys.argv[4])) if len(sys.argv) > 4 else (0, 1)
    for i, j in enumerate(jobs):
        if i % NW != W: continue
        mm = re.match(r'^(\(.*\)) (\d+)', j)
        try:
            run(eval(mm.group(1)), int(mm.group(2)))
        except Exception as e:
            print('lam=%s dir%d ERROR %r' % (mm.group(1), int(mm.group(2)) + 1, e)); sys.stdout.flush()
