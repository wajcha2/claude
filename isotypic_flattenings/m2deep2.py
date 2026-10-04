"""python3 m2deep2.py LIST jobfile [worker nworkers]   -- cheaper version of m2deep.py for screen failures at d >= 10.
Kernels K(T) = ker V_g(T) for R6a and R7 only (dimension, M^*-support S).  Verdicts:
  STRUCT   dim K(R6a) = dim K(R7) and both supports are the same 1-dim space <phi_0>: rank_U(R6) = rank_U(R7) for every U.
  SUPP=s   both kernels have the same dimension and the same support S (dim s >= 2): a separating point must lie in P(S);
           exact pencils along S (s = 2) or NL random lines in P(S): roots of the drop polynomial of R6a, rank of R7 there.
           Only if some root has rank(R6a) < rank(R7) are R6b and M2 evaluated (SEP? / WIN flags).
  DIFF     dimensions or supports differ (reported for manual analysis).
Coordinates: exactly n1 independent source points, K = min(g n1, n23) + 8 target points."""
import sys, os, re, numpy as np, sympy
import m2lib, m2lines
from m2lib import p, dim_schur, kronecker, random_gs, frank, choose_fillings, rand_tensor, m2_terms, compress_cols
from specialU import nullspace

def kmats(Fs, g, n1, rng):
    V = np.vstack(Fs)
    return [np.array(k, dtype=np.int64).reshape(g, n1) for k in nullspace(compress_cols(V, V.shape[0] + 8, rng).T % p)]

def colbasis(M, s):
    cols = []
    for c in range(M.shape[1]):
        if frank(np.array(cols + [M[:, c]])) > len(cols): cols.append(M[:, c])
        if len(cols) == s: break
    return np.array(cols)

def run(lam, dirn, seed=31):
    rng = np.random.default_rng([seed] + [x for l in lam for x in l] + [dirn])
    perm = [dirn] + [t for t in range(3) if t != dirn]
    lam_p = tuple(lam[t] for t in perm); g = kronecker(*lam)
    n1 = dim_schur(lam_p[0], 4); n23 = dim_schur(lam_p[1], 4) * dim_schur(lam_p[2], 4)
    tens = {'R6a': rand_tensor(rng, 6), 'R7': rand_tensor(rng, 7), 'R6b': rand_tensor(rng, 6), 'M2': m2_terms('strassen')}
    tens = {k: tuple(v[t] for t in perm) for k, v in tens.items()}
    fills = choose_fillings(lam_p, g, tens['R7'], rng)
    K = min(g * n1, n23) + 8
    for _ in range(5):
        gs = random_gs(rng, 4, n1, K)
        F = {'R7': [m2lib.flat_pre(f, m2lib.prep_all(tens['R7'], gs)) % p for f in fills]}
        if frank(np.hstack(F['R7'])) == n1: break
    else:
        print('lam=%s dir%d source points dependent' % (lam, dirn + 1)); sys.stdout.flush(); return
    getF = lambda k: F.setdefault(k, [m2lib.flat_pre(f, m2lib.prep_all(tens[k], gs)) % p for f in fills])
    getF('R6a')
    km = {k: kmats(F[k], g, n1, rng) for k in ('R6a', 'R7')}
    dims = {k: len(v) for k, v in km.items()}
    sup = {k: (np.hstack(v) % p if v else np.zeros((g, 0), dtype=np.int64)) for k, v in km.items()}
    sd = {k: (frank(sup[k]) if dims[k] else 0) for k in km}
    sall = frank(np.hstack([sup['R6a'], sup['R7']])) if (dims['R6a'] or dims['R7']) else 0
    head = 'lam=%s dir%d g=%d n1=%d n23=%d | dimK R6a=%d R7=%d supp %d,%d joint %d' % (lam, dirn + 1, g, n1, n23, dims['R6a'], dims['R7'], sd['R6a'], sd['R7'], sall)
    if dims['R6a'] != dims['R7'] or sd['R6a'] != sd['R7'] or sall != sd['R6a']:
        print(head + ' | DIFF'); sys.stdout.flush(); return
    s = sd['R6a']
    if s <= 1:
        print(head + ' | STRUCT'); sys.stdout.flush(); return
    Sb = colbasis(sup['R6a'], s)
    lines = [(Sb[0], Sb[1])] if s == 2 else [tuple((rng.integers(0, p, s) @ Sb) % p for _ in range(2)) for _ in range(int(os.environ.get('NL', '3')))]
    out, flags = [], set()
    for la, lb in lines:
        AB = {k: (m2lib.combine(F[k], la), m2lib.combine(F[k], lb)) for k in ('R6a', 'R7')}
        tr = int(rng.integers(1, p))
        rho = {k: frank((AB[k][0] + tr * AB[k][1]) % p) for k in AB}
        h = m2lines.drop_poly(*AB['R6a'], rho['R6a'], rng)
        pts = []
        facs = sympy.factor_list(h.as_expr(), m2lines.X, modulus=p)[1] if h.degree() > 0 else []
        for fq, mult in facs:
            q = sympy.Poly(fq, m2lines.X, modulus=p)
            if q.degree() > m2lines.EMAX: pts.append('deg%d-skipped' % q.degree()); flags.add('SKIPPED'); continue
            r6, lab = m2lines.rank_at_root(*AB['R6a'], q); r7, _ = m2lines.rank_at_root(*AB['R7'], q)
            tag = '%s(x%d):%d/%d' % (lab, mult, r6, r7)
            if r6 < r7:                       # candidate: check a second rank-6 tensor and M2
                for k in ('R6b', 'M2'):
                    getF(k)
                    if k not in AB: AB[k] = (m2lib.combine(F[k], la), m2lib.combine(F[k], lb))
                r6b, _ = m2lines.rank_at_root(*AB['R6b'], q); rm, _ = m2lines.rank_at_root(*AB['M2'], q)
                tag += ',R6b=%d,M2=%d' % (r6b, rm)
                if max(r6, r6b) < r7: flags.add('SEP?')
                if rm > max(r6, r6b): flags.add('WIN')
            pts.append(tag)
        r6, r7 = frank(AB['R6a'][1]), frank(AB['R7'][1])
        pts.append('inf:%d/%d' % (r6, r7))
        if r6 < r7: flags.add('SEP?inf')
        out.append('generic %d/%d deg h %d: %s' % (rho['R6a'], rho['R7'], h.degree(), ' '.join(pts)))
    print(head + ' | SUPP=%d | %s | %s' % (s, ' ; '.join(out), ' '.join(sorted(flags)) or '-')); sys.stdout.flush()

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
