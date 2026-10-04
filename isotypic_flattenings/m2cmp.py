"""python3 m2cmp.py "lam" dirn [KCAP]      (or: python3 m2cmp.py LIST file  -- one 'lam dirn' per line)
Ranks of every flattening type of the 4-way isotypic tensor (see m2lib.py) for generic U of dimension k = 1..g, on two
random rank-6 tensors (R6a, R6b), a random rank-7 tensor (R7) and M2 (Strassen's 7 terms).  Also dim K_T = dim of
{phi : Phi_phi(T) = 0} for each tensor.  Source points N1 = min(n1, g n23) + 8, target points K = min(g n1, n23, KCAP) + 8;
V_k is reported only while min(k n1, n23) + 8 <= K.  Flags: 'SEP' when R6 < R7 for some (type, k); 'M2WIN' when M2 > R6.
Env SEED (default 11)."""
import sys, os, time, numpy as np
import m2lib
from m2lib import p, dim_schur, kronecker, random_gs, frank, Hrank, Vrank, combine, choose_fillings, rand_tensor, m2_terms
import flatlib

def run(lam, dirn, kcap=1500, seed=None, verbose=True):
    seed = int(os.environ.get('SEED', '11')) if seed is None else seed
    rng = np.random.default_rng([seed] + [x for l in lam for x in l] + [dirn])
    perm = [dirn] + [t for t in range(3) if t != dirn]
    lam_p = tuple(lam[t] for t in perm)
    g = kronecker(*lam)
    n1 = dim_schur(lam_p[0], 4); n23 = dim_schur(lam_p[1], 4) * dim_schur(lam_p[2], 4)
    N1 = min(n1, g * n23) + 8
    K = min(g * n1, n23, kcap) + 8
    t0 = time.time()
    tens = {'R6a': rand_tensor(rng, 6), 'R6b': rand_tensor(rng, 6), 'R7': rand_tensor(rng, 7), 'M2': m2_terms('strassen')}
    tens = {k: tuple(v[t] for t in perm) for k, v in tens.items()}
    fills = choose_fillings(lam_p, g, tens['R7'], rng)
    gs = random_gs(rng, 4, N1, K)
    F = {k: [flatlib.flat(f, v, gs) % p for f in fills] for k, v in tens.items()}
    teval = time.time() - t0
    # dim of the span of the F_j(T) (= g - dim K_T)
    span = {k: frank(np.array([M[:min(N1, 64), :min(K, 64)].ravel() for M in F[k]])) for k in tens}
    res = {}
    C = rng.integers(0, p, (g, g))          # U_k = span of the first k rows of C (nested generic flag)
    ks = list(range(1, g + 1))
    for k in ks:
        for name in tens:
            Gs = [combine(F[name], C[i]) for i in range(k)]
            if k == 1:
                res[('g', 1, name)] = frank(Gs[0])
            else:
                res[('H', k, name)] = Hrank(Gs, rng)
            if k > 1 and min(k * n1, n23) + 8 <= K:
                res[('V', k, name)] = Vrank(Gs, rng)
    types = sorted({(t, k) for t, k, _ in res})
    out, flags = [], set()
    for t, k in types:
        r6 = max(res[(t, k, 'R6a')], res[(t, k, 'R6b')]); r7 = res[(t, k, 'R7')]; m2 = res[(t, k, 'M2')]
        s = '%s%d:%d,%d/%d/M2=%d' % (t, k, res[(t, k, 'R6a')], res[(t, k, 'R6b')], r7, m2)
        if r6 < r7: flags.add('SEP'); s += '!'
        if m2 > r6: flags.add('M2WIN'); s += '!!!'
        out.append(s)
    line = 'lam=%s dir%d g=%d n1=%d n23=%d N1=%d K=%d span(R6a,R6b,R7,M2)=%s | %s | %s (eval %.0fs, total %.0fs)' % (
        lam, dirn + 1, g, n1, n23, N1, K, ','.join(str(span[k]) for k in tens), ' '.join(out), ' '.join(sorted(flags)) or '-',
        teval, time.time() - t0)
    if verbose: print(line); sys.stdout.flush()
    return res, flags, line

if __name__ == '__main__':
    if sys.argv[1] == 'LIST':
        jobs = [l.split('|')[0].strip() for l in open(sys.argv[2]) if l.strip() and not l.startswith('#')]
        kcap = int(sys.argv[3]) if len(sys.argv) > 3 else 1500
        W, NW = (int(sys.argv[4]), int(sys.argv[5])) if len(sys.argv) > 5 else (0, 1)
        done = set()
        for lf in os.environ.get('RESUME', '').split(':'):
            if lf and os.path.exists(lf):
                done |= {l.split(' g=')[0] for l in open(lf) if l.startswith('lam=')}
        for i, j in enumerate(jobs):
            if i % NW != W: continue
            lam_s, dirn_s = j.rsplit(' ', 1)
            lam = eval(lam_s); dirn = int(dirn_s)
            if ('lam=%s dir%d' % (lam, dirn + 1)) in done: continue
            try:
                run(lam, dirn, kcap)
            except Exception as e:
                print('lam=%s dir%d ERROR %r' % (lam, dirn + 1, e)); sys.stdout.flush()
    else:
        run(eval(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 1500)
