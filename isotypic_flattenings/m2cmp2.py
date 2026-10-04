"""python3 m2cmp2.py LIST jobfile [KCAP [worker nworkers]]   or   python3 m2cmp2.py "lam" dirn [KCAP]
Like m2cmp.py (ranks of R6a, R6b, R7, M2 for 1-dim U = generic phi, and the full stacks H_g, V_g with U = M^*), plus the
containment tests that decide whether M2 can beat a rank-6 tensor at ANY U:
  all ranks of T at all U are determined by K(T) = ker(V_g(T): M^* (x) S^{l1}V^* -> rest)   [F_phi(T) x = V_g(T)(phi (x) x)]
  and equally by K'(T) = ker(H_g(T)^t: M^* (x) rest^* -> S^{l1}V); if K(R6) <= K(M2) or K'(R6) <= K'(M2), then
  rank_U(M2) <= rank_U(R6) for every U and every type (1-dim, H-stack, V-stack).
  incV = rank[V(R6a) | V(M2)] - rank V(R6a)   (columns = target points; 0  <=>  K(R6a) <= K(M2))
  incH = rank[H(R6a) ; H(M2)] - rank H(R6a)   (rows = source points;  0  <=>  K'(R6a) <= K'(M2))
  Both need K >= max(V_g(R6a), V_g(M2)) + 8 target points to be valid (else marked '?').
  Verdict: EXCL (incV = 0 or incH = 0, valid) / OPEN.  Env ALLK=1 also computes H_k, V_k for nested generic U_k, k < g."""
import sys, os, re, time, numpy as np
import m2lib
from m2lib import p, dim_schur, kronecker, random_gs, frank, combine, choose_fillings, rand_tensor, m2_terms, compress_cols
import flatlib

def rank_cols(M, rng):           # rank of a tall/any matrix, compressing the longer side first
    if M.shape[0] > M.shape[1] + 8:
        return frank(compress_cols(M.T, M.shape[1] + 8, rng))
    return frank(compress_cols(M, M.shape[0] + 8, rng))

def run(lam, dirn, kcap=1500, seed=None, verbose=True):
    seed = int(os.environ.get('SEED', '11')) if seed is None else seed
    allk = os.environ.get('ALLK', '0') == '1'
    rng = np.random.default_rng([seed] + [x for l in lam for x in l] + [dirn])
    perm = [dirn] + [t for t in range(3) if t != dirn]
    lam_p = tuple(lam[t] for t in perm)
    g = kronecker(*lam)
    n1 = dim_schur(lam_p[0], 4); n23 = dim_schur(lam_p[1], 4) * dim_schur(lam_p[2], 4)
    N1 = min(n1, g * n23) + 8
    memel = float(os.environ.get('MEMEL', '4e7'))          # max g * N1 * K elements per tensor
    K = max(min(g * n1, n23, kcap, int(memel // (g * N1))), min(n1, n23)) + 8
    t0 = time.time()
    tens = {'R6a': rand_tensor(rng, 6), 'R6b': rand_tensor(rng, 6), 'R7': rand_tensor(rng, 7), 'M2': m2_terms('strassen')}
    if os.environ.get('NOR6B') == '1': del tens['R6b']
    tens = {k: tuple(v[t] for t in perm) for k, v in tens.items()}
    fills = choose_fillings(lam_p, g, tens['R7'], rng)
    gs = random_gs(rng, 4, N1, K)
    F = {k: [(flatlib.flat(f, v, gs) % p).astype(np.int32) for f in fills] for k, v in tens.items()}
    teval = time.time() - t0
    span = {k: frank(np.array([M[:min(N1, 64), :min(K, 64)].ravel() for M in F[k]])) for k in tens}
    C = rng.integers(0, p, (g, g))
    res = {}
    for name in tens:
        res[('g', 1, name)] = frank(combine(F[name], C[0]))
    if g >= 2:
        Hm = {k: np.hstack(F[k]) for k in tens}            # N1 x gK
        Vm = {k: np.vstack(F[k]) for k in tens}            # gN1 x K
        for name in tens:
            res[('H', g, name)] = rank_cols(Hm[name], rng)
            res[('V', g, name)] = rank_cols(Vm[name], rng)
        if allk:
            for name in tens:
                Gs = [combine(F[name], C[i]) for i in range(g)]
                c = min(K, N1)
                AH = np.hstack([compress_cols(G, c, rng) for G in Gs])            # N1 x g c
                hr = m2lib.prefix_ranks(AH, [c * (k + 1) for k in range(g)])
                AV = np.hstack([compress_cols(G.T, c, rng) for G in Gs])          # K x g c
                vr = m2lib.prefix_ranks(AV, [c * (k + 1) for k in range(g)])
                for k in range(2, g + 1):
                    res[('H', k, name)] = hr[k - 1]
                    if min(k * n1, n23) + 8 <= K:
                        res[('V', k, name)] = vr[k - 1]
                assert hr[0] == res[('g', 1, name)] or True
        valid = K >= max(res[('V', g, 'R6a')], res[('V', g, 'M2')]) + 8
        incV = rank_cols(np.hstack([Vm['R6a'], Vm['M2']]), rng) - res[('V', g, 'R6a')]
        incH = rank_cols(np.vstack([Hm['R6a'], Hm['M2']]), rng) - res[('H', g, 'R6a')]
        # same kernels for rank 6 and rank 7  =>  identical ranks at every U (no separation, hence no M2 win)
        sameV = res[('V', g, 'R6a')] == res[('V', g, 'R7')] and rank_cols(np.hstack([Vm['R6a'], Vm['R7']]), rng) == res[('V', g, 'R7')]
        sameH = res[('H', g, 'R6a')] == res[('H', g, 'R7')] and rank_cols(np.vstack([Hm['R6a'], Hm['R7']]), rng) == res[('H', g, 'R7')]
    else:
        valid, incV, incH, sameV, sameH = True, None, None, None, None
    types = sorted({(t, k) for t, k, _ in res})
    out, flags = [], set()
    for t, k in types:
        r6b = res.get((t, k, 'R6b'), res[(t, k, 'R6a')])
        r6 = max(res[(t, k, 'R6a')], r6b); r7 = res[(t, k, 'R7')]; m2 = res[(t, k, 'M2')]
        s = '%s%d:%d,%d/%d/M2=%d' % (t, k, res[(t, k, 'R6a')], r6b, r7, m2)
        if r6 < r7: flags.add('SEP'); s += '!'
        if m2 > r6: flags.add('M2WIN'); s += '!!!'
        out.append(s)
    if g >= 2:
        verdict = ('EXCL' if (incV == 0 or incH == 0) else 'NOSEP' if (sameV or sameH) else 'OPEN') + ('' if valid else '?')
        inc = 'incV=%d incH=%d sameV=%d sameH=%d %s' % (incV, incH, sameV, sameH, verdict)
    else:
        inc = 'g=1'
    line = 'lam=%s dir%d g=%d n1=%d n23=%d N1=%d K=%d span(%s)=%s | %s | %s | %s (eval %.0fs, total %.0fs)' % (
        lam, dirn + 1, g, n1, n23, N1, K, ','.join(tens), ','.join(str(span[k]) for k in tens), ' '.join(out), inc,
        ' '.join(sorted(flags)) or '-', teval, time.time() - t0)
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
            mm = re.match(r'^(\(.*\)) (\d+)(?: (\d+))?$', j)       # 'lam dirn [kcap for this job]'
            lam = eval(mm.group(1)); dirn = int(mm.group(2)); kc = int(mm.group(3)) if mm.group(3) else kcap
            if ('lam=%s dir%d' % (lam, dirn + 1)) in done: continue
            try:
                run(lam, dirn, kc)
            except Exception as e:
                import traceback; traceback.print_exc()
                print('lam=%s dir%d ERROR %r' % (lam, dirn + 1, e)); sys.stdout.flush()
    else:
        run(eval(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 1500)
