"""python3 specialverify.py n d lam t r [r ...]        (env SEED, PRIME, FCACHE as in specialscan.py)

Fresh-tensor check of the stacked flattenings with U = M (all g fillings) for one component lam and direction t
(0-based): for each rank r a new random rank-r tensor 'X<r>' (seeded by SEED; fillings and evaluation points of
the direction are re-drawn for every SEED), the filling matrices F_0 .. F_{g-1} (N1 x K, exact mod p) are evaluated
one at a time and added to
  V: rows of all F_i      -> rank of the V-stack  U (x) S_{l1}^* -> S_{l2} (x) S_{l3}  (bound min(g n1, n23)),
  H: columns of all F_i   -> rank of the H-stack  S_{l1}^* -> U^* (x) S_{l2} (x) S_{l3} (bound min(n1, g n23)).
The running ranks after each filling are printed and the result is appended as one JSON line to OUT
(default special/verify.jsonl).  Each F_i is checkpointed in FCACHE (removed at the end), so a restarted run
resumes.  Memory: the V basis (rank x K float64) plus one F_i."""
import os, sys, time, json
if os.environ.get('PYTHONHASHSEED') != '0':           # same fillings in every process (see specialscan.py)
    os.environ['PYTHONHASHSEED'] = '0'
    os.execv(sys.executable, [sys.executable] + sys.orig_argv[1:])
import specialscan as S
import numpy as np

OUT = os.environ.get('OUT', 'special/verify.jsonl')


def main():
    n, d = int(sys.argv[1]), int(sys.argv[2])
    lam = tuple(tuple(x) for x in eval(sys.argv[3]))
    t = int(sys.argv[4])
    ranks = [int(x) for x in sys.argv[5:]]
    seed = int(os.environ.get('SEED', '11'))
    perm_lam = tuple(lam[u] for u in [t] + [u for u in range(3) if u != t])
    rgen = S.generic_rank(n)
    rprobe = max(x for x in range(1, rgen + 1) if S.word_minor_size(perm_lam, n, x) <= S.rankscan.WCAP)
    cp = S.Comp(n, lam, t, seed, rprobe)
    S.log('verify n=%d d=%d lam=%s dir %d seed %d p %d: g=%d n1=%d n23=%d N1=%d K=%d' % (
        n, d, lam, t + 1, seed, S.p, cp.g, cp.n1, cp.n23, cp.N1, cp.K))
    for r in ranks:
        S.reset_peak_rss()
        T0 = time.time()
        name = 'X%d' % r
        cp.add_tensor(name, r)
        vm = cp.D.vm(name)
        EV, EH = S.RREF(cp.K), S.RREF(cp.N1)
        vs, hs = [], []
        path = cp.fcache_path(name)
        for i, fl in enumerate(cp.D.fillings):
            pi = path[:-4] + '_f%d.npy' % i
            Fi = None
            if os.path.exists(pi):
                try:
                    Fi = np.load(pi).astype(np.float64)
                    assert Fi.shape == (cp.N1, cp.K)
                except Exception:
                    Fi = None
            if Fi is None:
                Fi = np.asarray(S.compute_F(fl[0], vm, cp.D.pm, fl[1], fl[2]), dtype=np.float64)
                os.makedirs(S.FCACHE, exist_ok=True)
                np.save(pi[:-4] + '.tmp.npy', Fi.astype(np.float32))
                os.replace(pi[:-4] + '.tmp.npy', pi)
            EV.add(Fi)
            EH.add(Fi.T)
            vs.append(EV.rank)
            hs.append(EH.rank)
            S.log('   r%d after F_%d: V %d  H %d  (%.0fs)' % (r, i, EV.rank, EH.rank, time.time() - T0))
            del Fi
        rec = {'n': n, 'd': d, 'lam': lam, 't': t, 'r': r, 'seed': seed, 'p': S.p, 'g': cp.g, 'n1': cp.n1,
               'n23': cp.n23, 'V': vs, 'H': hs, 'Vbound': min(cp.g * cp.n1, cp.n23), 'Hbound': min(cp.n1, cp.g * cp.n23),
               'wall': time.time() - T0, 'rss_peak_mb': S.peak_rss_mb(),
               'ts': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}
        with open(OUT, 'a') as fh:
            fh.write(json.dumps(rec) + '\n')
        S.log('   r%d: V-stack (U = M) %d of bound %d, H-stack %d of bound %d  (%.0fs, peak %.0f MB)' % (
            r, vs[-1], rec['Vbound'], hs[-1], rec['Hbound'], rec['wall'], rec['rss_peak_mb']))
        for i in range(len(cp.D.fillings)):
            pi = path[:-4] + '_f%d.npy' % i
            if os.path.exists(pi):
                os.remove(pi)


if __name__ == '__main__':
    main()
