"""kp_single.py -- H_s and V_s flattenings of single isotypic components for EVERY projection rank s = 1..g of the
Kronecker space (random s-dim subspace U of M^*), with sample sizes cut to what these single flattenings need (so it
reaches degrees where the combined search of kp_search.py is too expensive).

usage: python3 kp_single.py n d r_lo,r_hi --dir k [--mode H|V|HV] [--gmin 3] [--worker i --nworkers m] [--resume logs]
  H_s : S^{lam}A^* -> U^* (x) S^{mu}B (x) S^{nu}C     (s functionals side by side; rank = dim of the sum of their
        column spaces in S^{lam}A),   needs N1 >= min(n1, s n23), K >= min(n23, n1)
  V_s : U (x) S^{lam}A^* -> S^{mu}B (x) S^{nu}C       (stacked; rank = dim of the sum of their row spaces),
        needs N1 >= min(n1, n23), K >= min(n23, s n1)
(s = 1 is the generic functional gN for both; s = g is HN / VN of the isotypic sweeps.)  The functionals are nested
(phi_1..phi_s generic), every s is a generic s-dim projection.  Components (lam, mu, nu) are ORDERED triples of the
source factor `--dir` and the other two factors (for 4x5x5, --dir 0: source C^4; --dir 1: source the first C^5, targets
C^4 (x) C^5; --dir 2 is --dir 1 with the two C^5 factors swapped, i.e. the same components).  Only components with
g >= gmin (default 3: those with a level strictly between 1 and g).  Same tensors as sweep_fast.py / combflat.Context
for the same seed and ranks; exact mod p (env PRIME for a second prime).
Output per component: 'kpS lam|mu|nu g=.. dims=(n1,n23) H:1/a/b,2/..,..  V:1/..  (time)', hits '*** SEPARATES [I|E]'
([I] = 1 < s < g, new w.r.t. the isotypic sweeps; [E] = s = 1 or s = g).  Components go to the
workers by a static split of the cost-sorted list (component i -> worker i mod nworkers), cheapest first;
--resume skips components with a result line in earlier logs (after a container restart)."""
import sys, os, time, argparse
PRIME = int(os.environ.get('PRIME', '0'))
# combflat (2026-10-23) scores up to FILLPOOL = 1500 random fillings per component unless one below FILLCHEAP flops turns up;
# its default 1e8 makes the many small components here pay 1-4 s of scoring each (kpA lam=33 at 4x5x5 d=6: 62 of 177 s).
# 1e9 stops after 100 fillings whenever one evaluates in about a second.  Only the chosen basis changes, not the ranks.
os.environ.setdefault('FILLCHEAP', '1e9')
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import hwv, isoflat
if PRIME:
    hwv.p = isoflat.p = PRIME
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from combflat import Context, eval_F, fmt, p, mulmod, EXTRA
from hwv_fast import minors_of_points
from isoflat import modrank

ap = argparse.ArgumentParser()
ap.add_argument('n'); ap.add_argument('d', type=int); ap.add_argument('ranks')
ap.add_argument('--dir', type=int, default=0); ap.add_argument('--seed', type=int, default=5)
ap.add_argument('--mode', default='HV'); ap.add_argument('--gmin', type=int, default=3)
ap.add_argument('--worker', type=int, default=0); ap.add_argument('--nworkers', type=int, default=1)
ap.add_argument('--resume', default='', help='log1:log2: skip components already reported there')
ap.add_argument('--maxcost', type=float, default=float('inf'), help='skip components with g * N1 * K above this')
ap.add_argument('--nomirror', action='store_true', help='equal target dimensions: only one of (lam, mu, nu), (lam, nu, mu)')
ap.add_argument('--only', default='', help='comma-free list "lam|mu|nu;..." of components')
args = ap.parse_args()
ns = tuple(int(x) for x in args.n.split(',')); ns = ns * 3 if len(ns) == 1 else ns
ranks = [int(x) for x in args.ranks.split(',')]
ctx = Context(ns, args.d, ranks, seed=args.seed, dirn=args.dir, cache=None, verbose=False)
H, V = 'H' in args.mode, 'V' in args.mode

def sizes(tri):
    g = ctx.g[tri]; n1 = ctx.n1(tri[0]); n23 = ctx.n23(tri[1:])
    N1 = min(n1, g * n23 if H else n23) + EXTRA
    K = min(n23, g * n1 if V else n1) + EXTRA
    return N1, K

comps = [t for t in ctx.g if ctx.g[t] >= args.gmin]
if args.nomirror and ctx.ns[1] == ctx.ns[2]:
    comps = [t for t in comps if ctx.pidx[1][t[1]] <= ctx.pidx[2][t[2]]]     # swapping the target factors: same generic ranks
if args.only:
    want = set(args.only.split(';'))
    comps = [t for t in comps if '%s|%s|%s' % tuple(map(fmt, t)) in want]
comps.sort(key=lambda t: (ctx.g[t] * np.prod(sizes(t)), ctx.tri_index(t)))
DONE = set()
for lf in args.resume.split(':'):
    if lf and os.path.exists(lf):
        for l in open(lf):
            if l.startswith('kpS '):
                DONE.add(l.split()[1])
print('# kp_single n=%s d=%d ranks=%s seed=%d dir=%d mode=%s gmin=%d p=%d worker %d/%d: %d components, %d already done'
      % (args.n, args.d, ranks, args.seed, args.dir, args.mode, args.gmin, p, args.worker, args.nworkers, len(comps), len(DONE)))
sys.stdout.flush()
FOUND = []
T0 = time.time()
for i, tri in enumerate(comps):
    N1, K = sizes(tri); g = ctx.g[tri]
    if g * N1 * K > args.maxcost:
        continue
    if i % args.nworkers != args.worker or '%s|%s|%s' % tuple(map(fmt, tri)) in DONE:
        continue
    t0 = time.time()
    lam, mn = tri[0], tri[1:]
    n1, n23 = ctx.n1(lam), ctx.n23(mn)
    # per-component sample points (own random streams; the shared-point Context sizes are not used)
    rng = np.random.default_rng([args.seed, 41, args.dir] + ctx.tri_index(tri))
    G0 = rng.integers(0, p, (N1, ctx.ns[0], ctx.ns[0]))
    Gs = [rng.integers(0, p, (K, ctx.ns[t], ctx.ns[t])) for t in (1, 2)]
    pm = [{l: minors_of_points(G0, l) for l in range(1, ctx.ns[0] + 1)}] + \
         [{l: minors_of_points(G, l) for l in range(1, ctx.ns[t] + 1)} for G, t in zip(Gs, (1, 2))]
    basis = ctx.basis(tri)
    Phi = rng.integers(1, p, (g, g))            # column t = the t-th generic functional (nested: first s columns)
    res = {'H': {}, 'V': {}}
    for r in ranks:
        Fs = np.stack([eval_F(f, ctx.vm(r), pm) for f in basis])        # (g, N1, K) int64
        Fphi = [None] * g
        accH = accV = None
        cV = min(K, g * n1 + EXTRA)
        crng = np.random.default_rng([args.seed, 42, args.dir, r] + ctx.tri_index(tri))
        for s in range(g):
            Fp = np.zeros((N1, K), dtype=np.int64)
            for m in range(g):
                Fp = (Fp + int(Phi[m, s]) * Fs[m]) % p
            if H:
                C = mulmod(Fp, crng.integers(0, p, (K, N1)))                  # N1 x N1, same column space as Fp
                accH = C if accH is None else (accH + C) % p
                res['H'].setdefault(s + 1, []).append(modrank(accH))
            if V:
                C = mulmod(crng.integers(0, p, (cV, N1)), Fp)                 # cV x K, same row space as Fp
                accV = C if accV is None else (accV + C) % p
                res['V'].setdefault(s + 1, []).append(modrank(accV))
        del Fs
    out = []
    for kind in 'HV':
        if not res[kind]:
            continue
        out.append('%s:%s' % (kind, ','.join('%d/%s' % (s, '/'.join(map(str, v))) for s, v in sorted(res[kind].items()))))
        for s, v in sorted(res[kind].items()):
            if v[0] < v[1]:
                cls = 'I' if 1 < s < g else 'E'
                line = '*** SEPARATES [%s] r%d<r%d kpS %s|%s|%s dir%d %s_%d g=%d dims=(%d,%d) %s ranks %s' % (
                    cls, ranks[0], ranks[1], fmt(lam), fmt(mn[0]), fmt(mn[1]), args.dir, kind, s, g, n1, n23,
                    '/'.join(map(str, v)), '/'.join(map(str, ranks)))
                print(line); FOUND.append(line); sys.stdout.flush()
    print('kpS %s|%s|%s g=%d dims=(%d,%d) samples=(%d,%d) %s (%.1fs)' % (fmt(lam), fmt(mn[0]), fmt(mn[1]), g, n1, n23, N1, K,
                                                                         '  '.join(out), time.time() - t0))
    sys.stdout.flush()
print('n=%s d=%d kp_single worker %d total %.0fs: FOUND %d' % (args.n, args.d, args.worker, time.time() - T0, len(FOUND)))
