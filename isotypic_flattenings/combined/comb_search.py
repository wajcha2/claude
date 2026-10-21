"""comb_search.py -- search for COMBINED isotypic flattenings that separate rank r_low from rank r_high.

usage: python3 comb_search.py n d r_low,r_high [options]
  --fam A,B,E        families (default A,B):
       A  fixed source lam, sum over targets (mu, nu); Kronecker spaces on the target side (aux = 1, levels l = 1, g),
          or with --aux k >= 2 on the source side via a shared X = C^k (generic Psi_j: X -> M_j^*)
       B  fixed target (mu, nu), sum over sources lam; Kronecker spaces on the source side (aux = 1, levels k = 1, g),
          or with --aux l >= 2 on the target side via a shared Y = C^l
       E  single component, generic Psi in M^* (x) X^* (x) Y with dim X, dim Y >= 2 ('reshaped'; g >= 2)
  --aux 1,2          aux dimensions for A and B (default 1)
  --nrand N          random subsets per lattice (default 300);  --pairs N / --triples N: caps (default 3000 / 1500)
  --greedy N         greedy runs per lattice (default 2);  --bmax S: skip B lattices whose compressed size exceeds S
  --seed s (default 5: the tensors of sweep_fast.py with the same seed and rank list), --cache DIR (default live/cache)
  --only-lam "lam;lam"  restrict family A to these sources;  --only-mn "mu|nu;..."  restrict family B
  --emax E           family E: skip (k, l) whose sampled matrix has more than E entries (default 4e7)
Every subset S tested is a flattening; '*** SEPARATES' marks dim on rank r_low < dim on rank r_high (exact = the
sample sizes guarantee the exact rank).  Rank r_low <= rank r_high always (semicontinuity), so only strict drops print.
Per lattice a summary line: members, number of subsets tested, singles/all/natural values, max drop."""
import sys, os, time, itertools, argparse
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from combflat import Context, LatticeFamily, fmt, p

ap = argparse.ArgumentParser()
ap.add_argument('n'); ap.add_argument('d', type=int); ap.add_argument('ranks')
ap.add_argument('--fam', default='A,B'); ap.add_argument('--aux', default='1')
ap.add_argument('--nrand', type=int, default=300); ap.add_argument('--pairs', type=int, default=3000)
ap.add_argument('--triples', type=int, default=1500); ap.add_argument('--greedy', type=int, default=2)
ap.add_argument('--bmax', type=int, default=2500); ap.add_argument('--emax', type=float, default=4e7)
ap.add_argument('--seed', type=int, default=5)
ap.add_argument('--cache', default=os.path.join(os.path.dirname(os.path.abspath(__file__)), 'live', 'cache'))
ap.add_argument('--only-lam', default=''); ap.add_argument('--only-mn', default='')
args = ap.parse_args()
ns = tuple(int(x) for x in args.n.split(',')); ns = ns * 3 if len(ns) == 1 else ns
ranks = [int(x) for x in args.ranks.split(',')]
fams = args.fam.split(','); auxes = [int(x) for x in args.aux.split(',')]
ctx = Context(ns, args.d, ranks, seed=args.seed, cache=args.cache, auxmax=max(auxes))
print('# comb_search n=%s d=%d ranks=%s seed=%d fam=%s aux=%s p=%d: %d sources, %d targets, %d ordered components'
      % (args.n, args.d, ranks, args.seed, args.fam, auxes, p, len(ctx.sources), len(ctx.targets), len(ctx.g)))
sys.stdout.flush()
FOUND = []

SEPSINGLE = set()          # (family, member, level) whose single block already separates
NHITS = {}                 # lattice -> [new hits, hits containing a separating single]
MAXPRINT = 20
SEEN = set()               # subsets already reported

def report(fam, S, dims, how):
    """print a separating S if it is NEW: no summand of S separates on its own (other hits are only counted)."""
    fk = (fam.kind, fam.key, fam.aux)
    skey = fk + tuple(sorted(map(repr, S)))
    if skey in SEEN:
        return
    SEEN.add(skey)
    cnt = NHITS.setdefault(fk, [0, 0])
    if len(S) == 1:
        SEPSINGLE.add(fk + tuple(S[0]))
    elif any(fk + tuple(s) in SEPSINGLE for s in S):
        cnt[1] += 1
        return
    cnt[0] += 1
    if len(S) > 1 and cnt[0] > MAXPRINT:
        return
    ex = fam.exact(S)
    head = 'fam%s%s %s=%s' % (fam.kind, '' if fam.aux == 1 else '(aux=%d)' % fam.aux, 'lam' if fam.kind == 'A' else 'mn',
                              fmt(fam.key) if fam.kind == 'A' else '%s|%s' % (fmt(fam.key[0]), fmt(fam.key[1])))
    line = '*** SEPARATES%s %s %s %s ranks %s exact=%s (%s)' % ('' if len(S) == 1 else ' NEW', head, fam.describe(S),
                                                                  '/'.join(map(str, dims)), '/'.join(map(str, ranks)), ex, how)
    print(line); sys.stdout.flush()
    FOUND.append(line)

def natural_groups(fam):
    """named member subsets: family A by mu, by nu, diagonal; family B by number of rows and by first row."""
    G = {}
    for m in fam.members:
        if fam.kind == 'A':
            mu, nu = m
            G.setdefault('mu=%s' % fmt(mu), []).append(m); G.setdefault('nu=%s' % fmt(nu), []).append(m)
            G.setdefault('diag' if mu == nu else 'offdiag', []).append(m)
            G.setdefault('rows(mu)+rows(nu)=%d' % (len(mu) + len(nu)), []).append(m)
        else:
            G.setdefault('rows=%d' % len(m), []).append(m); G.setdefault('row1=%d' % m[0], []).append(m)
    return {k: v for k, v in G.items() if 1 < len(v) < len(fam.members)}

def search(fam, rng):
    members = fam.members; m = len(members)
    full = [fam.full(x) for x in members]
    one = [(x, 1) for x in members]
    tested, best = [0], [0, None, None]
    def test(S, how):
        S = list(S)
        if not S:
            return None
        dims = fam.dims(S); tested[0] += 1
        drop = dims[-1] - dims[0]
        if drop > best[0]:
            best[:] = [drop, S, dims]
        if drop > 0:
            report(fam, S, dims, how)
        return dims
    singles = {}
    for x in members:
        for lev in fam.levels[x]:
            singles[(x, lev)] = test([(x, lev)], 'single')
    if m == 1:
        return tested[0], best, singles, {}
    named = {'all': test(full, 'all'), 'all:1': test(one, 'all:1')}
    for x in members:
        test([y for y in full if y[0] != x], 'all-but-one')
    for name, grp in natural_groups(fam).items():
        named[name] = test([fam.full(x) for x in grp], name)
        test([(x, 1) for x in grp], name + ':1')
    pairs = list(itertools.combinations(full, 2))
    if len(pairs) > args.pairs:
        pairs = [pairs[i] for i in rng.choice(len(pairs), args.pairs, replace=False)]
    for S in pairs:
        test(S, 'pair')
    if m >= 3:
        if m * (m - 1) * (m - 2) // 6 <= args.triples:
            trip = list(itertools.combinations(full, 3))
        else:
            trip = [tuple(full[i] for i in rng.choice(m, 3, replace=False)) for _ in range(args.triples)]
        for S in trip:
            test(S, 'triple')
    for _ in range(args.nrand):
        k = int(rng.integers(2, m + 1))
        idx = rng.choice(m, k, replace=False)
        test([(members[i], int(rng.choice(fam.levels[members[i]]))) for i in idx], 'random')
    for _ in range(args.greedy):
        # greedy: grow S one member (full level) at a time, keeping the largest drop (ties: random)
        S, rest = [], list(full)
        while rest:
            scores = []
            for y in rest:
                dims = test(S + [y], 'greedy')
                scores.append((dims[-1] - dims[0], rng.random(), y))
            scores.sort(key=lambda t: (-t[0], t[1]))
            S.append(scores[0][2]); rest.remove(scores[0][2])
    return tested[0], best, singles, named

def summary(fam, tested, best, singles, named, secs):
    sv = ' '.join('%s:%s' % (fam.describe([s])[1:-1], '/'.join(map(str, v))) for s, v in singles.items())
    nv = ' '.join('%s:%s' % (k, '/'.join(map(str, v))) for k, v in named.items() if v is not None)
    head = 'fam%s%s %s=%s' % (fam.kind, '' if fam.aux == 1 else '(aux=%d)' % fam.aux, 'lam' if fam.kind == 'A' else 'mn',
                              fmt(fam.key) if fam.kind == 'A' else '%s|%s' % (fmt(fam.key[0]), fmt(fam.key[1])))
    cnt = NHITS.get((fam.kind, fam.key, fam.aux), [0, 0])
    print('%s members=%d size=%d tested=%d maxdrop=%d%s new_hits=%d hits_with_separating_single=%d  singles: %s  named: %s  (%.1fs)'
          % (head, len(fam.members), fam.size, tested, best[0],
             '' if not best[0] else ' at %s %s' % (fam.describe(best[1]), '/'.join(map(str, best[2]))), cnt[0], cnt[1], sv, nv, secs))
    sys.stdout.flush()

T0 = time.time()
if 'A' in fams:
    only = [tuple(int(c) for c in s.split('.')) if '.' in s else tuple(int(c) for c in s) for s in args.only_lam.split(';') if s]
    for lam in sorted(ctx.sources, key=lambda l: ctx.n1(l)):
        if only and lam not in only:
            continue
        for aux in auxes:
            t0 = time.time()
            fam = LatticeFamily(ctx, 'A', lam, aux=aux, levels='ends')
            res = search(fam, np.random.default_rng([args.seed, 21, aux] + list(lam)))
            summary(fam, *res, time.time() - t0)
        ctx.drop()
if 'B' in fams:
    def parse_mn(s):
        a, b = s.split('|')
        return tuple(tuple(int(c) for c in x) for x in (a, b))
    only = [parse_mn(s) for s in args.only_mn.split(';') if s]
    for mn in sorted(ctx.targets, key=lambda mn: ctx.K[mn]):
        if only and mn not in only:
            continue
        for aux in auxes:
            t0 = time.time()
            nmem = sum(1 for lam in ctx.sources if (lam,) + mn in ctx.g)
            bound = min(aux * (ctx.K[mn] - 8), ctx.capB[mn])
            if bound + 8 > args.bmax:
                print('famB mn=%s|%s aux=%d SKIPPED (compressed size %d > bmax %d; %d sources)' % (fmt(mn[0]), fmt(mn[1]), aux, bound + 8, args.bmax, nmem))
                continue
            fam = LatticeFamily(ctx, 'B', mn, aux=aux, levels='ends')
            res = search(fam, np.random.default_rng([args.seed, 22, aux] + list(mn[0]) + [0] + list(mn[1])))
            summary(fam, *res, time.time() - t0)
        ctx.drop()
if 'E' in fams:
    for tri in sorted(ctx.g, key=lambda t: ctx.g[t] * ctx.N1[t[0]] * ctx.K[t[1:]]):
        g = ctx.g[tri]
        if g < 2:
            continue
        lam, mn = tri[0], tri[1:]
        t0 = time.time(); out = []
        for k in range(2, g + 1):
            for l in range(2, g + 1):
                if k * ctx.N1[lam] * l * ctx.K[mn] > args.emax:
                    out.append('%dx%d:skip' % (k, l)); continue
                dims, ex = ctx.block_rank([(lam, k)], [(mn, l)])
                out.append('%dx%d:%s%s' % (k, l, '/'.join(map(str, dims)), '' if ex else '(inexact)'))
                if dims[0] < dims[-1]:
                    line = '*** SEPARATES famE %s g=%d k=%d l=%d %s ranks %s exact=%s' % (tri, g, k, l, '/'.join(map(str, dims)), '/'.join(map(str, ranks)), ex)
                    print(line); FOUND.append(line)
        print('famE %s g=%d dims=(%d,%d) %s (%.1fs)' % (tri, g, ctx.n1(lam), ctx.n23(mn), ' '.join(out), time.time() - t0))
        sys.stdout.flush()
        ctx.drop([tri])
nnew = sum(v[0] for v in NHITS.values()); nold = sum(v[1] for v in NHITS.values())
print('n=%s d=%d ranks=%s total %.0fs: separating singles %d, NEW combined hits %d (printed: first %d per lattice), hits containing a separating single %d'
      % (args.n, args.d, ranks, time.time() - T0, len(SEPSINGLE), nnew - len(SEPSINGLE), MAXPRINT, nold))
print('FOUND (printed lines): %d' % len(FOUND))
