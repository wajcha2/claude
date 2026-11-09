"""comb_search.py -- search for COMBINED isotypic flattenings that separate rank r_low from rank r_high.

usage: python3 comb_search.py n d r_1,r_2[,r_3..] [options]   (separations r_i vs r_{i+1})
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
  --resume L1:L2     skip lattices / components already summarised in these logs (after a restart)
  --emax E           family E: skip (k, l) whose sampled matrix has more than E entries (default 4e7)
Every subset S tested is a flattening; '*** SEPARATES' marks dim on rank r_low < dim on rank r_high (exact = the
sample sizes guarantee the exact rank).  Ranks are nondecreasing in r (semicontinuity); every consecutive pair of the rank list is checked.
Per lattice a summary line: members, number of subsets tested, singles/all/natural values, max drop."""
import sys, os, re, ast, time, itertools, argparse
import multiprocessing as mp
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
ap.add_argument('--dir', type=int, default=0, help='source factor (0, 1, 2); needed for unequal formats such as 4,5,5')
ap.add_argument('--sources', default='', help='restrict to these source partitions, e.g. "61;52;511", or "pattern:K" = all lam with lam_1 >= d - K except (d)')
ap.add_argument('--maxsub', type=int, default=0, help='with --exhaust: only subsets of at most this many members (0 = all)')
ap.add_argument('--allsub', type=int, default=0, help='lattices with at most this many members: every subset with every combination of levels (1, g), each by a direct rank (checked before --exhaust); from the degree-9 combined session')
ap.add_argument('--allsub-maxconf', type=int, default=256, help='with --allsub: if the number of level combinations exceeds this, test every subset only at uniform levels (all full, all level 1)')
ap.add_argument('--exhaust', type=int, default=0, help='lattices with at most this many members: ALL subsets (levels full and 1) by incremental enumeration instead of sampling')
ap.add_argument('--direct-sub', dest='direct_sub', action='store_true', help='with --exhaust and --maxsub, or with --allsub: test the subsets '
                'by direct ranks (fam.dims, kept in the dims store, so a lattice resumes after a restart) instead of the '
                'incremental RREF walk, whose per-member bases and DFS stack need several K x K arrays (2026-11-09: the '
                'all-source d = 7 targets of size 14008..20858)')
ap.add_argument('--procs', type=int, default=1, help='with --direct-sub: rank this many subsets at a time in forked processes '
                'that share the thin matrices (fewer when --mem-budget does not allow)')
ap.add_argument('--mem-budget', dest='mem_budget', type=float, default=12e9, help='bytes for the thin matrices plus the '
                'subset matrices of the --procs processes')
ap.add_argument('--cache', default=os.path.join(os.path.dirname(os.path.abspath(__file__)), 'live', 'cache'))
ap.add_argument('--only-lam', default=''); ap.add_argument('--only-mn', default='')
ap.add_argument('--resume', default='', help='log1:log2: skip lattices / components already summarised there')
args = ap.parse_args()
ns = tuple(int(x) for x in args.n.split(',')); ns = ns * 3 if len(ns) == 1 else ns
ranks = [int(x) for x in args.ranks.split(',')]
fams = args.fam.split(','); auxes = [int(x) for x in args.aux.split(',')]
def parse_lam(s):
    return tuple(int(c) for c in s.split('.')) if '.' in s else tuple(int(c) for c in s)
only_sources = None
if args.sources.startswith('pattern:'):
    kk = int(args.sources.split(':')[1])
    from combflat import partitions as _parts
    _src_n = ns[args.dir]
    only_sources = [l for l in _parts(args.d, _src_n) if l[0] >= args.d - kk and l != (args.d,)]
elif args.sources:
    only_sources = [parse_lam(s) for s in args.sources.split(';') if s]
ctx = Context(ns, args.d, ranks, seed=args.seed, dirn=args.dir, cache=args.cache, auxmax=max(auxes), only_sources=only_sources)
if only_sources is not None:
    print('# restricted to sources %s' % only_sources)
print('# comb_search n=%s d=%d ranks=%s seed=%d dir=%d fam=%s aux=%s exhaust=%d p=%d: %d sources, %d targets, %d ordered components'
      % (args.n, args.d, ranks, args.seed, args.dir, args.fam, auxes, args.exhaust, p, len(ctx.sources), len(ctx.targets), len(ctx.g)))
sys.stdout.flush()
FOUND = []

SEPSINGLE = set()          # (family, member, level) whose single block already separates
NHITS = {}                 # lattice -> [new hits, hits containing a separating single]
MAXPRINT = 20
SEEN = set()               # subsets already reported

def report(fam, S, dims, how, pair):
    """print a separating S if it is NEW: no summand of S separates the same rank pair on its own (other hits are
    only counted).  pair = index i: ranks[i] vs ranks[i+1]."""
    fk = (fam.kind, fam.key, fam.aux, pair)
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
    line = '*** SEPARATES%s r%d<r%d %s %s %s ranks %s exact=%s (%s)' % ('' if len(S) == 1 else ' NEW', ranks[pair], ranks[pair + 1],
                                                                          head, fam.describe(S), '/'.join(map(str, dims)),
                                                                          '/'.join(map(str, ranks)), ex, how)
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

def dims_store(fam):
    """(file, dict) of the subset dims of this lattice already computed in an earlier run (2026-10-25): a large --allsub
    lattice takes hours and container restarts lost them twice; the dims are exact ranks for the fixed seed, so a
    restart reuses them.  One line 'repr(sorted(S))<TAB>d1,d2,...' per subset in the lattice's cache directory."""
    if not fam.ctx.cache:
        return None, {}
    key = fmt(fam.key) if fam.kind == 'A' else '%s-%s' % (fmt(fam.key[0]), fmt(fam.key[1]))
    fn = os.path.join(fam.ctx.cache, 'dims_%s%d_%s.txt' % (fam.kind, fam.aux, key))
    store = {}
    if os.path.exists(fn):
        for l in open(fn):
            parts = l.rstrip('\n').split('\t')
            if len(parts) == 2 and parts[1]:
                store[parts[0]] = tuple(int(x) for x in parts[1].split(','))
    return fn, store

def search(fam, rng):
    members = fam.members; m = len(members)
    full = [fam.full(x) for x in members]
    one = [(x, 1) for x in members]
    tested, best = [0], [0, None, None]
    sfile, store = dims_store(fam)
    def test(S, how):
        S = list(S)
        if not S:
            return None
        k = repr(sorted(S))
        if k in store:
            dims = store[k]
        else:
            dims = fam.dims(S)
            if sfile:
                with open(sfile, 'a') as fh:
                    fh.write('%s\t%s\n' % (k, ','.join(map(str, dims))))
            store[k] = dims
        tested[0] += 1
        drop = dims[-1] - dims[-2]          # the top pair (r_last - 1 vs r_last) drives the greedy search
        if drop > best[0]:
            best[:] = [drop, S, dims]
        for i in range(len(dims) - 1):
            if dims[i] < dims[i + 1]:
                report(fam, S, dims, how, i)
        return dims
    singles = {}
    for x in members:
        for lev in fam.levels[x]:
            singles[(x, lev)] = test([(x, lev)], 'single')
    if m == 1:
        return tested[0], best, singles, {}
    # a member whose level-1 subspace alone already has the lattice's maximal dimension (fam.rankcap) on the lowest rank
    # saturates every sum containing it, on every rank: drop such members (family A at d=9: every single target of the
    # source (7,1,1) already has rank n1 = 280 on rank 8, and 25000 pairs were all 280/280)
    satm = [x for x in members if singles[(x, min(fam.levels[x]))][0] >= fam.rankcap]
    if satm:
        print('# fam%s%s %s: %d of %d members saturated (dim %d on rank %d at level 1), dropped from the subsets'
              % (fam.kind, '' if fam.aux == 1 else '(aux=%d)' % fam.aux,
                 'lam=' + fmt(fam.key) if fam.kind == 'A' else 'mn=%s|%s' % (fmt(fam.key[0]), fmt(fam.key[1])),
                 len(satm), m, fam.rankcap, ranks[0]))
        sys.stdout.flush()
        members = [x for x in members if x not in satm]; m = len(members)
        for r in fam.mats:                                   # their compressed matrices are never used again
            for x in satm:
                for lev in fam.levels[x]:
                    fam.mats[r].pop((x, lev), None)
        full = [fam.full(x) for x in members]
        one = [(x, 1) for x in members]
        if m <= 1:
            return tested[0], best, singles, {}
    if fam.aux == 1:
        # direct-sum certificate (from the kronproj session, claude/zealous-mendel-i9qpdu): with aux 1 every level-l
        # subspace of a member lies in its full-level subspace.  If on rank r_i the full sum is DIRECT (its dim is the sum
        # of the full single dims) and every single (member, level) has equal dims on r_i and r_{i+1}, then every S has
        # dim_i(S) = sum of its single dims = sum of the r_{i+1} single dims >= dim_{i+1}(S): no S separates r_i from
        # r_{i+1}, and the lattice is done after one rank.
        dall = test(full, 'all')
        if all(dall[i] == sum(singles[s][i] for s in full) and
               all(v[i] == v[i + 1] for (x, lev), v in singles.items() if x in members) for i in range(len(ranks) - 1)):
            return tested[0], best, singles, {'all': dall, 'direct-sum-certified': (1,)}
    if m <= args.allsub:
        # every nonempty subset with every combination of the members' levels (1 and g: mixed levels included), each by
        # a direct rank (fam.dims, blocked modrank) -- for small lattices of large size this is much faster than the
        # RREF walk (python-loop rref in basis_rows); adopted from the degree-9 combined session (claude/charming-heisenberg-f66sy8)
        named = {}
        nconf = 1
        for x in members:
            nconf *= 1 + len(fam.levels[x])
        if nconf <= args.allsub_maxconf:
            confs = itertools.product(*[[None] + [(x, lev) for lev in fam.levels[x]] for x in members])
        else:
            # too many mixed-level combinations (e.g. 6 members with g >= 2: 3^6): every subset at uniform levels only,
            # whole Kronecker spaces or one generic functional each (2 * (2^m - 1) subsets)
            confs = itertools.chain(itertools.product(*[[None, fam.full(x)] for x in members]),
                                    itertools.product(*[[None, (x, 1)] for x in members]))
        if args.direct_sub:
            subs = [S for S in ([s for s in c if s is not None] for c in confs) if len(S) >= 2]
            res = direct_subsets(fam, subs, singles, test, store, sfile, tested, best)
            named = {'direct-sub': res}
            for nm, S in (('all', full), ('all:1', one)):
                if repr(sorted(S)) in store:
                    named[nm] = store[repr(sorted(S))]
            return tested[0], best, singles, named
        for S in confs:
            S = [s for s in S if s is not None]
            if len(S) < 2:
                continue
            dims = test(S, 'allsub')
            if len(S) == m and all(lev == max(fam.levels[x]) for x, lev in S):
                named['all'] = dims
            if len(S) == m and all(lev == 1 for x, lev in S):
                named['all:1'] = dims
        return tested[0], best, singles, named
    if m <= args.exhaust and args.direct_sub and args.maxsub and m > args.allsub:
        subs = [S for lev in ('full', 1) for k in range(2, min(args.maxsub, m) + 1)
                for S in itertools.combinations([fam.full(x) if lev == 'full' else (x, 1) for x in members], k)]
        res = direct_subsets(fam, subs, singles, test, store, sfile, tested, best)
        return tested[0], best, singles, {'direct-sub': res}
    if m <= args.exhaust:
        # every subset at the full level (Kronecker spaces whole) and at level 1 (one generic functional each)
        named = {}
        for lev in ('full', 1):
            def cb(S, dims, lev=lev):
                tested[0] += 1
                drop = dims[-1] - dims[-2]
                if drop > best[0]:
                    best[:] = [drop, list(S), dims]
                if len(S) == m:
                    named['all' if lev == 'full' else 'all:1'] = dims
                if any(dims[i] < dims[i + 1] for i in range(len(dims) - 1)):
                    test(S, 'exhaustive')            # re-checked by a direct rank, then reported
            fam.enumerate(lev, maxmembers=args.exhaust, callback=cb, maxsize=args.maxsub or None, members=members)
        return tested[0], best, singles, named
    named = {'all': test(full, 'all'), 'all:1': test(one, 'all:1')}
    for x in members:
        test([y for y in full if y[0] != x], 'all-but-one')
    for name, grp in natural_groups(fam).items():
        grp = [x for x in grp if x in members]
        if len(grp) < 2:
            continue
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
    for gi in range(args.greedy):
        # greedy: grow S one member at a time (full levels; every second run level 1), keeping the largest drop of the
        # top rank pair (ties: random); incremental RREF, hits re-checked with fam.dims
        cands = full if gi % 2 == 0 else one
        for S, dims in fam.greedy([], cands, rng, lambda dm: dm[-1] - dm[-2]):
            tested[0] += 1
            if any(dims[i] < dims[i + 1] for i in range(len(dims) - 1)) or dims[-1] - dims[-2] > best[0]:
                test(S, 'greedy')
    return tested[0], best, singles, named

_FAM = None
def _dimjob(task):
    S, idx = task
    return S, idx, _FAM.dims_at(S, idx)

def direct_subsets(fam, subsets, singles, test, store, sfile, tested, best):
    """--direct-sub: rank the given subsets (tuples of (member, level)) directly, larger ones first (by size, then by the
    sum of the levels), in --procs forked processes that share the thin matrices.  With two ranks r_lo < r_hi and aux 1,
    a subset S whose singles all have equal dims on r_lo and r_hi needs only r_lo when its sum is direct there (dim =
    sum of the single r_lo dims): then dim_hi(S) <= sum of the single r_hi dims = dim_lo(S), so S does not separate (the
    direct-sum certificate of one subset).  A subset whose every (member, level) lies in a member of a direct subset at
    a level >= its own (with aux 1 the level-l subspace lies in every higher-level one) is direct too and is skipped.
    Results: full dims in the dims store, direct subsets in <store>.direct; both are read again after a restart, and
    every result is written as soon as it arrives."""
    global _FAM
    prune = len(ranks) == 2 and fam.aux == 1
    dfile = sfile + '.direct' if sfile else None
    lofile = sfile + '.lo' if sfile else None              # r_lo dims of subsets that are not direct (r_hi still to do)
    dlist, lo_known = [], {}
    if dfile and os.path.exists(dfile):
        for l in open(dfile):
            dlist.append(dict(ast.literal_eval(l.split('\t')[0])))
    if lofile and os.path.exists(lofile):
        for l in open(lofile):
            k, v = l.rstrip('\n').split('\t')
            lo_known[k] = int(v)
    def covered(S):
        return any(all(x in D and lev <= D[x] for x, lev in S) for D in dlist)
    single_dims = {s: max(v) for s, v in singles.items()}
    mats_bytes = sum(a.nbytes for d in fam.mats.values() for a in d.values())
    def nbytes(S):
        rows = sum(single_dims[s] for s in S) + 8
        return rows * min(fam.ncols, rows) * 8
    def run(tasks):
        """tasks: [(S, rank indices)]; yields (S, idx, dims) as they arrive, in as many processes as --mem-budget
        allows for the largest matrix of this batch."""
        if not tasks:
            return
        tasks = sorted(tasks, key=lambda t: -nbytes(t[0]))                  # largest first: load balance
        procs = max(1, min(args.procs, len(tasks), int((args.mem_budget - mats_bytes) // max(nbytes(tasks[0][0]), 1))))
        if procs == 1:
            for t in tasks:
                yield _dimjob(t)
            return
        pool = mp.get_context('fork').Pool(procs)
        try:
            for res in pool.imap_unordered(_dimjob, tasks, chunksize=1):
                yield res
        finally:
            pool.terminate(); pool.join()
    def record(S, d):
        k_ = repr(sorted(S))
        store[k_] = d
        if sfile:
            with open(sfile, 'a') as fh:
                fh.write('%s\t%s\n' % (k_, ','.join(map(str, d))))
        test(S, 'exhaustive')
    uniq = {}
    for S in subsets:
        uniq.setdefault(frozenset(S), tuple(sorted(S, key=repr)))
    groups = {}
    for S in uniq.values():
        groups.setdefault((len(S), sum(lev for _, lev in S)), []).append(S)
    print('# direct-sub %d members, %d subsets in %d batches, thin matrices %.1f GB, largest subset matrix %.1f GB, '
          'up to %d processes' % (len(fam.members), len(uniq), len(groups), mats_bytes / 1e9,
                                  max(nbytes(S) for S in uniq.values()) / 1e9 if uniq else 0, args.procs))
    sys.stdout.flush()
    _FAM = fam
    nd = ns = nr = 0
    try:
        for key in sorted(groups, reverse=True):
            lo, rest, d0 = [], [], {}
            for S in groups[key]:
                k_ = repr(sorted(S))
                if k_ in store:
                    test(S, 'exhaustive')                         # counted and reported from the store
                    continue
                eq = prune and all(singles[s][0] == singles[s][1] for s in S)
                if eq and covered(S):
                    ns += 1
                    continue
                if eq and k_ in lo_known:                         # not direct on r_lo (earlier run): r_hi still to do
                    d0[k_] = lo_known[k_]; rest.append((S, (1,)))
                elif eq:
                    lo.append((S, (0,)))
                else:
                    rest.append((S, tuple(range(len(ranks)))))
            for S, idx, d in run(lo):
                k_ = repr(sorted(S))
                if d[0] == sum(singles[s][0] for s in S):
                    dlist.append(dict(S)); nd += 1
                    if dfile:
                        with open(dfile, 'a') as fh:
                            fh.write('%s\t%d\n' % (k_, d[0]))
                else:
                    d0[k_] = d[0]; rest.append((S, (1,)))
                    if lofile:
                        with open(lofile, 'a') as fh:
                            fh.write('%s\t%d\n' % (k_, d[0]))
            for S, idx, d in run(rest):
                record(S, (d0[repr(sorted(S))],) + d if idx == (1,) else d)
                nr += 1
            print('# direct-sub size %d, level sum %d: %d ranked, %d direct on r%d, %d skipped (so far)'
                  % (key[0], key[1], nr, nd, ranks[0], ns))
            sys.stdout.flush()
    finally:
        _FAM = None
    return nr, nd, ns

def summary(fam, tested, best, singles, named, secs):
    sv = ' '.join('%s:%s' % (fam.describe([s])[1:-1], '/'.join(map(str, v))) for s, v in singles.items())
    nv = ' '.join('%s:%s' % (k, '/'.join(map(str, v))) for k, v in named.items() if v is not None)
    head = 'fam%s%s %s=%s' % (fam.kind, '' if fam.aux == 1 else '(aux=%d)' % fam.aux, 'lam' if fam.kind == 'A' else 'mn',
                              fmt(fam.key) if fam.kind == 'A' else '%s|%s' % (fmt(fam.key[0]), fmt(fam.key[1])))
    cnt = [sum(v[i] for k, v in NHITS.items() if k[:3] == (fam.kind, fam.key, fam.aux)) for i in (0, 1)]
    print('%s members=%d size=%d tested=%d maxdrop=%d%s new_hits=%d hits_with_separating_single=%d  singles: %s  named: %s  (%.1fs)'
          % (head, len(fam.members), fam.size, tested, best[0],
             '' if not best[0] else ' at %s %s' % (fam.describe(best[1]), '/'.join(map(str, best[2]))), cnt[0], cnt[1], sv, nv, secs))
    sys.stdout.flush()

# --resume: lattices and family-E components that already have a summary (or SKIPPED) line in an earlier log of the
# same command are skipped (a container restart kills the run); the final totals then count this run's hits only
DONE = set()
for lf in args.resume.split(':'):
    if lf and os.path.exists(lf):
        for l in open(lf):
            m = re.match(r'fam([AB])(?:\(aux=(\d+)\))? (?:lam|mn)=(\S+) (?:members=|aux=(\d+) SKIPPED)', l)
            if m:
                DONE.add((m.group(1), int(m.group(2) or m.group(4) or 1), m.group(3)))
            elif l.startswith('famE '):
                DONE.add(('E', l[5:].split(' g=')[0]))
if DONE:
    print('# resume: %d lattices / components already done' % len(DONE)); sys.stdout.flush()

T0 = time.time()
if 'A' in fams:
    only = [tuple(int(c) for c in s.split('.')) if '.' in s else tuple(int(c) for c in s) for s in args.only_lam.split(';') if s]
    for lam in sorted(ctx.sources, key=lambda l: ctx.n1(l)):
        if only and lam not in only:
            continue
        for aux in auxes:
            if ('A', aux, fmt(lam)) in DONE:
                continue
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
            if ('B', aux, '%s|%s' % (fmt(mn[0]), fmt(mn[1]))) in DONE:
                continue
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
        if g < 2 or ('E', str(tri)) in DONE:
            continue
        lam, mn = tri[0], tri[1:]
        t0 = time.time(); out = []
        for k in range(2, g + 1):
            for l in range(2, g + 1):
                if k * ctx.N1[lam] * l * ctx.K[mn] > args.emax:
                    out.append('%dx%d:skip' % (k, l)); continue
                dims, ex = ctx.block_rank([(lam, k)], [(mn, l)])
                out.append('%dx%d:%s%s' % (k, l, '/'.join(map(str, dims)), '' if ex else '(inexact)'))
                for i in range(len(dims) - 1):
                    if dims[i] < dims[i + 1]:
                        line = '*** SEPARATES r%d<r%d famE %s g=%d k=%d l=%d %s ranks %s exact=%s' % (ranks[i], ranks[i + 1], tri, g, k, l, '/'.join(map(str, dims)), '/'.join(map(str, ranks)), ex)
                        print(line); FOUND.append(line)
        print('famE %s g=%d dims=(%d,%d) %s (%.1fs)' % (tri, g, ctx.n1(lam), ctx.n23(mn), ' '.join(out), time.time() - t0))
        sys.stdout.flush()
        ctx.drop([tri])
for i in range(len(ranks) - 1):
    nnew = sum(v[0] for k, v in NHITS.items() if k[3] == i); nold = sum(v[1] for k, v in NHITS.items() if k[3] == i)
    nsing = sum(1 for s in SEPSINGLE if s[3] == i)
    print('n=%s d=%d rank %d vs %d total %.0fs: separating singles %d, NEW combined hits %d (printed: first %d per lattice), hits containing a separating single %d'
          % (args.n, args.d, ranks[i], ranks[i + 1], time.time() - T0, nsing, nnew - nsing, MAXPRINT, nold))
print('FOUND (printed lines): %d' % len(FOUND))
