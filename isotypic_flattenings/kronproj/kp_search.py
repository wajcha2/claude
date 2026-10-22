"""kp_search.py -- RANDOM PROJECTIONS OF THE KRONECKER SPACES in isotypic and combined isotypic flattenings.

usage: python3 kp_search.py n d r_1,r_2[,..] [options]        (separations r_i vs r_{i+1}; n = 5 or 4,5,5)

Setting and evaluation as in combflat.py (copied unchanged from combined/ of the 'combined flattenings' agent): T^{(x)d}
= sum S_lam A (x) S_mu B (x) S_nu C (x) M_{lam mu nu}, M = Kronecker space (dim g).  A GL-equivariant flattening may
use any linear map on M (Schur's lemma: nothing else commutes with GL(A) x GL(B) x GL(C)), so its rank is a GL-invariant,
lower semicontinuous function of T for EVERY such map.  The combined-flattening agent uses, per block, either one
generic functional on M (level 1) or the whole M (level g) (comb_search.py: levels='ends').  Here every block uses a
RANDOM PROJECTION of M of rank s, 1 <= s <= g (s = 1: one generic functional, the same for H and V; s = g: whole M):
  kpA   fixed source lam, sum over a set of targets (mu_j, nu_j), block j = s_j generic functionals of M_j on the TARGET
        side: S_lam A^* -> (+)_j C^{s_j} (x) S_mu_j B (x) S_nu_j C.  A single member at level s = the H_s flattening.
        (All targets at s_j = g_j is S_lam(T_A), never separating; with s_j < g_j it is a different map.)
  kpB   fixed target (mu, nu), sum over a set of sources lam_i, block i = s_i generic functionals on the SOURCE side:
        (+)_i C^{s_i} (x) S_lam_i A^* -> S_mu B (x) S_nu C.  A single member at level s = the V_s flattening.
  kpE   single component, k x l grid (k, l >= 2): Psi = P Q with P: a random s-dim subspace of M^* (2 <= s < min(g, kl))
        and Q a generic tensor in C^s (x) C^k* (x) C^l, i.e. the block sum_t Q_t (x) F(phi_t) (pencil / net type; the
        agent's family E is the full-rank case s = min(g, kl)).  k = l, s = 2 is skipped (a generic pencil of square
        matrices is simultaneously diagonalisable: rank = k * rank of one generic functional).
  kpG   general block matrices: several sources AND several targets at once, X_i = C^{k_i}, Y_j = C^{l_j}, block (i, j) =
        a generic Psi_ij of rank s_ij <= min(g_ij, k_i l_j) (random configurations).
Levels are nested (combflat.LatticeFamily, levels='all'): level s of a member = the first s columns of one generic
Psi, so every level is a generic s-dim projection and sums over (member, level) are lattice dimensions.

Search per lattice (kpA, kpB): all singles (member, s), then
  * EXHAUSTIVE over all level vectors (s_m in 0..g_m for every member) when prod (g_m + 1) <= --exh, by a depth-first
    walk with one incremental RREF basis per rank (one reduction per node), else
  * uniform levels (s_m = min(s, g_m)) and codim-t levels (s_m = max(1, g_m - t)) over all members, all-but-one at
    every uniform level, every member lowered/removed from the full sum (s_m -> s < g_m, others full), natural groups at
    uniform levels, pairs with all level combinations (capped), random subsets with random levels, greedy growth over
    all (member, level) candidates.
Lattices whose members all have g = 1 are skipped (nothing beyond the agent's search).

Hit lines '*** SEPARATES [cls] r_lo<r_hi ...' with cls = I (some level strictly between 1 and g: NOT covered by the
combined agent), M (only levels 1 and g but mixed within one sum), E (ends only: their search space).  'NEW' = no
single (member, level) of the configuration separates on its own.  Every printed hit is re-checked by a direct rank
of the summed lattice matrices; exact=True means the sample sizes guarantee the exact rank (Context.exact).
Env PRIME=524269 switches the prime (verification).  Tensors: as sweep_fast.py / comb_search.py for the same seed."""
import sys, os, re, time, itertools, argparse
PRIME = int(os.environ.get('PRIME', '0'))
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import hwv, isoflat
if PRIME:
    hwv.p = isoflat.p = PRIME
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import combflat
from combflat import Context, LatticeFamily, fmt, p, rref, reduce_rows, mulmod, compressed_rank
from kplib import add_basis
from isoflat import modrank
assert p == (PRIME or 524287) and hwv.p == p and isoflat.p == p

ap = argparse.ArgumentParser()
ap.add_argument('n'); ap.add_argument('d', type=int); ap.add_argument('ranks')
ap.add_argument('--fam', default='A,B,E')
ap.add_argument('--dir', type=int, default=0, help='source factor (0, 1, 2); 4,5,5: 0 = the C^4 factor, 1 = a C^5 factor')
ap.add_argument('--seed', type=int, default=5)
ap.add_argument('--exh', type=float, default=20000, help='exhaustive level vectors when prod(g_m + 1) <= exh')
ap.add_argument('--exhB', type=float, default=0, help='separate exhaustive bound for kpB (default: --exh)')
ap.add_argument('--nrand', type=int, default=1500); ap.add_argument('--pairs', type=int, default=4000)
ap.add_argument('--greedy', type=int, default=2); ap.add_argument('--gcand', type=int, default=400,
                help='greedy: at most this many (member, level) candidates (random subset)')
ap.add_argument('--bmax', type=int, default=3000, help='skip kpB lattices whose compressed size exceeds this')
ap.add_argument('--amax', type=int, default=10 ** 9, help='skip kpA lattices with more members than this')
ap.add_argument('--emax', type=float, default=4e7); ap.add_argument('--kmax', type=int, default=3)
ap.add_argument('--gcount', type=int, default=0, help='kpG: number of random general block configurations')
ap.add_argument('--only-lam', default=''); ap.add_argument('--only-mn', default='')
ap.add_argument('--cache', default=os.path.join(os.path.dirname(os.path.abspath(__file__)), 'live', 'cache'))
ap.add_argument('--resume', default='')
args = ap.parse_args()
ns = tuple(int(x) for x in args.n.split(',')); ns = ns * 3 if len(ns) == 1 else ns
ranks = [int(x) for x in args.ranks.split(',')]
fams = args.fam.split(',')
exhB = args.exhB or args.exh
ctx = Context(ns, args.d, ranks, seed=args.seed, dirn=args.dir, cache=args.cache + ('_p%d' % p if PRIME else ''), auxmax=1)
gs = sorted(set(ctx.g.values()))
print('# kp_search n=%s d=%d ranks=%s seed=%d dir=%d fam=%s exh=%g p=%d: %d sources, %d targets, %d ordered components, g in %s'
      % (args.n, args.d, ranks, args.seed, args.dir, args.fam, args.exh, p, len(ctx.sources), len(ctx.targets), len(ctx.g), gs))
sys.stdout.flush()
NPAIR = len(ranks) - 1
FOUND = []
TOT = {}          # (pair, cls, new) -> count
MAXPRINT = 20

def lvcls(fam, S):
    """I: some level strictly between 1 and g; M: levels 1 and g mixed among members with g >= 2; E: otherwise."""
    kinds = set()
    for m, lev in S:
        g = fam.gm[m]
        if g >= 2:
            kinds.add('one' if lev == 1 else 'full' if lev == g else 'mid')
    return 'I' if 'mid' in kinds else 'M' if kinds >= {'one', 'full'} else 'E'

def canon(S):
    """nested levels: keep the highest level per member."""
    top = {}
    for m, lev in S:
        top[m] = max(lev, top.get(m, 0))
    return sorted(top.items(), key=repr)

class Searcher:
    def __init__(self, fam):
        self.fam = fam
        self.seen = set(); self.sepsingle = set(); self.nprint = {}; self.tested = 0
        self.best = (0, None, None)
        self.count = {}

    def head(self):
        fam = self.fam
        return 'kp%s %s=%s' % (fam.kind, 'lam' if fam.kind == 'A' else 'mn',
                               fmt(fam.key) if fam.kind == 'A' else '%s|%s' % (fmt(fam.key[0]), fmt(fam.key[1])))

    def note(self, S, dims, how, recheck=False):
        """record a tested configuration; report separations."""
        self.tested += 1
        drop = dims[-1] - dims[-2]
        if drop > self.best[0]:
            self.best = (drop, list(S), dims)
        if not any(dims[i] < dims[i + 1] for i in range(NPAIR)):
            return
        S = canon(S)
        key = tuple(map(repr, S))
        if key in self.seen:
            return
        self.seen.add(key)
        if recheck:
            d2 = self.fam.dims(S)
            if d2 != tuple(dims):
                print('# WARNING recheck mismatch %s %s %s' % (self.fam.describe(S), dims, d2)); sys.stdout.flush()
                dims = d2
                if not any(dims[i] < dims[i + 1] for i in range(NPAIR)):
                    return
        fam = self.fam
        cls = lvcls(fam, S)
        for i in range(NPAIR):
            if dims[i] >= dims[i + 1]:
                continue
            if len(S) == 1:
                self.sepsingle.add((i,) + tuple(map(repr, S[0])))
                new = True
            else:
                new = not any((i,) + tuple(map(repr, s)) in self.sepsingle for s in S)
            ck = (i, cls, new)
            self.count[ck] = self.count.get(ck, 0) + 1
            TOT[ck] = TOT.get(ck, 0) + 1
            pk = (i, cls)
            self.nprint[pk] = self.nprint.get(pk, 0) + 1
            if self.nprint[pk] > MAXPRINT and len(S) > 1:
                continue
            line = '*** SEPARATES%s [%s] r%d<r%d %s %s %s ranks %s exact=%s (%s)' % (
                ' NEW' if new and len(S) > 1 else '', cls, ranks[i], ranks[i + 1], self.head(), fam.describe(S),
                '/'.join(map(str, dims)), '/'.join(map(str, ranks)), fam.exact(S), how)
            print(line); sys.stdout.flush()
            FOUND.append(line)

    def test(self, S, how):
        S = canon(S)
        if not S:
            return None
        dims = self.fam.dims(S)
        self.note(S, dims, how)
        return dims

# ------------------------------------------------------------------------------------------------------------------
def exhaustive(sr, members):
    """every level vector (s_m in 0..g_m) over `members`, depth first; nested levels are added incrementally."""
    fam = sr.fam
    def dfs(i, cur, S):
        for j in range(i, len(members)):
            m = members[j]; c = cur
            for lev in range(1, fam.gm[m] + 1):
                c = {r: add_basis(*c[r], fam.basis_rows(r, (m, lev))) for r in ranks}
                S2 = S + [(m, lev)]
                sr.note(S2, tuple(len(c[r][1]) for r in ranks), 'exhaustive', recheck=True)
                dfs(j + 1, c, S2)
    dfs(0, {r: (np.zeros((0, fam.size), dtype=np.float32), []) for r in ranks}, [])

def greedy(sr, cands, rng):
    """grow a configuration one (member, level) at a time, maximising the top-pair drop (ties random); a member already
    in at level s can be raised (its lower levels are dropped from the candidates)."""
    fam = sr.fam
    cur = {r: (np.zeros((0, fam.size), dtype=np.float32), []) for r in ranks}
    S, rest = [], list(cands)
    while rest:
        best = None
        for c in rest:
            red = {r: reduce_rows(fam.basis_rows(r, c), *cur[r]) for r in ranks}
            dims = tuple(len(cur[r][1]) + (modrank(red[r]) if red[r].size else 0) for r in ranks)
            key = (dims[-1] - dims[-2], rng.random())
            if best is None or key > best[0]:
                best = (key, c, dims)
        _, c, dims = best
        for r in ranks:
            cur[r] = add_basis(*cur[r], fam.basis_rows(r, c))
        S.append(c)
        rest = [x for x in rest if not (x[0] == c[0] and x[1] <= c[1])]
        sr.note(S, tuple(len(cur[r][1]) for r in ranks), 'greedy', recheck=True)

def natural_groups(fam):
    G = {}
    for m in fam.members:
        if fam.kind == 'A':
            mu, nu = m
            G.setdefault('mu=%s' % fmt(mu), []).append(m); G.setdefault('nu=%s' % fmt(nu), []).append(m)
            G.setdefault('diag' if mu == nu else 'offdiag', []).append(m)
        else:
            G.setdefault('rows=%d' % len(m), []).append(m); G.setdefault('row1=%d' % m[0], []).append(m)
    return {k: v for k, v in G.items() if 1 < len(v) < len(fam.members)}

def search(fam, rng):
    sr = Searcher(fam)
    ms = fam.members; gm = fam.gm; gmax = max(gm.values())
    singles = {}
    for m in ms:
        singles[m] = [sr.test([(m, lev)], 'single') for lev in range(1, gm[m] + 1)]
    named = {}
    nvec = float(np.prod([gm[m] + 1 for m in ms], dtype=np.float64)) - 1
    bound = args.exh if fam.kind == 'A' else exhB
    if len(ms) > 1 and nvec <= bound:
        exhaustive(sr, ms)
        named['exhaustive'] = int(nvec)
        named['all'] = fam.dims([(m, gm[m]) for m in ms])
        return sr, singles, named
    if len(ms) == 1:
        return sr, singles, named
    named['all'] = sr.test([(m, gm[m]) for m in ms], 'all')
    for s in range(1, gmax):
        named['all:%d' % s] = sr.test([(m, min(s, gm[m])) for m in ms], 'uniform s=%d' % s)
        named['all:g-%d' % s] = sr.test([(m, max(1, gm[m] - s)) for m in ms], 'codim %d' % s)
    # every member lowered (s < g_m) or removed, the others at full level; all-but-one at every uniform level
    for m in ms:
        for s in range(0, gm[m]):
            sr.test([(x, gm[x]) for x in ms if x != m] + ([(m, s)] if s else []), 'full sum, %s at %d' % (fam.describe([(m, 1)])[1:-1].split(':')[0], s))
    for s in range(1, gmax):
        for m in ms:
            sr.test([(x, min(s, gm[x])) for x in ms if x != m], 'all-but-one s=%d' % s)
    for name, grp in natural_groups(fam).items():
        for s in range(1, gmax + 1):
            sr.test([(x, min(s, gm[x])) for x in grp], '%s s=%d' % (name, s))
    # pairs with all level combinations
    combos = [(a, la, b, lb) for a, b in itertools.combinations(ms, 2) for la in range(1, gm[a] + 1) for lb in range(1, gm[b] + 1)
              if gm[a] > 1 or gm[b] > 1]
    if len(combos) > args.pairs:
        combos = [combos[i] for i in rng.choice(len(combos), args.pairs, replace=False)]
    for a, la, b, lb in combos:
        sr.test([(a, la), (b, lb)], 'pair')
    for _ in range(args.nrand):
        k = int(rng.integers(2, len(ms) + 1))
        idx = rng.choice(len(ms), k, replace=False)
        sr.test([(ms[i], int(rng.integers(1, gm[ms[i]] + 1))) for i in idx], 'random')
    cands = [(m, lev) for m in ms for lev in range(1, gm[m] + 1)]
    for gi in range(args.greedy):
        cc = cands if len(cands) <= args.gcand else [cands[i] for i in sorted(rng.choice(len(cands), args.gcand, replace=False))]
        greedy(sr, cc, rng)
    return sr, singles, named

def summary(sr, singles, named, secs):
    fam = sr.fam
    sv = ' '.join('%s:%s' % (fam.describe([(m, fam.gm[m])])[1:-1].split(':')[0],
                             ','.join('/'.join(map(str, v)) for v in vals)) for m, vals in singles.items())
    nv = ' '.join('%s:%s' % (k, v if isinstance(v, int) else '/'.join(map(str, v))) for k, v in named.items() if v is not None)
    hits = ' '.join('r%d<r%d[%s]%s:%d' % (ranks[i], ranks[i + 1], c, '+new' if n else '', v) for (i, c, n), v in sorted(sr.count.items()))
    b = sr.best
    print('%s members=%d g=%s size=%d tested=%d maxdrop=%d%s hits: %s  singles(s=1..g): %s  named: %s  (%.1fs)'
          % (sr.head(), len(fam.members), ''.join(str(min(fam.gm[m], 9)) for m in fam.members), fam.size, sr.tested, b[0],
             '' if not b[0] else ' at %s %s' % (fam.describe(b[1]), '/'.join(map(str, b[2]))), hits or 'none', sv, nv, secs))
    sys.stdout.flush()

# ------------------------------------------------------------------------------------------------------------------
DONE = set()
for lf in args.resume.split(':'):
    if lf and os.path.exists(lf):
        for l in open(lf):
            m = re.match(r'kp([AB]) (?:lam|mn)=(\S+) (?:members=|SKIPPED)', l)
            if m:
                DONE.add((m.group(1), m.group(2)))
            elif l.startswith('kpE '):
                DONE.add(('E', l[4:].split(' g=')[0]))
            elif l.startswith('kpG done'):
                DONE.add(('G',))
if DONE:
    print('# resume: %d lattices / components already done' % len(DONE)); sys.stdout.flush()

T0 = time.time()
if 'A' in fams:
    only = [tuple(int(c) for c in s) for s in args.only_lam.split(';') if s]
    for lam in sorted(ctx.sources, key=lambda l: ctx.n1(l)):
        if (only and lam not in only) or ('A', fmt(lam)) in DONE:
            continue
        mem = [mn for mn in ctx.targets if (lam,) + mn in ctx.g]
        if max(ctx.g[(lam,) + mn] for mn in mem) < 2:
            print('kpA lam=%s SKIPPED (all %d members g = 1)' % (fmt(lam), len(mem))); sys.stdout.flush()
            continue
        if len(mem) > args.amax:
            print('kpA lam=%s SKIPPED (%d members > amax)' % (fmt(lam), len(mem))); sys.stdout.flush()
            continue
        t0 = time.time()
        fam = LatticeFamily(ctx, 'A', lam, aux=1, levels='all')
        res = search(fam, np.random.default_rng([args.seed, 31] + list(lam)))
        summary(*res, time.time() - t0)
        ctx.drop()
if 'B' in fams:
    def parse_mn(s):
        a, b = s.split('|')
        return tuple(tuple(int(c) for c in x) for x in (a, b))
    only = [parse_mn(s) for s in args.only_mn.split(';') if s]
    for mn in sorted(ctx.targets, key=lambda mn: ctx.K[mn]):
        name = '%s|%s' % (fmt(mn[0]), fmt(mn[1]))
        if (only and mn not in only) or ('B', name) in DONE:
            continue
        mem = [lam for lam in ctx.sources if (lam,) + mn in ctx.g]
        if max(ctx.g[(lam,) + mn] for lam in mem) < 2:
            print('kpB mn=%s SKIPPED (all %d members g = 1)' % (name, len(mem))); sys.stdout.flush()
            continue
        bound = min(ctx.K[mn] - 8, ctx.capB[mn])
        if bound + 8 > args.bmax:
            print('kpB mn=%s SKIPPED (compressed size %d > bmax %d; %d sources)' % (name, bound + 8, args.bmax, len(mem))); sys.stdout.flush()
            continue
        t0 = time.time()
        fam = LatticeFamily(ctx, 'B', mn, aux=1, levels='all')
        res = search(fam, np.random.default_rng([args.seed, 32] + list(mn[0]) + [0] + list(mn[1])))
        summary(*res, time.time() - t0)
        ctx.drop()
if 'E' in fams:
    for tri in sorted(ctx.g, key=lambda t: ctx.g[t] * ctx.N1[t[0]] * ctx.K[t[1:]]):
        g = ctx.g[tri]
        if g < 3 or ('E', str(tri)) in DONE:
            continue
        lam, mn = tri[0], tri[1:]
        t0 = time.time(); out = []
        rng = np.random.default_rng([args.seed, 33, args.dir] + ctx.tri_index(tri))
        for k in range(2, args.kmax + 1):
            for l in range(2, args.kmax + 1):
                for s in range(2, min(g, k * l)):
                    if k == l and s == 2:
                        continue
                    if k * ctx.N1[lam] * l * ctx.K[mn] > args.emax:
                        out.append('%dx%d/s%d:skip' % (k, l, s)); continue
                    P = rng.integers(0, p, (g, s)); Q = rng.integers(0, p, (s, k * l))
                    Psi = mulmod(P, Q).reshape(g, k, l)
                    dims, ex = ctx.block_rank([(lam, k)], [(mn, l)], psis={(lam, mn): Psi})
                    out.append('%dx%d/s%d:%s%s' % (k, l, s, '/'.join(map(str, dims)), '' if ex else '(inexact)'))
                    for i in range(NPAIR):
                        if dims[i] < dims[i + 1]:
                            line = '*** SEPARATES [I] r%d<r%d kpE %s g=%d k=%d l=%d s=%d %s ranks %s exact=%s' % (
                                ranks[i], ranks[i + 1], tri, g, k, l, s, '/'.join(map(str, dims)), '/'.join(map(str, ranks)), ex)
                            print(line); FOUND.append(line); sys.stdout.flush()
                            TOT[(i, 'I', True)] = TOT.get((i, 'I', True), 0) + 1
        print('kpE %s g=%d dims=(%d,%d) %s (%.1fs)' % (tri, g, ctx.n1(lam), ctx.n23(mn), ' '.join(out), time.time() - t0))
        sys.stdout.flush()
        ctx.drop([tri])
if 'G' in fams and args.gcount and ('G',) not in DONE:
    # random general block matrices: 2-3 sources x 2-3 targets with nonzero blocks, k_i, l_j in {1, 2}, ranks s_ij random
    rng = np.random.default_rng([args.seed, 34, args.dir])
    tris = list(ctx.g)
    ng = 0; t0 = time.time()
    while ng < args.gcount:
        t = tris[rng.integers(len(tris))]
        srcs = [t[0]]; tgts = [t[1:]]
        for _ in range(int(rng.integers(1, 3))):
            c = [lam for lam in ctx.sources if lam not in srcs and any((lam,) + mn in ctx.g for mn in tgts)]
            if c: srcs.append(c[rng.integers(len(c))])
        for _ in range(int(rng.integers(1, 3))):
            c = [mn for mn in ctx.targets if mn not in tgts and any((lam,) + mn in ctx.g for lam in srcs)]
            if c: tgts.append(c[rng.integers(len(c))])
        if len(srcs) < 2 or len(tgts) < 2:
            continue
        ks = {lam: int(rng.integers(1, 3)) for lam in srcs}; ls = {mn: int(rng.integers(1, 3)) for mn in tgts}
        if sum(ks[l] * ctx.N1[l] for l in srcs) * sum(ls[m] * ctx.K[m] for m in tgts) > args.emax:
            continue
        psis, desc = {}, []
        for lam in srcs:
            for mn in tgts:
                tri = (lam,) + mn
                if tri not in ctx.g:
                    continue
                g = ctx.g[tri]; s = int(rng.integers(1, min(g, ks[lam] * ls[mn]) + 1))
                psis[(lam, mn)] = mulmod(rng.integers(0, p, (g, s)), rng.integers(0, p, (s, ks[lam] * ls[mn]))).reshape(g, ks[lam], ls[mn])
                desc.append('%s>%s,%s:%d/%d' % (fmt(lam), fmt(mn[0]), fmt(mn[1]), s, g))
        dims, ex = ctx.block_rank([(l, ks[l]) for l in srcs], [(m, ls[m]) for m in tgts], psis=psis)
        ng += 1
        conf = 'rows %s cols %s blocks %s' % (' '.join('%s^%d' % (fmt(l), ks[l]) for l in srcs),
                                               ' '.join('%s,%s^%d' % (fmt(m[0]), fmt(m[1]), ls[m]) for m in tgts), ' '.join(desc))
        for i in range(NPAIR):
            if dims[i] < dims[i + 1]:
                line = '*** SEPARATES [G] r%d<r%d kpG %s %s ranks %s exact=%s' % (ranks[i], ranks[i + 1], conf, '/'.join(map(str, dims)), '/'.join(map(str, ranks)), ex)
                print(line); FOUND.append(line); sys.stdout.flush()
                TOT[(i, 'G', True)] = TOT.get((i, 'G', True), 0) + 1
        if ng % 50 == 0:
            print('# kpG %d configurations, %.0fs' % (ng, time.time() - t0)); sys.stdout.flush()
    print('kpG done %d configurations (%.1fs)' % (ng, time.time() - t0)); sys.stdout.flush()
for i in range(NPAIR):
    parts = ' '.join('[%s]%s:%d' % (c, 'new' if n else 'inherited', v) for (j, c, n), v in sorted(TOT.items()) if j == i)
    print('n=%s d=%d rank %d vs %d total %.0fs: hits %s' % (args.n, args.d, ranks[i], ranks[i + 1], time.time() - T0, parts or 'none'))
print('FOUND (printed lines): %d' % len(FOUND))
