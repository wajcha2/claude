"""test_comb.py -- validation of combflat.py.   usage: python3 test_comb.py [quick|full]
 1. lattice families A and B (full Kronecker space) == brute force (brute.py) on all singletons, the full set and
    random subsets: n = 2 (d = 3, 4, 5), n = 3 (d = 3; family A also d = 4);
 2. family A, full set of targets == dim S_lam(C^{min(r, n)}) (it is S_lam(T_A)) for every lam and r = 1..n+1;
 3. assembled block matrices (generic Psi) == lattice dimensions, families A and B, k/l = 1 and full;
 4. single components reproduce known isotypic ranks: C^3 d = 5 rank 4 vs 5 (RESULTS.md: 3/6, 12/15, V 15/21),
    and (full) C^4 d = 8 ((6,2),(3,2,2,1),(3,2,2,1)) H 304/309, ((5,3),(3,3,1,1),(3,3,1,1)) V 252/254."""
import sys, os, itertools, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from combflat import Context, LatticeFamily, p
from brute import Brute
from hwv import dim_schur

MODE = sys.argv[1] if len(sys.argv) > 1 else 'quick'
fails = 0
def check(name, a, b):
    global fails
    ok = a == b
    fails += not ok
    print('%-90s %s %s' % (name, 'ok  ' if ok else 'FAIL', '' if ok else '%s != %s' % (a, b))); sys.stdout.flush()

def subsets(members, rng, nrand=6):
    out = [[m] for m in members] + [list(members)]
    for _ in range(nrand):
        k = int(rng.integers(2, max(3, len(members))))
        out.append([members[i] for i in rng.choice(len(members), size=min(k, len(members)), replace=False)])
    return out

def test_brute(n, d, ranks, fams='AB'):
    ctx = Context(n, d, ranks, seed=3, verbose=False)
    rng = np.random.default_rng(7)
    br = {r: Brute(ctx.vecs[r], d) for r in ranks}
    t0 = time.time()
    if 'A' in fams:
        for lam in ctx.sources:
            fam = LatticeFamily(ctx, 'A', lam, levels='full')
            for S in subsets(fam.members, rng):
                got = fam.dims([fam.full(m) for m in S])
                want = tuple(br[r].rank_A(lam, S) for r in ranks)
                check('brute n=%d d=%d A %s %s' % (n, d, lam, fam.describe([fam.full(m) for m in S]))[:90], got, want)
    if 'B' in fams:
        for mn in ctx.targets:
            fam = LatticeFamily(ctx, 'B', mn, levels='full')
            for S in subsets(fam.members, rng):
                got = fam.dims([fam.full(m) for m in S])
                want = tuple(br[r].rank_B(mn, S) for r in ranks)
                check('brute n=%d d=%d B %s %s' % (n, d, mn, fam.describe([fam.full(m) for m in S]))[:90], got, want)
    print('# brute n=%d d=%d: %.1fs' % (n, d, time.time() - t0))

def test_schur_functor(n, d):
    ranks = list(range(1, n + 2))
    ctx = Context(n, d, ranks, seed=4, verbose=False)
    for lam in ctx.sources:
        fam = LatticeFamily(ctx, 'A', lam, levels='full')
        got = fam.dims([fam.full(m) for m in fam.members])
        want = tuple(dim_schur(lam, min(r, n)) if len(lam) <= min(r, n) else 0 for r in ranks)
        check('S_lam(T_A) n=%d d=%d lam=%s ranks %s' % (n, d, lam, ranks), got, want)

def test_assembly(n, d, ranks):
    ctx = Context(n, d, ranks, seed=5, verbose=False)
    rng = np.random.default_rng(8)
    for lam in ctx.sources[:4]:
        for lev in ('full', 'one'):
            fam = LatticeFamily(ctx, 'A', lam, levels='ends')
            S = list(fam.members)[:max(1, len(fam.members) // 2)]
            sel = [(m, fam.gm[m] if lev == 'full' else 1) for m in S]
            cols = [(m, l) for m, l in sel]
            got, ex = ctx.block_rank([(lam, 1)], cols)
            check('assembly A %s %s exact=%s' % (lam, fam.describe(sel), ex), got, fam.dims(sel))
        fam2 = LatticeFamily(ctx, 'A', lam, aux=2, levels='ends')
        S = list(fam2.members)[:3]
        sel = [(m, 1) for m in S]
        got, ex = ctx.block_rank([(lam, 2)], [(m, 1) for m in S])
        check('assembly A aux=2 %s %s exact=%s' % (lam, fam2.describe(sel), ex), got, fam2.dims(sel))
    for mn in sorted(ctx.targets, key=lambda mn: -sum(1 for lam in ctx.sources if (lam,) + mn in ctx.g))[:4]:
        fam = LatticeFamily(ctx, 'B', mn, levels='ends')
        S = list(fam.members)
        sel = [(m, fam.gm[m]) for m in S]
        got, ex = ctx.block_rank([(m, k) for m, k in sel], [(mn, 1)])
        check('assembly B %s %s exact=%s' % (mn, fam.describe(sel), ex), got, fam.dims(sel))
        fam2 = LatticeFamily(ctx, 'B', mn, aux=2, levels='ends')
        sel = [(m, 1) for m in fam2.members]
        got, ex = ctx.block_rank([(m, 1) for m in fam2.members], [(mn, 2)])
        check('assembly B aux=2 %s %s exact=%s' % (mn, fam2.describe(sel), ex), got, fam2.dims(sel))

def test_known():
    ctx = Context(3, 5, [4, 5], seed=5, verbose=False)
    for tri, want in [(((3, 1, 1), (2, 2, 1), (2, 2, 1)), (3, 6)), (((3, 2), (3, 1, 1), (2, 2, 1)), (12, 15)),
                      (((3, 2), (3, 1, 1), (3, 1, 1)), (12, 15))]:
        got, ex = ctx.block_rank([(tri[0], 1)], [(tri[1:], 1)])
        check('known C^3 d=5 %s g1 exact=%s' % (tri, ex), got, want)
    tri = ((3, 2), (3, 1, 1), (3, 1, 1))
    got, ex = ctx.block_rank([(tri[0], 2)], [(tri[1:], 1)])
    check('known C^3 d=5 %s V2 exact=%s' % (tri, ex), got, (15, 21))
    if MODE == 'full':
        ctx = Context(4, 8, [6, 7], seed=5, verbose=False)
        tri = ((6, 2), (3, 2, 2, 1), (3, 2, 2, 1))
        got, ex = ctx.block_rank([(tri[0], 1)], [(tri[1:], 4)])
        check('known C^4 d=8 %s H4 exact=%s' % (tri, ex), got, (304, 309))
        tri = ((5, 3), (3, 3, 1, 1), (3, 3, 1, 1))
        got, ex = ctx.block_rank([(tri[0], 2)], [(tri[1:], 1)])
        check('known C^4 d=8 %s V2 exact=%s' % (tri, ex), got, (252, 254))

t0 = time.time()
test_known()
test_schur_functor(2, 4); test_schur_functor(3, 4); test_schur_functor(4, 4)
if MODE == 'full':
    test_schur_functor(3, 5); test_schur_functor(4, 5)
test_brute(2, 3, [1, 2, 3]); test_brute(2, 4, [1, 2, 3]); test_brute(3, 3, [2, 3, 4, 5])
if MODE == 'full':
    test_brute(2, 5, [1, 2, 3]); test_brute(3, 4, [3, 4, 5], fams='A')
test_assembly(3, 5, [4, 5]); test_assembly(4, 5, [6, 7])
print('%d failures, %.0fs' % (fails, time.time() - t0))
