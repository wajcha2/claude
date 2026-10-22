"""test_kp.py -- validation of the random-projection levels used by kp_search.py.   usage: python3 test_kp.py [quick|full]
 1. single components at every level s = 1..g (LatticeFamily levels='all') == directly assembled block matrices with an
    independent generic Psi of shape (g, 1, s) (H_s, family A) or (g, s, 1) (V_s, family B);
 2. random mixed-level sums (families A and B, 4x5x5 d = 6 in both directions, 5x5x5 d = 6) == assembled block matrices;
 3. known values: C^3 d=5 ((3,2),(3,1,1),(3,1,1)) g=2: H1 12/15, V2 15/21;  (full) C^4 d=8 ((6,2),(3,2,2,1),(3,2,2,1))
    g=4: H1 225/225 and H_s 304/309 for s = 2, 3, 4 (PROGRESS.md: 'any generic U of dim >= 2 gives 304/309');
 4. kpE sanity: a rank-1 Psi in a k x l grid gives k * rank(gN) (k <= l); a generic pencil (s = 2) of k x k matrices gives
    k * rank(gN) (simultaneous diagonalisation); a 2 x 3 grid with s = 2 is the L_2 pencil [[F1, F2, 0], [0, F1, F2]],
    compared with that matrix assembled by hand;
 5. the exhaustive level-vector walk of kp_search (incremental RREF) == fam.dims on every node (small lattices)."""
import sys, os, itertools, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from combflat import Context, LatticeFamily, p, mulmod, rref, reduce_rows, compressed_rank, combine
from isoflat import modrank

MODE = sys.argv[1] if len(sys.argv) > 1 else 'quick'
fails = 0
def check(name, a, b):
    global fails
    ok = a == b
    fails += not ok
    print('%-100s %s %s' % (name[:100], 'ok  ' if ok else 'FAIL', '' if ok else '%s != %s' % (a, b))); sys.stdout.flush()

def test_levels(ctx, ntri, rng):
    big = sorted([t for t in ctx.g if ctx.g[t] >= 3], key=lambda t: ctx.N1[t[0]] * ctx.K[t[1:]])[:ntri]   # intermediate levels
    two = [t for t in ctx.g if ctx.g[t] == 2]
    tris = big + [two[i] for i in rng.choice(len(two), min(2, len(two)), replace=False)]
    for tri in tris:
        lam, mn = tri[0], tri[1:]; g = ctx.g[tri]
        fa = LatticeFamily(ctx, 'A', lam, levels='all', members=[mn])
        fb = LatticeFamily(ctx, 'B', mn, levels='all', members=[lam])
        for s in range(1, g + 1):
            got, ex = ctx.block_rank([(lam, 1)], [(mn, s)], tag=3)
            check('H_%d %s dir%d exact=%s' % (s, tri, ctx.dirn, ex), fa.dims([(mn, s)]), got)
            got, ex = ctx.block_rank([(lam, s)], [(mn, 1)], tag=3)
            check('V_%d %s dir%d exact=%s' % (s, tri, ctx.dirn, ex), fb.dims([(lam, s)]), got)
        ctx.drop()

def psis_from(fam, S):
    """the Psi arrays the lattice uses (ctx.psi with the family's shapes), sliced to the chosen levels."""
    ctx = fam.ctx; out = {}
    for m, lev in S:
        tri = fam.tri(m); top = max(fam.levels[m])
        if fam.kind == 'A':
            out[(fam.key, m)] = ctx.psi(tri, 1, top, fam.tag)[:, :, :lev]
        else:
            out[(m, tuple(fam.key))] = ctx.psi(tri, top, 1, fam.tag)[:, :lev, :]
    return out

def test_mixed(ctx, nlat, nsub, rng):
    lams = [l for l in ctx.sources if max(ctx.g[t] for t in ctx.g if t[0] == l) >= 2]
    for lam in [lams[i] for i in rng.choice(len(lams), min(nlat, len(lams)), replace=False)]:
        mem = [mn for mn in ctx.targets if (lam,) + mn in ctx.g]
        mem = [mem[i] for i in rng.choice(len(mem), min(8, len(mem)), replace=False)]
        fam = LatticeFamily(ctx, 'A', lam, levels='all', members=mem)
        for _ in range(nsub):
            S = [(m, int(rng.integers(1, fam.gm[m] + 1))) for m in mem if rng.random() < 0.6] or [(mem[0], fam.gm[mem[0]])]
            got, ex = ctx.block_rank([(lam, 1)], [(m, l) for m, l in S], psis=psis_from(fam, S))
            check('mixed A dir%d %s exact=%s' % (ctx.dirn, fam.describe(S), ex), fam.dims(S), got)
        ctx.drop()
    mns = sorted([mn for mn in ctx.targets if max(ctx.g[t] for t in ctx.g if t[1:] == mn) >= 2], key=lambda mn: ctx.K[mn])[:3 * nlat]
    for mn in [mns[i] for i in rng.choice(len(mns), min(nlat, len(mns)), replace=False)]:
        fam = LatticeFamily(ctx, 'B', mn, levels='all')
        for _ in range(nsub):
            S = [(m, int(rng.integers(1, fam.gm[m] + 1))) for m in fam.members if rng.random() < 0.6] or [(fam.members[0], 1)]
            got, ex = ctx.block_rank([(m, l) for m, l in S], [(mn, 1)], psis=psis_from(fam, S))
            check('mixed B dir%d %s|%s %s exact=%s' % (ctx.dirn, mn[0], mn[1], fam.describe(S), ex), fam.dims(S), got)
        ctx.drop()

def test_known():
    ctx = Context(3, 5, [4, 5], seed=5, verbose=False)
    tri = ((3, 2), (3, 1, 1), (3, 1, 1))
    fa = LatticeFamily(ctx, 'A', tri[0], levels='all', members=[tri[1:]])
    fb = LatticeFamily(ctx, 'B', tri[1:], levels='all', members=[tri[0]])
    check('known C^3 d=5 %s H1' % (tri,), fa.dims([(tri[1:], 1)]), (12, 15))
    check('known C^3 d=5 %s V2' % (tri,), fb.dims([(tri[0], 2)]), (15, 21))
    if MODE == 'full':
        ctx = Context(4, 8, [6, 7], seed=5, verbose=False)
        tri = ((6, 2), (3, 2, 2, 1), (3, 2, 2, 1))
        fa = LatticeFamily(ctx, 'A', tri[0], levels='all', members=[tri[1:]])
        for s, want in [(1, (225, 225)), (2, (304, 309)), (3, (304, 309)), (4, (304, 309))]:
            check('known C^4 d=8 %s H_%d' % (tri, s), fa.dims([(tri[1:], s)]), want)

def test_grid(ctx, rng):
    tris = sorted([t for t in ctx.g if ctx.g[t] >= 3], key=lambda t: ctx.N1[t[0]] * ctx.K[t[1:]])[:3]
    for tri in tris:
        lam, mn = tri[0], tri[1:]; g = ctx.g[tri]
        gN = ctx.block_rank([(lam, 1)], [(mn, 1)])[0]
        for k, l in [(2, 2), (2, 3), (3, 3)]:
            Psi = mulmod(rng.integers(0, p, (g, 1)), rng.integers(0, p, (1, k * l))).reshape(g, k, l)
            got = ctx.block_rank([(lam, k)], [(mn, l)], psis={(lam, mn): Psi})[0]
            check('grid rank-1 %dx%d %s' % (k, l, tri), got, tuple(min(k, l) * x for x in gN))
        for k in (2, 3):
            Psi = mulmod(rng.integers(0, p, (g, 2)), rng.integers(0, p, (2, k * k))).reshape(g, k, k)
            got = ctx.block_rank([(lam, k)], [(mn, k)], psis={(lam, mn): Psi})[0]
            check('grid pencil %dx%d s=2 %s' % (k, k, tri), got, tuple(k * x for x in gN))
        # L_2 pencil by hand: phi1, phi2 generic in M^*
        phi = rng.integers(0, p, (g, 2))
        Psi = np.zeros((g, 2, 3), dtype=np.int64)
        Psi[:, 0, 0] = phi[:, 0]; Psi[:, 0, 1] = phi[:, 1]; Psi[:, 1, 1] = phi[:, 0]; Psi[:, 1, 2] = phi[:, 1]
        got = ctx.block_rank([(lam, 2)], [(mn, 3)], psis={(lam, mn): Psi})[0]
        want = []
        for r in ctx.ranks:
            Fs = ctx.flats(tri, r)
            F1, F2 = combine(phi[:, 0], Fs), combine(phi[:, 1], Fs); Z = np.zeros_like(F1)
            want.append(compressed_rank(np.block([[F1, F2, Z], [Z, F1, F2]]), np.random.default_rng(1)))
        check('grid L_2 pencil 2x3 %s' % (tri,), got, tuple(want))
        Psi = mulmod(rng.integers(0, p, (g, 2)), rng.integers(0, p, (2, 6))).reshape(g, 2, 3)
        got2 = ctx.block_rank([(lam, 2)], [(mn, 3)], psis={(lam, mn): Psi})[0]
        check('grid generic 2x3 s=2 == L_2 %s' % (tri,), got2, tuple(want))

def test_walk(ctx, rng):
    """kp_search's exhaustive walk on a few small lattices: every node == fam.dims."""
    from kplib import add_basis
    for mn in sorted([mn for mn in ctx.targets if max(ctx.g[t] for t in ctx.g if t[1:] == mn) >= 2], key=lambda mn: ctx.K[mn])[:2]:
        fam = LatticeFamily(ctx, 'B', mn, levels='all')
        ms = fam.members[:5]; nodes = [0]; bad = [0]
        def dfs(i, cur, S):
            for j in range(i, len(ms)):
                m = ms[j]; c = cur
                for lev in range(1, fam.gm[m] + 1):
                    c = {r: add_basis(*c[r], fam.basis_rows(r, (m, lev))) for r in ctx.ranks}
                    S2 = S + [(m, lev)]
                    nodes[0] += 1
                    if tuple(len(c[r][1]) for r in ctx.ranks) != fam.dims(S2):
                        bad[0] += 1
                    dfs(j + 1, c, S2)
        dfs(0, {r: (np.zeros((0, fam.size), dtype=np.float32), []) for r in ctx.ranks}, [])
        check('walk B %s|%s: %d nodes, mismatches' % (mn[0], mn[1], nodes[0]), bad[0], 0)
        ctx.drop()

t0 = time.time()
rng = np.random.default_rng(11)
test_known()
for ns, ranks, dirs in [((4, 5, 5), [8, 9], (0, 1)), ((5, 5, 5), [9, 10], (0,))]:
    for dirn in dirs:
        ctx = Context(ns, 6, ranks, seed=7, dirn=dirn, verbose=False)
        test_levels(ctx, 4 if MODE == 'quick' else 10, rng)
        test_mixed(ctx, 2 if MODE == 'quick' else 4, 4, rng)
        if dirn == 0:
            test_grid(ctx, rng)
            test_walk(ctx, rng)
print('%d failures, %.0fs' % (fails, time.time() - t0))
