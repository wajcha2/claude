import sys
sys.path.insert(0, '/home/user/claude/isotypic_flattenings/combined')
from combflat import Context, LatticeFamily
for ns, d, ranks, dirn in [((4, 4, 4), 6, [5, 6, 7], 0), ((4, 5, 5), 6, [8, 9], 1)]:
    ctx = Context(ns, d, ranks, seed=5, dirn=dirn, cache='live/cache', auxmax=1, verbose=False)
    for kind in ('B', 'A'):
        keys = sorted(ctx.targets, key=lambda mn: ctx.K[mn])[:12] if kind == 'B' else sorted(ctx.sources, key=lambda l: ctx.n1(l))[:6]
        bad = ok = 0
        for key in keys:
            fam = LatticeFamily(ctx, kind, key, aux=1, levels='ends')
            for m in fam.members:
                if fam.gm[m] < 2: continue
                a = fam.dims([fam.full(m)]); b = fam.dims([(m, 1), fam.full(m)])
                if a == b: ok += 1
                else: bad += 1; print('NOT NESTED', ns, d, kind, key, m, a, b)
        print(ns, d, kind, 'nested', ok, 'not nested', bad); sys.stdout.flush()
