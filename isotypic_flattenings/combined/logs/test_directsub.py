# check: fam.dims (new float64 work array) == old np.vstack + modrank, and == the incremental walk (fam.enumerate), on
# family-B lattices of C^4, d = 6, ranks 6, 7 (several members, not direct-sum certified)
import sys, itertools, numpy as np
sys.path.insert(0, '/home/user/claude/isotypic_flattenings/combined')
from combflat import Context, LatticeFamily, modrank, EXTRA
ctx = Context((4, 4, 4), 6, [6, 7], seed=5, cache=None, verbose=False)
ntarg = nsub = 0
for mn in sorted(ctx.targets, key=lambda mn: -len([t for t in ctx.g if t[1:] == mn]))[:6]:
    fam = LatticeFamily(ctx, 'B', mn, aux=1, levels='ends'); fam.build()
    ms = fam.members
    if len(ms) < 4: continue
    ntarg += 1
    for lev in ('full', 1):
        walk = {}
        fam.enumerate(lev, maxmembers=14, callback=lambda S, d: walk.__setitem__(tuple(sorted(S, key=repr)), d), maxsize=3)
        sel = [fam.full(x) if lev == 'full' else (x, 1) for x in ms]
        for k in (1, 2, 3):
            for Sx in itertools.combinations(sel, k):
                key = tuple(sorted(Sx, key=repr))
                new = fam.dims(Sx)
                c = min(fam.ncols, sum(max(fam._dims[(s,)]) for s in key) + EXTRA)
                old = tuple(modrank(np.vstack([fam.mats[r][s][:, :c] for s in key])) for r in ctx.ranks)
                assert new == old == walk[key], (mn, Sx, new, old, walk[key])
                nsub += 1
print('ok: %d targets, %d subsets: new dims == old dims == walk' % (ntarg, nsub))
