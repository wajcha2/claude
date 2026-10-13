"""V-stack candidate lists for C^5 rank 9 vs 10 (2026-10-13).

Components lam with Kronecker coefficient g >= 2 such that for some direction N the V-stack
U (x) S^{l_N}V^* -> S^{l_i}V (x) S^{l_j}V (U = M, dim g) is balanced:
    1/2 <= g * dim(l_N) / (dim(l_i) * dim(l_j)) <= 2.
All seven 4x4x4 rank 6 vs 7 V-only separators at d = 8 (rank-scan session) satisfy this; the H-shaped
'promising' filter of make_prom5.py rejects most of them.  Generic V-stacks for C^5 rank 9 vs 10 are already
checked at d <= 8 by the special-U agent (specialscan.py), so these lists start at d = 9.
Usage: python3 make_promV5.py d > promV5_d<d>.txt"""
import sys, itertools
from isoflat import partitions, kronecker
from hwv import dim_schur

d = int(sys.argv[1]); n = 5
out = []
for lam in itertools.combinations_with_replacement(partitions(d, n), 3):
    dims = [dim_schur(l, n) for l in lam]
    g = kronecker(*lam)
    if g < 2:
        continue
    for N in range(3):
        i, j = [t for t in range(3) if t != N]
        r = g * dims[N] / (dims[i] * dims[j])
        if 0.5 <= r <= 2:
            out.append(lam)
            break
for lam in out:
    print(repr(lam))
print('# d=%d: %d components' % (d, len(out)), file=sys.stderr)
