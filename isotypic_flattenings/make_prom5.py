"""python3 make_prom5.py d [n]  -> prints the 'promising' component list for (C^n)^3 in degree d, one repr(lam) per line,
in the order sweep_fast.py enumerates components (combinations_with_replacement of partitions(d, n)):
Kronecker coefficient g > 0, l1 with at most 2 rows, l2 and l3 with at least 4 rows,
dim S^{l1} >= dim S^{l2} * dim S^{l3} / 2.  Reproduces prom5_d12.txt (same criteria as the d7d8 agent's list)."""
import sys, itertools
from isoflat import partitions, kronecker
from hwv import dim_schur
d = int(sys.argv[1]); n = int(sys.argv[2]) if len(sys.argv) > 2 else 5
for lam in itertools.combinations_with_replacement(partitions(d, n), 3):
    l1, l2, l3 = lam
    if len(l1) > 2 or len(l2) < 4 or len(l3) < 4:
        continue
    d1, d2, d3 = (dim_schur(l, n) for l in lam)
    if 2 * d1 < d2 * d3:
        continue
    if kronecker(*lam) > 0:
        print(repr(lam))
