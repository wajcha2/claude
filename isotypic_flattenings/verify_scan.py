"""python3 verify_scan.py n d "lam" ranks [seed ...]      (env PRIME = other prime, default p of hwv.py)

Re-evaluates one component of rankscan.py with fresh random data: for each seed, new tensors of the given ranks,
new evaluation points, fillings and generic subspaces U_k; prints the H_k / V_k rank profiles of every direction
at every rank, so that a separation found by the scan can be confirmed (another seed, another prime)."""
import os, sys
import hwv, isoflat
if os.environ.get('PRIME'):
    hwv.p = isoflat.p = int(os.environ['PRIME'])          # before hwv_fast / rankscan import p
import numpy as np
import rankscan
from rankscan import Direction, distinct_dirs, generic_rank, word_minor_size

n, d = int(sys.argv[1]), int(sys.argv[2])
lam = tuple(tuple(x) for x in eval(sys.argv[3]))
ranks = [int(x) for x in sys.argv[4].split(',')]
seeds = [int(x) for x in sys.argv[5:]] or [7]
g = isoflat.kronecker(*lam)
print('# verify n=%d d=%d lam=%s g=%d p=%d ranks=%s seeds=%s' % (n, d, lam, g, hwv.p, ranks, seeds), flush=True)
for seed in seeds:
    vecs = {r: tuple(np.random.default_rng([seed, n, r, t, 99]).integers(0, hwv.p, (r, n)) for t in range(3)) for r in ranks}
    crng = np.random.default_rng([seed, n, d, 12345])
    for t in distinct_dirs(lam):
        D = Direction(n, lam, g, t, crng, vecs, max(ranks))
        prof = {r: D.profile(r) for r in ranks}
        print('seed %d dir %d (n1=%d n23=%d span=%d): ' % (seed, t + 1, D.n1, D.n23, D.span) +
              '  '.join('r%d H%s V%s' % (r, P['H'], P['V']) for r, P in prof.items()), flush=True)
