"""Koszul flattenings (large projections) and degree-2 isotypic flattenings of the isotypic tensor, all components,
using the fast evaluator.  usage: python3 koszul_fast.py n d r_low,r_high maxprod [KBUDGET]"""
import numpy as np, sys, time, itertools, os
import hwv, hwv_fast
hwv.flattening_matrix = hwv_fast.flattening_matrix_fast
from hwv import *
from isoflat import modrank
import koszul, schur2
n = int(sys.argv[1]); d = int(sys.argv[2]); rl, rh = [int(x) for x in sys.argv[3].split(',')]
maxprod = float(sys.argv[4]) if len(sys.argv) > 4 else 3e6
rng = np.random.default_rng(61)
DONE = set()
for lf in os.environ.get('RESUME', '').split(':'):
    if lf and os.path.exists(lf):
        DONE |= {l.split(' g=')[0] for l in open(lf) if l.startswith('lam=') and 'SKIPPED' not in l}
WK, NW = [int(x) for x in os.environ.get('WORKER', '0/1').split('/')]
ci = -1
for lam in itertools.combinations_with_replacement(partitions(d, n), 3):
    g = kronecker(*lam)
    if g == 0: continue
    ci += 1
    if ci % NW != WK: continue
    if ('lam=%s' % (lam,)) in DONE: continue
    dims = tuple(dim_schur(l, n) for l in lam)
    cost = koszul.kwedge_cost(dims) if koszul.KWEDGE else np.prod([min(x + 2, koszul.GCAP) if koszul.GCAP else x + 2 for x in dims])
    if cost > maxprod:
        print("lam=%s dims=%s SKIPPED (size)" % (lam, dims)); sys.stdout.flush(); continue
    t0 = time.time()
    try: line = koszul.analyse(lam, n, rl, rh, rng, pks=(1, 2))
    except Exception as ex: line = "lam=%s ERROR %r" % (lam, ex)
    print(line + " (%.0fs)" % (time.time() - t0)); sys.stdout.flush()
    if os.environ.get('DEG2', '0') == '1':
        t0 = time.time()
        try: line = schur2.analyse(lam, n, rl, rh, rng)
        except Exception as ex: line = "lam=%s DEG2 ERROR %r" % (lam, ex)
        print(line + " (%.0fs)" % (time.time() - t0)); sys.stdout.flush()
