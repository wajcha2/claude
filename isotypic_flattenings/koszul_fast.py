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
for lam in itertools.combinations_with_replacement(partitions(d, n), 3):
    g = kronecker(*lam)
    if g == 0: continue
    dims = tuple(dim_schur(l, n) for l in lam)
    if np.prod([x + 2 for x in dims]) > maxprod:
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
