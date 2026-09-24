"""specialU.py driven by the fast evaluator (hwv_fast), skipping (lam, dir) cases already present in RESUME logs.
usage: python3 specialU_fast.py n d r_low,r_high [resume_log]"""
import numpy as np, sys, time, itertools, os
import hwv, hwv_fast
hwv.flattening_matrix = hwv_fast.flattening_matrix_fast
from hwv import partitions, kronecker
import specialU
n = int(sys.argv[1]); d = int(sys.argv[2]); rl, rh = [int(x) for x in sys.argv[3].split(',')]
done = set()
if len(sys.argv) > 4 and os.path.exists(sys.argv[4]):
    for l in open(sys.argv[4]):
        if l.startswith('lam='): done.add(l.split(' g=')[0].split(' FAILED')[0])
rng = np.random.default_rng(23)
for lam in itertools.combinations_with_replacement(partitions(d, n), 3):
    if kronecker(*lam) == 0: continue
    for direction in range(3):
        key = "lam=%s dir=%d" % (lam, direction + 1)
        if key in done: continue
        t0 = time.time()
        try: line = specialU.analyse(lam, n, rl, rh, rng, direction)
        except AssertionError as e: line = key + " FAILED %s" % e
        print(line + "  (%.0fs)" % (time.time() - t0)); sys.stdout.flush()
