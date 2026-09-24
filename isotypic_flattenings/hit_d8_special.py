import numpy as np, sys
import hwv, hwv_fast
hwv.flattening_matrix = hwv_fast.flattening_matrix_fast
import pencil, plane
lam = ((6, 2), (3, 2, 2, 1), (3, 2, 2, 1))
rng = np.random.default_rng(5)
print("--- line (pencil) analysis, direction 1"); sys.stdout.flush()
pencil.analyse(lam, 4, 6, 7, rng, 0)
print("--- plane analysis, direction 1"); sys.stdout.flush()
print(plane.analyse(lam, 4, 6, 7, rng, 0)[:600])
