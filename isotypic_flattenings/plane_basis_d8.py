"""Rank profiles of single fillings and of a basis of the separating plane, d=8 hit ((6,2),(3,2,2,1),(3,2,2,1)), direction 1.
Seed-5 basis P_0..P_3 of the HWV space (the fillings of hit_d8_special.py, printed by line_point_M2.py); separating plane
2c1 + c2 - c3 = 0 (plane_test_d8.py), phi_M2 = P_1 - 2 P_2.  Ranks on two rank-6 tensors, one rank-7 tensor and M2.
usage: python3 plane_basis_d8.py"""
import sys, numpy as np
import hwv, hwv_fast
hwv.flattening_matrix = hwv_fast.flattening_matrix_fast
from hwv import p, dim_schur, random_fillings, random_gs, flattening_matrix
from isoflat import modrank, kronecker
lam = ((6, 2), (3, 2, 2, 1), (3, 2, 2, 1))
rng = np.random.default_rng(5)
n = 4; n1 = dim_schur(lam[0], n); N1 = K = n1 + 4
gs = random_gs(rng, n, N1, K)
tens = {'low1': 6, 'low2': 6, 'high': 7}
vecs = {k: tuple(rng.integers(0, p, (r, n)) for _ in range(3)) for k, r in tens.items()}
g = kronecker(*lam); fills = []; tries = 0
while len(fills) < g and tries < 100 * g:
    f = random_fillings(rng, lam); tries += 1
    F = flattening_matrix(lam, f, vecs['high'], gs)
    if np.any(F) and modrank(np.array([x[1].ravel() for x in fills] + [F.ravel()])) == len(fills) + 1:
        fills.append((f, F))
E = np.eye(4, dtype=np.int64); ij = lambda i, j: E[2 * i + j]
vecs['M2'] = tuple(np.array([[ij(i, j), ij(j, k), ij(k, i)][s] for i in range(2) for j in range(2) for k in range(2)]) for s in range(3))
Fb = {k: [flattening_matrix(lam, f, v, gs) % p for f, _ in fills] for k, v in vecs.items()}
comb = lambda k, c: sum(int(x) * F for x, F in zip(c, Fb[k])) % p
print('seed-5 basis P_0..P_3; ranks on (rank-6 low1, rank-6 low2, rank-7 high, M2); separating plane: 2c1 + c2 - c3 = 0')
for c in [(1,0,0,0), (0,1,0,0), (0,0,1,0), (0,0,0,1), (0,1,-2,0), (0,0,1,1), (0,1,0,2), (1,1,-2,0)]:
    cc = np.array(c) % p
    print('c = %-14s 2c1+c2-c3 = %2d   ranks %s' % (c, 2*c[1] + c[2] - c[3], [modrank(comb(k, cc)) for k in ('low1', 'low2', 'high', 'M2')])); sys.stdout.flush()
print('F_1(M2) == 2 F_2(M2):', np.array_equal(Fb['M2'][1], (2 * Fb['M2'][2]) % p), '; ranks of F_j(M2):', [modrank(F) for F in Fb['M2']])
