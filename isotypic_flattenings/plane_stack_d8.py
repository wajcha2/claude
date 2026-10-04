"""Do the separating functionals of the d=8 hit share a cokernel?  Seed-5 setup of hit_d8_special.py; phi_M2, phi_A as in
plane_test_d8.py.  For phi_1, phi_2 (and a third point given as filling-basis coordinates on the command line):
F_phi(T) has rows = N1 source points (S^{62}V^*), columns = K target points (S^{3221}V (x) S^{3221}V).
hstack [F_phi1 | F_phi2 | ...] has rank 360 - dim(common kernel) (the H-stack of sweep_fast: 304 on rank 6, 309 on rank 7
for U = M); vstack has rank dim(sum of the images) <= 225 (220 = all images in one 220-dim space, a common cokernel).
Ranks on rank-6 (low1, low2) and rank-7 (high) tensors, against random phi's.
usage: python3 plane_stack_d8.py [c0,c1,c2,c3]"""
import sys, numpy as np
import hwv, hwv_fast
hwv.flattening_matrix = hwv_fast.flattening_matrix_fast
from hwv import p, dim_schur, random_fillings, random_gs, flattening_matrix
from isoflat import modrank, kronecker
from specialU import nullspace

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
ca, cb = rng.integers(1, p, g), rng.integers(1, p, g)
E = np.eye(4, dtype=np.int64); ij = lambda i, j: E[2 * i + j]
vecs['M2'] = tuple(np.array([[ij(i, j), ij(j, k), ij(k, i)][s] for i in range(2) for j in range(2) for k in range(2)]) for s in range(3))
Fb = {k: [flattening_matrix(lam, f, v, gs) % p for f, _ in fills] for k, v in vecs.items()}
comb = lambda k, c: sum(int(x) * F for x, F in zip(c, Fb[k])) % p
phiM2 = nullspace(np.array([F.ravel() for F in Fb['M2']]).T % p)[0]
phis = {'phi_M2': phiM2, 'phi_A': (ca + 509492 * cb) % p}
if len(sys.argv) > 1:
    phis['phi_B'] = np.array([int(x) for x in sys.argv[1].split(',')]) % p
rng2 = np.random.default_rng(3)
def report(name, cs):
    h = [modrank(np.hstack([comb(k, c) for c in cs])) for k in tens]
    v = [modrank(np.vstack([comb(k, c) for c in cs])) for k in tens]
    print('%-28s hstack ranks (low1, low2, high) = %s, vstack ranks = %s' % (name, h, v)); sys.stdout.flush()
print('matrices: rows = %d source points, columns = %d target points (rank of one F_phi <= 225)' % Fb['high'][0].shape)
names = list(phis)
report(' + '.join(names[:2]), [phis[x] for x in names[:2]])
if len(names) > 2: report(' + '.join(names), [phis[x] for x in names])
report('2 random phi', [rng2.integers(1, p, g) for _ in range(2)])
report('3 random phi', [rng2.integers(1, p, g) for _ in range(3)])
