"""Natural candidates for the separating 1-dim U of the d=8 hit ((6,2),(3,2,2,1),(3,2,2,1)), direction 1:
K_S = {phi in M^* : phi(iso_lam(S^{(x)8})) = 0} for special tensors S.  For each K_S of dimension >= 1, the ranks of
F_phi on two rank-6 and two rank-7 tensors for random phi in K_S (generic phi in M^*: 225/225)."""
import sys, numpy as np
import hwv, hwv_fast
hwv.flattening_matrix = hwv_fast.flattening_matrix_fast
from hwv import p, dim_schur, random_fillings, random_gs
from isoflat import modrank, kronecker
from specialU import nullspace

lam = ((6, 2), (3, 2, 2, 1), (3, 2, 2, 1))
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 17)
n = 4; g = kronecker(*lam); n1 = dim_schur(lam[0], n); N1 = K = n1 + 4
gs = random_gs(rng, n, N1, K)
tens = {'r6a': 6, 'r6b': 6, 'r7a': 7, 'r7b': 7}
vecs = {k: tuple(rng.integers(0, p, (r, n)) for _ in range(3)) for k, r in tens.items()}
fills = []
while len(fills) < g:
    f = random_fillings(rng, lam)
    F = hwv.flattening_matrix(lam, f, vecs['r7a'], gs)
    if F.any() and modrank(np.array([x[1].ravel() for x in fills] + [F.ravel()])) == len(fills) + 1:
        fills.append((f, F))
Fb = {k: [hwv.flattening_matrix(lam, f, vecs[k], gs) for f, _ in fills] for k in tens}
comb = lambda k, c: sum(int(x) * F for x, F in zip(c, Fb[k])) % p
print('generic phi:', [modrank(comb(k, rng.integers(1, p, g))) for k in tens]); sys.stdout.flush()
E = np.eye(4, dtype=np.int64); ij = lambda i, j: E[2 * i + j]
def rank1_sum(*terms):
    return tuple(np.array([t[s] for t in terms], dtype=np.int64) % p for s in range(3))
e = E
special = {
    'unit4 <4>': rank1_sum(*[(e[i], e[i], e[i]) for i in range(4)]),
    'unit3 <3>': rank1_sum(*[(e[i], e[i], e[i]) for i in range(3)]),
    'M2 (2x2 matmult)': rank1_sum(*[(ij(i, j), ij(j, k), ij(k, i)) for i in range(2) for j in range(2) for k in range(2)]),
    'W-state': rank1_sum((e[0], e[0], e[1]), (e[0], e[1], e[0]), (e[1], e[0], e[0])),
    'random rank 4': rank1_sum(*[tuple(rng.integers(0, p, 4) for _ in range(3)) for _ in range(4)]),
    'random rank 5': rank1_sum(*[tuple(rng.integers(0, p, 4) for _ in range(3)) for _ in range(5)]),
}
for nm, S in special.items():
    FS = [hwv.flattening_matrix(lam, f, S, gs) for f, _ in fills]
    KS = nullspace(np.array([F.ravel() for F in FS]).T % p)
    line = 'S = %-18s dim K_S = %d' % (nm, len(KS))
    if len(KS):
        for trial in range(2):
            phi = (rng.integers(1, p, len(KS)) @ KS) % p
            line += ' | random phi in K_S: ranks r6a,r6b,r7a,r7b = %s' % [modrank(comb(k, phi)) for k in tens]
    print(line); sys.stdout.flush()
