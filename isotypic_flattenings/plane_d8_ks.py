"""(K_S part of plane_d8.py, reusing its saved points.)  Is the locus of separating 1-dim U for the d=8 hit ((6,2),(3,2,2,1),(3,2,2,1)) (direction 1) a plane in P(M^*)?
For several random lines phi(t) = a + t b in M^* (filling-basis coordinates, g = 4): F_p-rational roots of the
tensor-independent rank-6 drop polynomial (pencil.py method), their rank profiles (rank-6, rank-6, rank-7), and the
rank of the span of all separating points (3 = they lie on a common projective plane).
usage: python3 plane_d8.py [nlines] [seed]"""
import sys, time, numpy as np
import hwv, hwv_fast
hwv.flattening_matrix = hwv_fast.flattening_matrix_fast
from hwv import p, dim_schur, random_fillings, random_gs
from isoflat import modrank, kronecker
import pencil
from pencil import drop_poly, roots_mod_p

lam = ((6, 2), (3, 2, 2, 1), (3, 2, 2, 1))
nlines = int(sys.argv[1]) if len(sys.argv) > 1 else 4
rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 5)
n = 4; g = kronecker(*lam); n1 = dim_schur(lam[0], n); N1 = K = n1 + 4
gs = random_gs(rng, n, N1, K)
tens = {'low1': 6, 'low2': 6, 'high': 7}
vecs = {k: tuple(rng.integers(0, p, (r, n)) for _ in range(3)) for k, r in tens.items()}
fills = []
while len(fills) < g:
    f = random_fillings(rng, lam)
    F = hwv.flattening_matrix(lam, f, vecs['high'], gs)
    if F.any() and modrank(np.array([x[1].ravel() for x in fills] + [F.ravel()])) == len(fills) + 1:
        fills.append((f, F))
pts = {k: list(v) for k, v in np.load('plane_d8_points.npy', allow_pickle=True).item().items()}
# kernels K_S = {phi in M^* : phi(iso_lam(S^{(x)8})) = 0} for special tensors S (natural planes?)
E = np.eye(4, dtype=np.int64); ij = lambda i, j: E[2 * i + j]
special = {
    'unit4': tuple(np.array([E[i] for i in range(4)]) for _ in range(3)),
    'M2': tuple(np.array([[ij(i, j), ij(j, k), ij(k, i)][s] for i in range(2) for j in range(2) for k in range(2)]) for s in range(3)),
    'W-type': (np.array([E[0], E[0], E[1]]), np.array([E[0], E[1], E[0]]), np.array([E[1], E[0], E[0]])),
}
from specialU import nullspace
for nm, S in special.items():
    FS = [hwv.flattening_matrix(lam, f, S, gs) for f, _ in fills]
    KS = nullspace(np.array([F.ravel() for F in FS]).T % p)        # c with sum c_j F_j(S) = 0
    msg = 'K_S for S=%s: dim %d' % (nm, len(KS))
    for prof, P in pts.items():
        if len(KS) and len(P):
            both = modrank(np.vstack([KS, np.array(P)]))
            msg += '; with %s points: dim(K_S + points) = %d' % (prof, both)
    print(msg); sys.stdout.flush()
