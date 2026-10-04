"""d=8 separator ((6,2),(3,2,2,1),(3,2,2,1)), direction 1, with the canonical 1-dim U = phi_M2 (the unique functional on
the 4-dim multiplicity space vanishing on the isotypic component of the 2x2 matrix multiplication tensor).
(1) ranks of F_{phi_M2} on random tensors of ranks 5..8;
(2) A-freed flattening: T' = sum_{i<=6} e_i (x) b_i (x) c_i in C^6 (x) C^4 (x) C^4 (F_T = F_{T'} o (S^{62}alpha)^T for
    T = sum a_i b_i c_i): rank and cokernel dimension for random (b, c) and for the frame normal form."""
import sys, os, numpy as np
os.makedirs('live', exist_ok=True)
import flatlib
from hwv import p, dim_schur, random_fillings
from isoflat import modrank, kronecker
from specialU import nullspace

lam = ((6, 2), (3, 2, 2, 1), (3, 2, 2, 1))
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 21)
n = 4; g = kronecker(*lam); n1 = dim_schur(lam[0], n); n2 = dim_schur(lam[1], n)
NS = n1 + 4
G1 = rng.integers(0, p, (NS, 4, 4)); Gb = rng.integers(0, p, (n2, 4, 4)); Gc = rng.integers(0, p, (n2, 4, 4))
Zb, Zc = np.repeat(Gb, n2, axis=0), np.tile(Gc, (n2, 1, 1))          # 15 x 15 grid of target functionals
gs4 = (G1, Zb, Zc)
R = lambda r: rng.integers(0, p, (r, 4))
r7 = (R(7), R(7), R(7))
fills, basis = [], []
while len(fills) < g:
    f = random_fillings(rng, lam)
    F = flatlib.flat(f, r7, gs4)
    if F.any() and modrank(np.array(basis + [F[:40, :40].ravel()])) == len(basis) + 1:
        fills.append(f); basis.append(F[:40, :40].ravel())
E = np.eye(4, dtype=np.int64); ij = lambda i, j: E[2 * i + j]
M2 = tuple(np.array([[ij(i, j), ij(j, k), ij(k, i)][s] for i in range(2) for j in range(2) for k in range(2)]) for s in range(3))
KS = nullspace(np.array([flatlib.flat(f, M2, gs4).ravel() for f in fills]).T % p)
assert len(KS) == 1, len(KS)
cM2 = KS[0]
print('phi_M2 in filling coordinates (mod p):', list(cM2)); sys.stdout.flush()
flatU = lambda vecs, gs: sum(int(c) * flatlib.flat(f, vecs, gs) for c, f in zip(cM2, fills)) % p
print('(1) ranks of F_{phi_M2}: ' + ' '.join('r%d:%d' % (r, modrank(flatU((R(r), R(r), R(r)), gs4))) for r in (5, 6, 7, 8)))
sys.stdout.flush()
E6 = np.eye(6, dtype=np.int64)
G6 = rng.integers(0, p, (n2 * n2 + 20, 6, 6))
gs6 = (G6, Zb, Zc)
for trial in range(2):
    b, c = R(6), R(6)
    F = flatU((E6, b, c), gs6)
    rk = modrank(F)
    print('(2) A-freed, random (b,c): rank %d of %d, cokernel dim %d' % (rk, n2 * n2, n2 * n2 - rk)); sys.stdout.flush()
frame = np.vstack([np.eye(4, dtype=np.int64), np.ones((1, 4), dtype=np.int64)])
b, c = np.vstack([frame, R(1)]), np.vstack([frame, R(1)])
F = flatU((E6, b, c), gs6); rk = modrank(F)
print('(2) A-freed, frames + random 6th points: rank %d, cokernel dim %d' % (rk, n2 * n2 - rk))
np.save('live/afree_d8_data.npy',
        {'cM2': cM2, 'fills': fills, 'Gb': Gb, 'Gc': Gc, 'G1': G1}, allow_pickle=True)
