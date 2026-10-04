"""Is there a cokernel vector psi(b6, c6) of the A-freed phi_M2 flattening (d=8 separator) that is BILINEAR in (b6, c6)
(b1..b5 = c1..c5 = projective frame)?  Values on a 4 x 4 grid (b6, c6) in (u_a, v_b) determine a bilinear psi; extra
points test it.  Unknowns: psi(u_a, v_b) = sum_i z_{ab,i} K(u_a, v_b)_i (3 per grid point).
usage: python3 bilinear_fit_d8.py [nextra]"""
import sys, numpy as np
import flatlib
from hwv import p
from isoflat import modrank
from specialU import nullspace
from sympy import Matrix

NEX = int(sys.argv[1]) if len(sys.argv) > 1 else 6
D = np.load('live/afree_d8_data.npy', allow_pickle=True).item()
cM2, fills, Gb, Gc = D['cM2'], D['fills'], D['Gb'], D['Gc']
n2 = Gb.shape[0]; T = n2 * n2
rng = np.random.default_rng(31)
Zb, Zc = np.repeat(Gb, n2, axis=0), np.tile(Gc, (n2, 1, 1))
gs6 = (rng.integers(0, p, (T + 20, 6, 6)), Zb, Zc)
E6 = np.eye(6, dtype=np.int64)
frame = np.vstack([np.eye(4, dtype=np.int64), np.ones((1, 4), dtype=np.int64)])
def coker(x, y):
    F = sum(int(c) * flatlib.flat(f, (E6, np.vstack([frame, x]), np.vstack([frame, y])), gs6) for c, f in zip(cM2, fills)) % p
    return nullspace(F)
U = rng.integers(0, p, (4, 4)); V = rng.integers(0, p, (4, 4))          # grid bases (rows)
Uinv = np.array(Matrix(U.T.tolist()).inv_mod(p).tolist(), dtype=np.int64)  # coordinates: lam = Uinv @ x
Vinv = np.array(Matrix(V.T.tolist()).inv_mod(p).tolist(), dtype=np.int64)
Kg = {(a, b): coker(U[a], V[b]) for a in range(4) for b in range(4)}
k = len(Kg[(0, 0)]); assert all(len(K) == k for K in Kg.values())
print('grid done: cokernel dim %d' % k); sys.stdout.flush()
rows = []
for e in range(NEX):
    x, y = rng.integers(0, p, 4), rng.integers(0, p, 4)
    Kx = coker(x, y); lam, mu = (Uinv @ x) % p, (Vinv @ y) % p
    # psi(x,y) = sum_ab lam_a mu_b psi(u_a,v_b) must lie in span(Kx): project onto the complement of span(Kx)
    Ann = nullspace(Kx.astype(np.int64))                # rows w with Kx w = 0: the orthogonal complement of span(Kx)
    blocks = []
    for (a, b), K in Kg.items():
        blocks.append((int(lam[a]) * int(mu[b]) % p) * (Ann @ K.T % p) % p)   # (T-k, k) columns for z_{ab}
    rows.append(np.hstack(blocks) % p)
    S = nullspace(np.vstack(rows) % p)
    print('after %d extra points: dimension of the space of bilinear sections = %d' % (e + 1, len(S))); sys.stdout.flush()
