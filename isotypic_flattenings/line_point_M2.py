"""Does the d7d8 special 1-dim U of the d=8 hit (pencil point t=509492 of hit_d8_special.py) vanish on M2?
Reproduces the random draws of pencil.analyse(lam, 4, 6, 7, default_rng(5), 0) exactly (fillings, evaluation points,
tensors, line ca + t cb in M^*), checks the published ranks at t=509492 (220, 220, 225) and t=37168 (84, 84, 84), then
evaluates F_phi(M2) for these points and compares them with K_M2 = {phi : phi(iso_lam(M2^{(x)8})) = 0} in the same basis.
usage: python3 line_point_M2.py"""
import sys, numpy as np
import hwv, hwv_fast
hwv.flattening_matrix = hwv_fast.flattening_matrix_fast
from hwv import p, dim_schur, random_fillings, random_gs, flattening_matrix
from isoflat import modrank, kronecker
from specialU import nullspace

lam = ((6, 2), (3, 2, 2, 1), (3, 2, 2, 1))
rng = np.random.default_rng(5)
n, r_low, r_high = 4, 6, 7
# --- identical to pencil.analyse(lam, n, r_low, r_high, rng, direction=0) up to the choice of the line
n1 = dim_schur(lam[0], n); N1 = K = n1 + 4
gs = random_gs(rng, n, N1, K)
tens = {'low1': r_low, 'low2': r_low, 'high': r_high}
vecs = {k: tuple(rng.integers(0, p, (r, n)) for _ in range(3)) for k, r in tens.items()}
g = kronecker(*lam); fills = []; tries = 0
while len(fills) < g and tries < 100 * g:
    f = random_fillings(rng, lam); tries += 1
    F = flattening_matrix(lam, f, vecs['high'], gs)
    if np.any(F) and modrank(np.array([x[1].ravel() for x in fills] + [F.ravel()])) == len(fills) + 1:
        fills.append((f, F))
assert len(fills) == g
ca, cb = rng.integers(1, p, g), rng.integers(1, p, g)
# ---
Fb = {k: [flattening_matrix(lam, f, vecs[k], gs) % p for f, _ in fills] for k in tens}
E = np.eye(4, dtype=np.int64); ij = lambda i, j: E[2 * i + j]
M2 = tuple(np.array([[ij(i, j), ij(j, k), ij(k, i)][s] for i in range(2) for j in range(2) for k in range(2)]) for s in range(3))
Fb['M2'] = [flattening_matrix(lam, f, M2, gs) % p for f, _ in fills]
comb = lambda k, c: sum(int(x) * F for x, F in zip(c, Fb[k])) % p
KS = nullspace(np.array([F.ravel() for F in Fb['M2']]).T % p)
print('p = %d; basis of M^* = the %d fillings of hit_d8_special.py (seed 5); dim K_M2 = %d, K_M2 = <%s>'
      % (p, g, len(KS), [int(x) for x in KS[0]] if len(KS) else None))
for j, (f, _) in enumerate(fills):
    print('  filling %d: columns of the (6,2) tableau %s | (3,2,2,1) tableau 2: %s | (3,2,2,1) tableau 3: %s' % (j, f[0], f[1], f[2]))
for t in (509492, 37168):
    phi = (ca + t * cb) % p
    print('t = %6d: phi = %s; ranks on low1, low2, high = %s (published: %s); rank F_phi(M2) = %d; phi in K_M2: %s'
          % (t, [int(x) for x in phi], [modrank(comb(k, phi)) for k in tens], {509492: (220, 220, 225), 37168: (84, 84, 84)}[t],
             modrank(comb('M2', phi)), modrank(np.vstack([KS, phi])) == len(KS)))
for c in KS:
    print('phi_M2 (spans K_M2): ranks on low1, low2, high = %s; F_phi(M2) == 0: %s'
          % ([modrank(comb(k, c)) for k in tens], not comb('M2', c).any()))
