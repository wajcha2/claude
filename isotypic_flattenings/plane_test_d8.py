"""Is the separating locus of the d=8 hit ((6,2),(3,2,2,1),(3,2,2,1)) (direction 1, 1-dim U) a plane, and does it contain
phi_M2?  Same seed-5 setup as hit_d8_special.py / line_point_M2.py (filling basis of M^*, points, tensors low1, low2, high).
phi_A = the d7d8 point (t = 509492 on their line), phi_M2 = generator of K_M2.  Separating points phi_B, phi_C on further
random lines (pencil.py drop polynomial), then ranks at random points of the line <phi_M2, phi_A> and of the planes spanned.
usage: python3 plane_test_d8.py [nlines] [seed]"""
import sys, time, numpy as np
import hwv, hwv_fast
hwv.flattening_matrix = hwv_fast.flattening_matrix_fast
from hwv import p, dim_schur, random_fillings, random_gs, flattening_matrix
from isoflat import modrank, kronecker
from specialU import nullspace
from pencil import drop_poly, roots_mod_p

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
nlines = int(sys.argv[1]) if len(sys.argv) > 1 else 3
rng2 = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 77)
extra = {'low3': 6, 'high2': 7}
vecs.update({k: tuple(rng2.integers(0, p, (r, n)) for _ in range(3)) for k, r in extra.items()})
E = np.eye(4, dtype=np.int64); ij = lambda i, j: E[2 * i + j]
vecs['M2'] = tuple(np.array([[ij(i, j), ij(j, k), ij(k, i)][s] for i in range(2) for j in range(2) for k in range(2)]) for s in range(3))
t0 = time.time()
Fb = {k: [flattening_matrix(lam, f, v, gs) % p for f, _ in fills] for k, v in vecs.items()}
comb = lambda k, c: sum(int(x) * F for x, F in zip(c, Fb[k])) % p
ks = ['low1', 'low2', 'low3', 'high', 'high2']
prof = lambda c: tuple(modrank(comb(k, c)) for k in ks)
phiM2 = nullspace(np.array([F.ravel() for F in Fb['M2']]).T % p)[0]
phiA = (ca + 509492 * cb) % p
print('basis flattenings built (%.0fs); profile = ranks on (low1, low2, low3, high, high2)' % (time.time() - t0))
print('phi_M2 = %s: profile %s' % (list(map(int, phiM2)), prof(phiM2)))
print('phi_A  = %s: profile %s' % (list(map(int, phiA)), prof(phiA))); sys.stdout.flush()
for trial in range(3):
    a, b = rng2.integers(1, p, 2)
    c = (a * phiM2 + b * phiA) % p
    print('random point of the line <phi_M2, phi_A>: profile %s' % (prof(c),)); sys.stdout.flush()
seps = [phiM2, phiA]
for L in range(nlines):
    a, b = rng2.integers(1, p, g), rng2.integers(1, p, g)
    F1 = {k: comb(k, a) for k in ('low1', 'low2')}; F2 = {k: comb(k, b) for k in ('low1', 'low2')}
    rho = modrank((F1['low1'] + 7 * F2['low1']) % p)
    hc = drop_poly(F1['low1'], F2['low1'], rho, rng2).gcd(drop_poly(F1['low2'], F2['low2'], rho, rng2))
    roots = roots_mod_p(hc) if hc.degree() > 0 else []
    out = []
    for t in roots:
        c = (a + t * b) % p; pr = prof(c); out.append((t, pr))
        if pr[0] < pr[3]: seps.append(c)
    print('random line %d: drop-poly degree %d, F_p roots %s  (%.0fs)' % (L, hc.degree(), out, time.time() - t0)); sys.stdout.flush()
S = np.array(seps) % p
print('separating points found: %d, rank of their span in M^* = %d' % (len(seps), modrank(S)))
if len(seps) >= 3:
    B = S[:3]
    print('rank of span{phi_M2, phi_A, phi_B} = %d' % modrank(B))
    for trial in range(4):
        c = (rng2.integers(1, p, 3) @ B) % p
        print('random point of the plane <phi_M2, phi_A, phi_B>: profile %s' % (prof(c),)); sys.stdout.flush()
