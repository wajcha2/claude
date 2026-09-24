"""Dissect the d=8 hit ((6,2),(3,2,2,1),(3,2,2,1)): which subspaces U of the 4-dim multiplicity space separate?
Uses the fast evaluation (hwv_fast) through the old interfaces by monkeypatching."""
import numpy as np, sys, time, itertools
import hwv, hwv_fast
hwv.flattening_matrix = hwv_fast.flattening_matrix_fast
from hwv import *
from isoflat import modrank
import specialU
from specialU import probe3, chunked_F, nullspace
lam = eval(sys.argv[1]) if len(sys.argv) > 1 else ((6, 2), (3, 2, 2, 1), (3, 2, 2, 1))
n, rl, rh = 4, 6, 7
rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 3)
g = kronecker(*lam); dims = tuple(dim_schur(l, n) for l in lam); n1 = dims[0]
G = tuple(rng.integers(0, p, (8, n, n)) for _ in range(3))
def rvecs(r): return tuple(rng.integers(0, p, (r, n)) for _ in range(3))
tens = {'low': rvecs(rl), 'low2': rvecs(rl), 'high': rvecs(rh), 'high2': rvecs(rh)}
fills, probes, tries = [], [], 0
while len(fills) < g and tries < 100 * g:
    f = random_fillings(rng, lam); tries += 1
    P = probe3(lam, f, tens['high'], G)
    if np.any(P) and modrank(np.array([q.ravel() for q in probes] + [P.ravel()])) == len(fills) + 1:
        fills.append(f); probes.append(P)
assert len(fills) == g
N1 = n1 + 4; K = n1 + 4
gs = random_gs(rng, n, N1, K)
t0 = time.time()
Fs = {k: [chunked_F(lam, f, v, gs, 64) for f in fills] for k, v in tens.items()}
print("lam=%s g=%d dims=%s  F matrices %s built in %.0fs" % (lam, g, dims, Fs['low'][0].shape, time.time() - t0)); sys.stdout.flush()
def stack_rank(k, U):   # U: rows = basis of the subspace (coordinates in the filling basis)
    blocks = [sum(int(c) * F for c, F in zip(u, Fs[k])) % p for u in U]
    return modrank(np.hstack(blocks))
# generic subspaces of each dimension
for dimU in range(1, g + 1):
    U = rng.integers(1, p, (dimU, g))
    print("generic U dim %d: ranks low/low2/high/high2 = %s" % (dimU, [stack_rank(k, U) for k in tens])); sys.stdout.flush()
# natural subspaces: U_k (functionals vanishing on sigma_k) and swap-23 eigenspaces
for kk in range(1, 7):
    rows = []
    for _ in range(2):
        v = rvecs(kk); rows.append(np.array([probe3(lam, f, v, G).ravel() for f in fills]).T)
    Uk = nullspace(np.vstack(rows))
    if len(Uk): print("U_%d (kills sigma_%d) dim %d: ranks = %s" % (kk, kk, len(Uk), [stack_rank(k, Uk) for k in tens])); sys.stdout.flush()
    else: print("U_%d = 0" % kk)
# swap of factors 2,3 (lam2 == lam3)
pm = [0, 2, 1]; cols = []
for f in fills:
    Pt = np.transpose(probe3(tuple(lam[t] for t in pm), [f[t] for t in pm], tuple(tens['high'][t] for t in pm), tuple(G[t] for t in pm)), pm)
    sol = nullspace(np.array([q.ravel() for q in probes] + [Pt.ravel()]).T); s = sol[0]
    inv = pow(int((-s[-1]) % p), p - 2, p); cols.append((s[:-1] * inv) % p)
Tau = np.array(cols).T % p
for sign, nm in ((1, '+'), (p - 1, '-')):
    E = nullspace((Tau - sign * np.eye(g, dtype=np.int64)) % p)
    if len(E): print("swap23 eigenspace %s dim %d: ranks = %s" % (nm, len(E), [stack_rank(k, E) for k in tens])); sys.stdout.flush()
