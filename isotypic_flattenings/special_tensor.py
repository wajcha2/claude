"""python3 special_tensor.py "lam" direction name [name ...]
Rank of the isotypic flattening (generic functional, direction `direction`) of lam on explicit tensors of
C^4 (x) C^4 (x) C^4 given by rank-one decompositions, compared with random tensors of rank 6 and 7:
  M2      2x2 matrix multiplication  sum_{i,j,k} e_ij (x) e_jk (x) e_ki  (8 terms; border rank 7, Landsberg 2006)
  M2S     the same tensor via Strassen's rank-7 decomposition (must give the same rank as M2)
  M2g     a random GL4 x GL4 x GL4 translate of M2 (same rank by equivariance)
  unit4   sum_{i<4} e_i (x) e_i (x) e_i  (rank 4)
  randR   random tensor of rank R (e.g. rand6, rand7)
Env: PRIME (default 524287, must be < 2^19), SEED (default 2024).
A flattening rank above the maximum over sigma_6 proves that the tensor is not in sigma_6 (border rank >= 7)."""
import sys, os, numpy as np
import opt_einsum as oe
import hwv, isoflat, hwv_fast
p = int(os.environ.get('PRIME', '524287')); assert p < 2 ** 19     # second prime e.g. 524269
hwv.p = isoflat.p = hwv_fast.p = p
from hwv import dim_schur, random_fillings, random_gs
from hwv_fast import prepare, build_network, find_path, execute
from isoflat import kronecker, modrank

n = 4
lam = eval(sys.argv[1]); dirn = int(sys.argv[2]); names = sys.argv[3:] or ['rand6', 'rand7', 'M2', 'M2S']
rng = np.random.default_rng(int(os.environ.get('SEED', '2024')))
E = np.eye(4, dtype=np.int64)
ij = lambda i, j: E[2 * i + j]

def tensor(name):
    if name == 'M2':
        t = [(ij(i, j), ij(j, k), ij(k, i)) for i in range(2) for j in range(2) for k in range(2)]
    elif name == 'M2S':   # Strassen: C = AB; A (x) B (x) C^T convention of M2: sum A_ij B_jk C_ki
        a11, a12, a21, a22 = (ij(0, 0), ij(0, 1), ij(1, 0), ij(1, 1))
        b11, b12, b21, b22 = a11, a12, a21, a22
        # c-slot pairs with e_ki: output entry c_ik appears as e_ki
        c11, c12, c21, c22 = ij(0, 0), ij(1, 0), ij(0, 1), ij(1, 1)
        t = [(a11 + a22, b11 + b22, c11 + c22), (a21 + a22, b11, c21 - c22), (a11, b12 - b22, c12 + c22),
             (a22, b21 - b11, c11 + c21), (a11 + a12, b22, c12 - c11), (a21 - a11, b11 + b12, c22),
             (a12 - a22, b21 + b22, c11)]
    elif name == 'M2g':   # random GL4 x GL4 x GL4 translate of M2 (flattening ranks are invariant)
        t = [(ij(i, j), ij(j, k), ij(k, i)) for i in range(2) for j in range(2) for k in range(2)]
        gl = [rng.integers(0, p, (4, 4)) for _ in range(3)]
        return tuple((np.array([x[s] for x in t], dtype=np.int64) @ gl[s]) % p for s in range(3))
    elif name == 'unit4':
        t = [(E[i], E[i], E[i]) for i in range(4)]
    elif name.startswith('rand'):
        r = int(name[4:])
        return tuple(rng.integers(0, p, (r, n)) for _ in range(3))
    return tuple(np.array([x[s] for x in t], dtype=np.int64) % p for s in range(3))

def full_tensor(v):
    return np.einsum('ri,rj,rk->ijk', *[x.astype(object) for x in v]) % p

T = {nm: tensor(nm) for nm in names}
if 'M2' in T and 'M2S' in T:
    assert (full_tensor(T['M2']) == full_tensor(T['M2S'])).all(), 'Strassen decomposition does not give M2'
perm = [dirn] + [t for t in range(3) if t != dirn]
lam_p = tuple(lam[t] for t in perm); g = kronecker(*lam)
n1 = dim_schur(lam_p[0], n); N1 = K = n1 + 4
gs = random_gs(rng, n, N1, K)
pre = {nm: prepare(tuple(T[nm][t] for t in perm), gs) for nm in names}
def flat(f, vm, pm):
    ops, out = build_network(f, vm, pm)
    return execute(ops, out, find_path(ops, out, None, oe.RandomGreedy(max_repeats=64))[0]).astype(np.int64)
ref = names[-1] if 'rand7' not in names else 'rand7'
fills, basis = [], []
while len(fills) < g:
    f = random_fillings(rng, lam_p); F = flat(f, *pre[ref])
    if F.any() and modrank(np.array(basis + [F[:24, :24].ravel()])) == len(basis) + 1:
        fills.append(f); basis.append(F[:24, :24].ravel())
coeffs = [int(c) for c in rng.integers(1, p, g)]
res = []
for nm in names:
    Fg = np.zeros((N1, K), dtype=np.int64)
    for c, f in zip(coeffs, fills):
        Fg = (Fg + c * flat(f, *pre[nm])) % p
    res.append('%s:%d' % (nm, modrank(Fg)))
    print('lam=%s direction %d (dims %s): %s' % (lam, dirn + 1, tuple(dim_schur(l, n) for l in lam_p), ' '.join(res))); sys.stdout.flush()
