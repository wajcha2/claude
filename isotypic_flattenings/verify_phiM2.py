"""Independent check of: 'exactly a 1-dim space of functionals phi on the 4-dim multiplicity space M of
lam = ((6,2),(3,2,2,1),(3,2,2,1)) kills the isotypic component of M2^{(x)8}, and that phi separates rank 6 from 7'.
* F_j(S) = flattening matrix S^{62}V^* -> S^{3221}V (x) S^{3221}V (N1 x K, N1 = K = 364 random HWV points) of the
  isotypic tensor phi_j(iso_lam(S^{(x)8})) for a basis phi_1..phi_4 of M^* (independent fillings);
  N1 >= 360 = dim S^{62} and K >= 225 = dim of the target, so F = 0 iff the isotypic tensor is 0 (generic points).
* K_S = {c : sum_j c_j F_j(S) = 0}; dim span{F_j(M2)} = 4 - dim K_M2.
Computed with the reference implementation hwv.flattening_matrix (no hwv_fast) for M2 via its 8-term decomposition, and
with hwv_fast for M2 via Strassen's 7-term decomposition, for random tensors, and for a second prime.
usage: python3 verify_phiM2.py [prime] [seed]"""
import sys, time, numpy as np
q = int(sys.argv[1]) if len(sys.argv) > 1 else 524287
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 101
import hwv, isoflat, hwv_fast
hwv.p = isoflat.p = hwv_fast.p = q
p = q
from hwv import dim_schur, random_fillings, random_gs, flattening_matrix as ref_flat
from hwv_fast import flattening_matrix_fast as fast_flat
from isoflat import modrank, kronecker
from specialU import nullspace

lam = ((6, 2), (3, 2, 2, 1), (3, 2, 2, 1))
rng = np.random.default_rng(seed)
n = 4; g = kronecker(*lam); N1 = K = dim_schur(lam[0], n) + 4
gs = random_gs(rng, n, N1, K)
E = np.eye(4, dtype=np.int64); ij = lambda i, j: E[2 * i + j]
def rank1_sum(terms):
    return tuple(np.array([t[s] for t in terms], dtype=np.int64) % p for s in range(3))
M2 = rank1_sum([(ij(i, j), ij(j, k), ij(k, i)) for i in range(2) for j in range(2) for k in range(2)])
a11, a12, a21, a22 = ij(0, 0), ij(0, 1), ij(1, 0), ij(1, 1)
c11, c12, c21, c22 = ij(0, 0), ij(1, 0), ij(0, 1), ij(1, 1)
M2S = rank1_sum([(a11 + a22, a11 + a22, c11 + c22), (a21 + a22, a11, c21 - c22), (a11, a12 - a22, c12 + c22),
                 (a22, a21 - a11, c11 + c21), (a11 + a12, a22, c12 - c11), (a21 - a11, a11 + a12, c22),
                 (a12 - a22, a21 + a22, c11)])
full = lambda v: np.einsum('ri,rj,rk->ijk', *[x.astype(object) for x in v]) % p
assert (full(M2) == full(M2S)).all(), 'Strassen decomposition != M2'
R = lambda r: rank1_sum([tuple(rng.integers(0, p, 4) for _ in range(3)) for _ in range(r)])
r6a, r6b, r7a, r7b = R(6), R(6), R(7), R(7)
fills = []
while len(fills) < g:
    f = random_fillings(rng, lam)
    F = fast_flat(lam, f, r7a, gs)
    if F.any() and modrank(np.array([fast_flat(lam, x, r7a, gs).ravel() for x in fills] + [F.ravel()])) == len(fills) + 1:
        fills.append(f)
print('prime %d, seed %d, %d independent fillings (multiplicity space basis), matrices %dx%d' % (p, seed, g, N1, K)); sys.stdout.flush()
t0 = time.time()
FM2_ref = [ref_flat(lam, f, M2, gs) % p for f in fills]
print('reference implementation, M2 (8 terms): rank of each F_j(M2): %s; dim span{F_j(M2)} = %d  (%.0fs)'
      % ([modrank(F) for F in FM2_ref], modrank(np.array([F.ravel() for F in FM2_ref])), time.time() - t0)); sys.stdout.flush()
FM2S = [fast_flat(lam, f, M2S, gs) % p for f in fills]
print('fast implementation, M2 via Strassen (7 terms): equal to the reference matrices: %s'
      % all(np.array_equal(a, b) for a, b in zip(FM2_ref, FM2S))); sys.stdout.flush()
KS = nullspace(np.array([F.ravel() for F in FM2_ref]).T % p)
print('dim K_M2 = %d' % len(KS))
comb = lambda Fs, c: sum(int(x) * F for x, F in zip(c, Fs)) % p
Fr = {nm: [fast_flat(lam, f, T, gs) % p for f in fills] for nm, T in (('r6a', r6a), ('r6b', r6b), ('r7a', r7a), ('r7b', r7b))}
for trial in range(2):
    c = rng.integers(1, p, g)
    print('random phi: rank F_phi(M2) = %d; ranks on r6a,r6b,r7a,r7b = %s'
          % (modrank(comb(FM2_ref, c)), [modrank(comb(Fr[k], c)) for k in Fr]))
for c in KS:
    print('phi in K_M2: F_phi(M2) is the zero matrix: %s; ranks on r6a,r6b,r7a,r7b = %s'
          % (not comb(FM2_ref, c).any(), [modrank(comb(Fr[k], c)) for k in Fr]))
