"""K_S = {phi in M^* : phi(iso_lam(S^{(x)8})) = 0} for degenerations S of M2 (limits of GL4^3-translates: compressions
by rank-3 projections in one, two or three factors) and for M2 minus one term of Strassen's decomposition (rank 6).
For S in the orbit closure of M2 the M-span of iso(S) lies in that of M2, so K_S contains K_M2.  Seed-5 setup of
hit_d8_special.py (filling basis of M^*); prints dim K_S, a basis (normalised, rational reconstruction) and the ranks of
F_phi for random phi in K_S on two rank-6 and one rank-7 tensor.
usage: python3 ks_degen_d8.py"""
import sys, numpy as np
from fractions import Fraction
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
Fb = {k: [flattening_matrix(lam, f, vecs[k], gs) % p for f, _ in fills] for k in tens}
comb = lambda k, c: sum(int(x) * F for x, F in zip(c, Fb[k])) % p
def ratrec(a):
    r0, r1, s0, s1 = p, int(a) % p, 0, 1
    while r1 * r1 * 2 > p:
        q = r0 // r1; r0, r1, s0, s1 = r1, r0 - q * r1, s1, s0 - q * s1
    return str(Fraction(r1, s1)) if s1 * s1 * 2 <= p else '?'
def basis_str(KS):
    if len(KS) == 0: return '0'
    M = np.array([[int(x) for x in v] for v in KS], dtype=np.int64) % p      # reduced echelon basis mod p
    r = 0
    for c in range(M.shape[1]):
        piv = [i for i in range(r, M.shape[0]) if M[i, c] % p]
        if not piv: continue
        M[[r, piv[0]]] = M[[piv[0], r]]
        M[r] = (M[r] * pow(int(M[r, c]), p - 2, p)) % p
        for i in range(M.shape[0]):
            if i != r and M[i, c]: M[i] = (M[i] - M[i, c] * M[r]) % p
        r += 1
    return '; '.join('(' + ', '.join(ratrec(x) for x in row) + ')' for row in M[:r])
E = np.eye(4, dtype=np.int64); ij = lambda i, j: E[2 * i + j]
def rank1_sum(terms):
    return tuple(np.array([t[s] for t in terms], dtype=np.int64) % p for s in range(3))
M2 = rank1_sum([(ij(i, j), ij(j, k), ij(k, i)) for i in range(2) for j in range(2) for k in range(2)])
a11, a12, a21, a22 = ij(0, 0), ij(0, 1), ij(1, 0), ij(1, 1)
c11, c12, c21, c22 = ij(0, 0), ij(1, 0), ij(0, 1), ij(1, 1)
strassen = [(a11 + a22, a11 + a22, c11 + c22), (a21 + a22, a11, c21 - c22), (a11, a12 - a22, c12 + c22),
            (a22, a21 - a11, c11 + c21), (a11 + a12, a22, c12 - c11), (a21 - a11, a11 + a12, c22),
            (a12 - a22, a21 + a22, c11)]
rng3 = np.random.default_rng(11)
def proj(k):                                    # random rank-k map C^4 -> C^4
    return (rng3.integers(0, p, (4, k)) @ rng3.integers(0, p, (k, 4))) % p
def apply(S, maps):
    return tuple((S[s] @ maps[s].T) % p if maps[s] is not None else S[s] for s in range(3))
I = None
cases = {'M2': M2}
for s in range(3):
    mp = [I, I, I]; mp[s] = proj(3); cases['M2 compressed: rank-3 map on factor %d' % (s + 1)] = apply(M2, mp)
for s in range(3):
    mp = [proj(3), proj(3), proj(3)]; mp[s] = I; cases['M2 compressed: rank-3 maps on the factors != %d' % (s + 1)] = apply(M2, mp)
cases['M2 compressed: rank-3 maps on all factors'] = apply(M2, [proj(3), proj(3), proj(3)])
for s in range(3):
    mp = [I, I, I]; mp[s] = proj(2); cases['M2 compressed: rank-2 map on factor %d' % (s + 1)] = apply(M2, mp)
for j in range(7):
    cases['Strassen M2 minus term %d (rank 6)' % (j + 1)] = rank1_sum([t for i, t in enumerate(strassen) if i != j])
KM2 = None
for nm, S in cases.items():
    FS = [flattening_matrix(lam, f, S, gs) % p for f, _ in fills]
    KS = nullspace(np.array([F.ravel() for F in FS]).T % p)
    if nm == 'M2': KM2 = KS
    line = '%-48s dim K_S = %d' % (nm, len(KS))
    if len(KS):
        line += ' | basis %s' % basis_str(KS)
        if KM2 is not None and len(KM2): line += ' | contains K_M2: %s' % (modrank(np.vstack([KS, KM2])) == len(KS))
        if len(KS) < g:
            phi = (rng3.integers(1, p, len(KS)) @ KS) % p
            line += ' | random phi in K_S: ranks low1, low2, high = %s' % [modrank(comb(k, phi)) for k in tens]
    print(line); sys.stdout.flush()
