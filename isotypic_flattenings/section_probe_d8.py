"""Degree of the cokernel of the A-freed phi_M2 flattening (d=8 separator) along a line in one point.
b_1..b_5 = c_1..c_5 = projective frame, the 6th point (or the moving point) on a line P(tau) = p0 + tau q0.
Cokernel dim k (= 3 here); normalised basis n_0..n_{k-1} (coordinates j_0..j_{k-1} = identity); a polynomial section
psi(tau) = sum_i c_i(tau) n_i(tau) with deg c_i <= d is detected by vanishing (d+1)-th finite differences.
usage: python3 section_probe_d8.py b6|c6|b1|c1 [npts]"""
import sys, numpy as np
from math import comb
import flatlib
from hwv import p
from isoflat import modrank
from specialU import nullspace

which = sys.argv[1] if len(sys.argv) > 1 else 'b6'
NPTS = int(sys.argv[2]) if len(sys.argv) > 2 else 16
D = np.load('live/afree_d8_data.npy', allow_pickle=True).item()
cM2, fills, Gb, Gc = D['cM2'], D['fills'], D['Gb'], D['Gc']
n2 = Gb.shape[0]; T = n2 * n2
rng = np.random.default_rng(29)
Zb, Zc = np.repeat(Gb, n2, axis=0), np.tile(Gc, (n2, 1, 1))
gs6 = (rng.integers(0, p, (T + 20, 6, 6)), Zb, Zc)
E6 = np.eye(6, dtype=np.int64)
flatU = lambda vecs: sum(int(c) * flatlib.flat(f, vecs, gs6) for c, f in zip(cM2, fills)) % p
frame = np.vstack([np.eye(4, dtype=np.int64), np.ones((1, 4), dtype=np.int64)])
b0 = np.vstack([frame, rng.integers(0, p, (1, 4))]); c0 = np.vstack([frame, rng.integers(0, p, (1, 4))])
p0, q0 = rng.integers(0, p, 4), rng.integers(0, p, 4)
side, j = which[0], int(which[1:]) - 1
Ks, taus = [], list(range(1, NPTS + 1))
for tau in taus:
    b, c = b0.copy(), c0.copy()
    (b if side == 'b' else c)[j] = (p0 + tau * q0) % p
    Ks.append(nullspace(flatU((E6, b, c))))
k = len(Ks[0]); assert all(len(K) == k for K in Ks)
print('moving %s: cokernel dim %d at all %d sample points' % (which, k, NPTS)); sys.stdout.flush()
J = [int(x) for x in rng.choice(T, k, replace=False)]
def normalised(K):
    M = K[:, J].T % p                                   # M[i, l] = K[l][J[i]]
    from sympy import Matrix
    Minv = np.array(Matrix(M.tolist()).inv_mod(p).tolist(), dtype=np.int64)
    return (Minv.T @ K) % p                             # rows n_i with n_i[J] = e_i
Ns = np.array([normalised(K) for K in Ks])            # (NPTS, k, T)
for d in range(0, 8):
    nd = NPTS - d - 1
    if nd <= 0: break
    cols = []
    for i in range(k):
        for e in range(d + 1):
            vals = (Ns[:, i, :] * np.array([pow(t, e, p) for t in taus], dtype=np.int64)[:, None]) % p
            diff = np.zeros((nd, T), dtype=np.int64)
            for s in range(d + 2):
                diff = (diff + ((-1) ** (d + 1 - s)) * comb(d + 1, s) * vals[s:s + nd]) % p
            cols.append(diff.ravel())
    S = nullspace(np.array(cols, dtype=np.int64).T % p)
    print('degree <= %d: dimension of the space of polynomial sections = %d' % (d, len(S))); sys.stdout.flush()
    if len(S) >= k + 1: break
