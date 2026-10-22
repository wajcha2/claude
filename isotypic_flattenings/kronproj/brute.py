"""brute.py -- independent brute-force ranks of the lattice families (small n, d), for test_comb.py.

T^{(x)d} is formed explicitly as an array with axes (A_1..A_d, B_1..B_d, C_1..C_d) mod p; S_d acts on the d tensor
positions of one factor; isotypic projectors P_lam = (f_lam / d!) sum chi_lam(s) s and Young symmetrizers c_lam act
as group-algebra elements.  Nothing from hwv / hwv_fast is used (no highest weight vectors, no sampling).
  family A (source lam, targets S with the full Kronecker space on the target side):
      rank = dim of the S_lam A-support of  sum_{(mu,nu) in S} (1 (x) P_mu (x) P_nu) T^{(x)d},
      i.e. the column space of [ c_lam a_1 Y | c_lam a_2 Y | ... ] (rows A^{(x)d}) for f_lam + 2 random a_k in C[S_d];
  family B (target (mu, nu), sources S with the full Kronecker space on the source side):
      rank = dim of the S_mu B (x) S_nu C-support of sum_{lam in S} (P_lam (x) 1 (x) 1) T^{(x)d}."""
import itertools, sys, os
import numpy as np
_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(_HERE))
import hwv
from hwv import p
from isoflat import mn_char, modrank
from math import factorial

def compose(s, t):
    """(s o t)(i) = s[t[i]]"""
    return tuple(s[i] for i in t)

def cycle_type(s):
    seen, ct = set(), []
    for i in range(len(s)):
        if i in seen: continue
        c, j = 0, i
        while j not in seen:
            seen.add(j); j = s[j]; c += 1
        ct.append(c)
    return tuple(sorted(ct, reverse=True))

def sign(s):
    return (-1) ** (len(s) - len(cycle_type(s)))

def ga_mul(x, y):
    """product in the group algebra (dicts perm -> coefficient mod p)."""
    out = {}
    for s, a in x.items():
        for t, b in y.items():
            u = compose(s, t); out[u] = (out.get(u, 0) + a * b) % p
    return {k: v for k, v in out.items() if v}

def isotypic_projector(lam, d):
    f = mn_char(tuple(lam), (1,) * d)
    c = f * pow(factorial(d), p - 2, p) % p
    return {s: c * mn_char(tuple(lam), cycle_type(s)) % p for s in itertools.permutations(range(d))}

def young_symmetrizer(lam, d):
    rows, k = [], 0
    for r in lam:
        rows.append(list(range(k, k + r))); k += r
    cols = [[row[j] for row in rows if j < len(row)] for j in range(lam[0])]
    def group(blocks):
        out = []
        for combo in itertools.product(*[itertools.permutations(b) for b in blocks]):
            s = list(range(d))
            for b, im in zip(blocks, combo):
                for x, y in zip(b, im):
                    s[x] = y
            out.append(tuple(s))
        return out
    R = {s: 1 for s in group(rows)}
    C = {s: sign(s) % p for s in group(cols)}
    return ga_mul(R, C)

def act(elem, Y, off, d):
    """apply the group-algebra element to the d axes off..off+d-1 of Y: (s.Y)[.., i_{s(1)}.., ..] = Y[.., i_1, ..],
    i.e. tensor position t is moved to position s(t) (a left action: act(s, act(t, Y)) = act(s o t, Y))."""
    out = np.zeros_like(Y)
    nd = Y.ndim
    for s, c in elem.items():
        axes = list(range(nd))
        for t in range(d):
            axes[off + s[t]] = off + t
        out = (out + c * np.transpose(Y, axes)) % p
    return out

def tensor_power(vecs, d):
    """T^{(x)d} with axes A_1..A_d, B_1..B_d, C_1..C_d, for T = sum_i A[i] (x) B[i] (x) C[i]."""
    A, B, C = [np.asarray(v, dtype=np.int64) % p for v in vecs]
    T = np.einsum('ia,ib,ic->abc', A, B, C) % p
    X = T
    for _ in range(d - 1):
        X = np.multiply.outer(X, T) % p
    # axes are (a1 b1 c1 a2 b2 c2 ...): reorder to (a1..ad b1..bd c1..cd)
    order = [3 * t + f for f in range(3) for t in range(d)]
    return np.ascontiguousarray(np.transpose(X, order))

def random_ga(rng, d):
    return {s: int(rng.integers(0, p)) for s in itertools.permutations(range(d))}

def _rank_stack(blocks, axis, rng):
    """rank of blocks stacked along axis (1: horizontally, 0: vertically), compressed by random matrices."""
    if axis == 1:
        R = blocks[0].shape[0]
        M = np.zeros((R, R + 8), dtype=np.int64)
        for Z in blocks:
            G = rng.integers(0, p, (Z.shape[1], R + 8))
            M = (M + hwv_mul(Z, G)) % p
    else:
        Cc = blocks[0].shape[1]
        D = min(Cc, sum(Z.shape[0] for Z in blocks)) + 8
        M = np.zeros((D, Cc), dtype=np.int64)
        for Z in blocks:
            G = rng.integers(0, p, (D, Z.shape[0]))
            M = (M + hwv_mul(G, Z)) % p
    return modrank(M)

def hwv_mul(X, Y):
    import hwv_fast
    return hwv_fast.fmatmul((X % p).astype(np.float64)[None], (Y % p).astype(np.float64)[None])[0].astype(np.int64)

class Brute:
    def __init__(self, vecs, d, seed=1):
        self.d = d
        self.n = vecs[0].shape[1]
        self.X = tensor_power(vecs, d)
        self.rng = np.random.default_rng(seed)
        self._proj = {}

    def proj(self, lam):
        if lam not in self._proj:
            self._proj[lam] = isotypic_projector(lam, self.d)
        return self._proj[lam]

    def rank_A(self, lam, S):
        d, n = self.d, self.n
        Y = np.zeros_like(self.X)
        for mu, nu in S:
            Y = (Y + act(self.proj(nu), act(self.proj(mu), self.X, d, d), 2 * d, d)) % p
        f = mn_char(tuple(lam), (1,) * d)
        c = young_symmetrizer(lam, d)
        blocks = [act(ga_mul(c, random_ga(self.rng, d)), Y, 0, d).reshape(n ** d, -1) for _ in range(f + 2)]
        return _rank_stack(blocks, 1, self.rng)

    def rank_B(self, mn, S):
        d, n = self.d, self.n
        mu, nu = mn
        Y = np.zeros_like(self.X)
        for lam in S:
            Y = (Y + act(self.proj(lam), self.X, 0, d)) % p
        cm, cn = young_symmetrizer(mu, d), young_symmetrizer(nu, d)
        fm, fn = mn_char(tuple(mu), (1,) * d), mn_char(tuple(nu), (1,) * d)
        Ys = [act(ga_mul(cm, random_ga(self.rng, d)), Y, d, d) for _ in range(fm + 2)]
        blocks = [act(ga_mul(cn, random_ga(self.rng, d)), Z, 2 * d, d).reshape(n ** d, -1) for Z in Ys for _ in range(fn + 2)]
        return _rank_stack(blocks, 0, self.rng)
