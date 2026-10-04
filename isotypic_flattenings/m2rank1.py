"""python3 m2rank1.py "lam" dirn      -- does the 1-dim drop locus D(T) = {phi : F_phi(T) not injective} exist at all?
For a tall component (generic rank n1), phi is a drop point of T iff phi (x) x lies in K(T) = ker V_g(T) for some x != 0.
Take a basis kappa_1..kappa_m of K(T) (g x n1 matrices); the rank-<=1 elements X(c) = sum c_a kappa_a are the common zeros
of all 2x2 minors of X(c), quadrics in c.  If these minors span the whole space of quadrics in m variables, the only
common zero is c = 0: K(T) has no rank-one element and F_phi(T) is injective for EVERY phi (rigorous over the algebraic
closure; the span is computed exactly mod p).  Printed for R6a, R7 and M2: dim K, dim span of minors / dim of quadrics."""
import sys, os, itertools, numpy as np
import m2lib
from m2lib import p, dim_schur, kronecker, random_gs, frank, choose_fillings, rand_tensor, m2_terms, compress_cols
import flatlib
from specialU import nullspace

def kernel_basis(Fs, n1, rng):
    """basis of K(T) in coordinates of M^* (x) X1^*: X1^* is represented by the N1 sample points modulo their
    linear relations; we use n1 independent source points (rows) only, so coordinates are exact."""
    V = np.vstack(Fs)                                   # (g N1) x K
    return nullspace(compress_cols(V, V.shape[0] + 8, np.random.default_rng(1)).T % p)   # left kernel vectors (rows)

def quad_span(X):
    """X: (m, g, n1) basis of a space of g x n1 matrices; returns (rank of the span of all 2x2 minors as quadrics in c, #quadrics)."""
    m, g, n1 = X.shape
    pairs = [(a, b) for a in range(m) for b in range(a, m)]
    inv2 = pow(2, p - 2, p); rows = []
    for i1, i2 in itertools.combinations(range(g), 2):
        for j1, j2 in itertools.combinations(range(n1), 2):
            Q = (np.outer(X[:, i1, j1], X[:, i2, j2]) - np.outer(X[:, i1, j2], X[:, i2, j1])) % p
            Q = (Q + Q.T) % p
            rows.append([Q[a, b] if a != b else Q[a, a] * inv2 % p for a, b in pairs])
    return frank(np.array(rows, dtype=np.int64)), len(pairs)

def sections(Fs, g, n1, rng, name):
    """for k = 2..g: random k-dim P in M^*, K_P = kernel of the V-stack on P (x) X1^*; quadric test on K_P."""
    res = []
    for k in range(2, g + 1):
        C = rng.integers(0, p, (k, g))
        Gs = [m2lib.combine(Fs, C[i]) for i in range(k)]
        V = np.vstack(Gs)
        Kb = nullspace(compress_cols(V, V.shape[0] + 8, rng).T % p)
        m = len(Kb)
        if m == 0:
            res.append('k%d:K=0' % k); continue
        if m * (m + 1) // 2 > 2000:
            res.append('k%d:K=%d(big)' % (k, m)); break
        r, nq = quad_span(np.array(Kb, dtype=np.int64).reshape(m, k, n1))
        res.append('k%d:K=%d,%d/%d%s' % (k, m, r, nq, '(no rank1)' if r == nq else ''))
    return '%s sections: %s' % (name, ' '.join(res))

def run(lam, dirn, seed=17, maxm=60):
    rng = np.random.default_rng([seed] + [x for l in lam for x in l] + [dirn])
    perm = [dirn] + [t for t in range(3) if t != dirn]
    lam_p = tuple(lam[t] for t in perm); g = kronecker(*lam)
    n1 = dim_schur(lam_p[0], 4); n23 = dim_schur(lam_p[1], 4) * dim_schur(lam_p[2], 4)
    tens = {'R6a': rand_tensor(rng, 6), 'R7': rand_tensor(rng, 7), 'M2': m2_terms('strassen')}
    tens = {k: tuple(v[t] for t in perm) for k, v in tens.items()}
    fills = choose_fillings(lam_p, g, tens['R7'], rng)
    # exactly n1 source points that are independent (checked on R7's stacked flattening): then coordinates on X1^* are exact
    K = min(g * n1, n23) + 8
    gs = random_gs(rng, 4, n1, K)
    out = []
    for name, v in tens.items():
        Fs = [flatlib.flat(f, v, gs) % p for f in fills]
        H = np.hstack(Fs)
        if name == 'R7' and frank(H) < n1:
            print('source points dependent; retry'); return
        out.append(sections(Fs, g, n1, rng, name))
        Kb = kernel_basis(Fs, n1, rng)                  # rows: vectors in C^{g n1}, index (j, y)
        m = len(Kb)
        if m == 0:
            out.append('%s: dim K = 0 (V_g injective)' % name); continue
        if m > maxm:
            out.append('%s: dim K = %d (too big for the quadric test)' % (name, m)); continue
        X = np.array(Kb, dtype=np.int64).reshape(m, g, n1)        # X(c) = sum_a c_a X[a]
        pairs = [(a, b) for a in range(m) for b in range(a, m)]
        rows = []
        for i1, i2 in itertools.combinations(range(g), 2):
            for j1, j2 in itertools.combinations(range(n1), 2):
                # minor = X_{i1 j1} X_{i2 j2} - X_{i1 j2} X_{i2 j1}, bilinear in c
                u1, u2, w1, w2 = X[:, i1, j1], X[:, i2, j2], X[:, i1, j2], X[:, i2, j1]
                Q = (np.outer(u1, u2) - np.outer(w1, w2)) % p
                Q = (Q + Q.T) % p
                rows.append([Q[a, b] if a != b else Q[a, a] * pow(2, p - 2, p) % p for a, b in pairs])
                if len(rows) >= 40 * len(pairs): break
            if len(rows) >= 40 * len(pairs): break
        r = frank(np.array(rows, dtype=np.int64))
        out.append('%s: dim K = %d, span of 2x2 minors = %d / %d quadrics%s' % (name, m, r, len(pairs),
                   ' => NO rank-one element (no drop point)' if r == len(pairs) else ''))
    print('lam=%s dir%d g=%d n1=%d n23=%d | %s' % (lam, dirn + 1, g, n1, n23, ' | '.join(out))); sys.stdout.flush()

if __name__ == '__main__':
    run(eval(sys.argv[1]), int(sys.argv[2]))
