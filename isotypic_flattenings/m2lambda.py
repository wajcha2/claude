"""python3 m2lambda.py "lam" dirn k [npts]
Extract linear components of the 1-dim drop locus of codimension k-1: for random k-dim P in M^*, K_P(T) = ker of the V-stack on
P (x) X1^*; when K_P(T) = phi_0 (x) W (all elements of rank one, same row) phi_0 is the unique point of P(P) on the drop locus.
Collect such points for R6a, R6b, R7 (and M2), report the span of the points (the linear component Lambda_T), whether the
Lambda's of different tensors coincide, and the ranks of all tensors at random points of each Lambda."""
import sys, os, numpy as np
import m2lib
from m2lib import p, dim_schur, kronecker, random_gs, frank, choose_fillings, rand_tensor, m2_terms, compress_cols, combine
import flatlib
from specialU import nullspace

def run(lam, dirn, k, npts=6, seed=19):
    rng = np.random.default_rng([seed] + [x for l in lam for x in l] + [dirn, k])
    perm = [dirn] + [t for t in range(3) if t != dirn]
    lam_p = tuple(lam[t] for t in perm); g = kronecker(*lam)
    n1 = dim_schur(lam_p[0], 4); n23 = dim_schur(lam_p[1], 4) * dim_schur(lam_p[2], 4)
    tens = {'R6a': rand_tensor(rng, 6), 'R6b': rand_tensor(rng, 6), 'R7': rand_tensor(rng, 7), 'M2': m2_terms('strassen')}
    tens = {kk: tuple(v[t] for t in perm) for kk, v in tens.items()}
    fills = choose_fillings(lam_p, g, tens['R7'], rng)
    K = min(k * n1, n23) + 8
    gs = random_gs(rng, 4, n1, K)          # exactly n1 source points (independent w.h.p.)
    F = {kk: [flatlib.flat(f, v, gs) % p for f in fills] for kk, v in tens.items()}
    assert frank(np.hstack(F['R7'])) == n1, 'source points dependent'
    Lam = {}
    for name in tens:
        pts, info = [], []
        for _ in range(npts):
            C = rng.integers(0, p, (k, g))
            V = np.vstack([combine(F[name], C[i]) for i in range(k)])
            Kb = nullspace(compress_cols(V, V.shape[0] + 8, rng).T % p)
            if not len(Kb): info.append('K=0'); continue
            X = np.array(Kb, dtype=np.int64).reshape(len(Kb), k, n1)
            # row space of the span: rank of the k x (m n1) matrix [X_1 | ... | X_m]
            R = np.hstack(list(X)) % p
            rr = frank(R)
            info.append('K=%d,rowrank=%d' % (len(Kb), rr))
            if rr == 1:
                row = nullspace(R.T % p)        # vectors w with w^T R = 0 (dimension k-1); phi_0 coefficient = orthogonal complement
                # phi_0 in P-coordinates: the nonzero row combination: take the column space of R (1-dim)
                col = R[:, np.flatnonzero(R.any(axis=0))[0]]
                phi = (col @ C) % p            # point of M^* (coefficients in the filling basis)
                pts.append(phi)
        span = frank(np.array(pts)) if pts else 0
        Lam[name] = np.array(pts) if pts else None
        print('%s: %s; points found %d, dim of their span %d' % (name, ' '.join(info), len(pts), span)); sys.stdout.flush()
    names = [n for n in tens if Lam[n] is not None]
    for a in names:
        for b in names:
            if a < b:
                print('span(Lambda_%s + Lambda_%s) = %d' % (a, b, frank(np.vstack([Lam[a], Lam[b]]))))
    for a in names:
        sp = Lam[a]
        for _ in range(2):
            c = rng.integers(0, p, len(sp))
            phi = (c @ sp) % p
            rk = {n: frank(combine(F[n], phi)) for n in tens}
            print('random point of Lambda_%s: ranks %s' % (a, rk)); sys.stdout.flush()

if __name__ == '__main__':
    run(eval(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else 6)
