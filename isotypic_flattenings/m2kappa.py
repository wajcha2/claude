"""python3 m2kappa.py "lam" dirn      -- the V-stack kernels K(T) and their M^*-supports.
K(T) = ker(V_g(T): M^* (x) X1^* -> X2 (x) X3); a kernel element kappa = sum_j phi_j (x) x_j is a g x n1 matrix (rows: the
basis of M^* given by the fillings; columns: coordinates on X1^* from exactly n1 independent source points).  Its M^*-support
U_kappa = column space (dim = rank).  A V-type U separates rank 6 from rank 7 iff dim(K(R6) cap U (x) X1^*) >
dim(K(R7) cap U (x) X1^*); with dim K = 1 that means U >= U_kappa(R6) for all rank-6 tensors but not U >= U_kappa(R7).
Printed: dim K, rank and support of each kernel element, and the dimension of sums of supports across tensors."""
import sys, numpy as np
import m2lib
from m2lib import p, dim_schur, kronecker, random_gs, frank, choose_fillings, rand_tensor, m2_terms, compress_cols, combine
import flatlib
from specialU import nullspace

def run(lam, dirn, seed=23, nr6=3):
    rng = np.random.default_rng([seed] + [x for l in lam for x in l] + [dirn])
    perm = [dirn] + [t for t in range(3) if t != dirn]
    lam_p = tuple(lam[t] for t in perm); g = kronecker(*lam)
    n1 = dim_schur(lam_p[0], 4); n23 = dim_schur(lam_p[1], 4) * dim_schur(lam_p[2], 4)
    tens = {('R6%d' % i): rand_tensor(rng, 6) for i in range(nr6)}
    tens.update({'R7a': rand_tensor(rng, 7), 'R7b': rand_tensor(rng, 7), 'M2': m2_terms('strassen')})
    tens = {k: tuple(v[t] for t in perm) for k, v in tens.items()}
    fills = choose_fillings(lam_p, g, tens['R7a'], rng)
    K = min(g * n1, n23) + 8
    gs = random_gs(rng, 4, n1, K)
    sup = {}
    for name, v in tens.items():
        Fs = [flatlib.flat(f, v, gs) % p for f in fills]
        if name == 'R7a': assert frank(np.hstack(Fs)) == n1, 'source points dependent'
        V = np.vstack(Fs)
        Kb = nullspace(compress_cols(V, V.shape[0] + 8, rng).T % p)
        mats = [np.array(k, dtype=np.int64).reshape(g, n1) for k in Kb]
        if len(mats) > 12:
            print('%s: dim K = %d (large; support of the whole kernel %d)' % (name, len(mats), frank(np.hstack(mats)))); continue
        ranks = [frank(M) for M in mats]
        S = np.hstack(mats) if mats else np.zeros((g, 0), dtype=np.int64)
        sup[name] = S
        print('%s: dim K = %d, ranks of kernel basis elements %s, dim support of K = %d' % (name, len(mats), ranks, frank(S) if mats else 0))
    names = list(sup)
    for i, a in enumerate(names):
        print('  support dims of sums: ' + ' '.join('%s+%s=%d' % (a, b, frank(np.hstack([sup[a], sup[b]]))) for b in names[i + 1:]))
    sys.stdout.flush()

if __name__ == '__main__':
    run(eval(sys.argv[1]), int(sys.argv[2]))
