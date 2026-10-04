"""python3 m2_bound_stacks.py d   -- GL2^3 bounds for M2 on all flattening types of the 4-way isotypic tensor
(see m2_bound.py).  For a k-dim U in M^* and direction N (source S^{lN}):
  gen (k=1): rank <= sum_{mu nu} D_mu D_nu min(a, b)                generic tensor: min(n1, n23)
  H_k (stack x -> (F_phi1 x, ..., F_phik x)): <= sum D D min(a, k b)   generic: min(n1, k n23)
  V_k (U (x) S^{lN}V^* -> rest, sum of images): <= sum D D min(k a, b)  generic: min(k n1, n23)
Prints, for every component with g >= 2 and direction, the k (1..g) at which the M2 bound equals the generic upper bound."""
import sys, itertools
from isoflat import partitions, kronecker
from hwv import dim_schur

def blocks(lam, dirn, two):
    l1, l2, l3 = lam[dirn], lam[(dirn + 1) % 3], lam[(dirn + 2) % 3]
    out = []
    for mu in two:
        for nu in two:
            a = kronecker(l1, mu, nu)
            if not a: continue
            b = sum(kronecker(l2, nu, xi) * kronecker(l3, xi, mu) for xi in two)
            D = (mu[0] - (mu[1] if len(mu) > 1 else 0) + 1) * (nu[0] - (nu[1] if len(nu) > 1 else 0) + 1)
            out.append((D, a, b))
    return out

if __name__ == '__main__':
    d = int(sys.argv[1]); two = partitions(d, 2)
    for lam in itertools.combinations_with_replacement(partitions(d, 4), 3):
        g = kronecker(*lam)
        if g < 2: continue
        for dirn in range(3):
            n1 = dim_schur(lam[dirn], 4); n23 = dim_schur(lam[(dirn + 1) % 3], 4) * dim_schur(lam[(dirn + 2) % 3], 4)
            bl = blocks(lam, dirn, two)
            assert sum(D * a for D, a, b in bl) == n1
            inv = sum(a * b for D, a, b in bl)
            H = [sum(D * min(a, k * b) for D, a, b in bl) for k in range(1, g + 1)]
            V = [sum(D * min(k * a, b) for D, a, b in bl) for k in range(1, g + 1)]
            Hg = [min(n1, k * n23) for k in range(1, g + 1)]; Vg = [min(k * n1, n23) for k in range(1, g + 1)]
            print('lam=%s g=%d dir%d n1=%d n23=%d inv=%d | H(M2bound/generic): %s | V: %s' % (lam, g, dirn + 1, n1, n23, inv,
                  ' '.join('%d/%d' % x for x in zip(H, Hg)), ' '.join('%d/%d' % x for x in zip(V, Vg))))
            sys.stdout.flush()
