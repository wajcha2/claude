"""python3 m2_bound.py d [gmin]
Upper bound for the rank of every isotypic flattening of M2 (2x2 matrix multiplication) from its GL2^3 symmetry.
A = U (x) V^*, B = V (x) W^*, C = W (x) U^*; M2 is G = GL(U) x GL(V) x GL(W)-invariant, so for every phi in M^* the
isotypic tensor Phi_phi(M2) in S^{l1}A (x) S^{l2}B (x) S^{l3}C is G-invariant and its flattening
S^{l1}A^* -> S^{l2}B (x) S^{l3}C is G-equivariant.  By Schur's lemma, with mu, nu, xi partitions of d with <= 2 rows,
   S^{l1}A^* = sum a_{mu nu} S^mu U^* (x) S^nu V,          a_{mu nu} = g(l1, mu, nu),
   multiplicity of S^mu U^* (x) S^nu V (x) triv_W in S^{l2}B (x) S^{l3}C:  b_{mu nu} = sum_xi g(l2, nu, xi) g(l3, xi, mu),
   rank <= sum_{mu, nu} (mu1 - mu2 + 1)(nu1 - nu2 + 1) min(a_{mu nu}, b_{mu nu}),
and dim (S^{l1}A (x) S^{l2}B (x) S^{l3}C)^G = sum a_{mu nu} b_{mu nu}.  Directions 2, 3 by cyclic symmetry of M2."""
import sys, itertools
from isoflat import partitions, kronecker
from hwv import dim_schur

def bound(lam, dirn, two):
    l1, l2, l3 = lam[dirn], lam[(dirn + 1) % 3], lam[(dirn + 2) % 3]     # cyclic: M2 is invariant under cyclic shift
    tot, inv = 0, 0
    for mu in two:
        for nu in two:
            a = kronecker(l1, mu, nu)
            if not a: continue
            b = sum(kronecker(l2, nu, xi) * kronecker(l3, xi, mu) for xi in two)
            inv += a * b
            dm = mu[0] - (mu[1] if len(mu) > 1 else 0) + 1; dn = nu[0] - (nu[1] if len(nu) > 1 else 0) + 1
            tot += dm * dn * min(a, b)
    return tot, inv

if __name__ == '__main__':
    d = int(sys.argv[1]); gmin = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    two = partitions(d, 2)
    for lam in itertools.combinations_with_replacement(partitions(d, 4), 3):
        g = kronecker(*lam)
        if g < gmin: continue
        out = []
        for dirn in range(3):
            n1 = dim_schur(lam[dirn], 4)
            n23 = dim_schur(lam[(dirn + 1) % 3], 4) * dim_schur(lam[(dirn + 2) % 3], 4)
            b, inv = bound(lam, dirn, two)
            out.append('dir%d n1=%d n23=%d M2bound=%d' % (dirn + 1, n1, n23, b))
        print('lam=%s g=%d dimInv=%d | %s' % (lam, g, inv, ' | '.join(out))); sys.stdout.flush()
