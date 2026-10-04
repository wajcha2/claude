"""Why phi(iso_lam(M2^{(x)8})) = 0 for a nonzero phi in M^*: a symmetry count (exact, characters only).
lam = (l, m, m) = ((6,2),(3,2,2,1),(3,2,2,1)), M = ([l] (x) [m] (x) [m])^{S_8}, g = dim M = 4.
G = GL2^3 acting on A = U (x) V^*, B = V (x) W^*, C = W (x) U^* (a_ij = u_i v_j^*, b_jk = v_j w_k^*, c_ki = w_k u_i^*) fixes
M2 = sum a_ij b_jk c_ki; tau = (P, P, P) o swap_BC, P = transpose of the 2x2 index (e_{2i+j} -> e_{2j+i}), fixes M2 too
and normalises G.  Hence iso(M2) lies in (W (x) M)^tau, W = (S^l A (x) S^m B (x) S^m C)^G, and tau acts on M by the swap
of the two [m] factors.  If that swap is trivial on M, phi -> phi(iso(M2)) maps M^* into W^+ (tau-fixed part of W), so
dim K_M2 >= g - dim W^+.
* dim W = int_{U(2)^3} s_l(x/y) s_m(y/z) s_m(z/x)                                   (Weyl integration, constant terms)
* tr(tau | W) = int s_l(eig P(X (x) Y^-T)) s_m(eig(X^-T Y (x) Z Z^-T)) = E_z[ s_l(z1, z2, s, -s) E_t[ s_m(-t^{+-2}/z_a) ] ],
  z = eigenvalues of a Haar U(2) element (s^2 = z1 z2), t, 1/t = eigenvalues of a Haar SU(2) element.
* dim M^+ (swap of the two [m]) = < chi_l, chi_{S^2 [m]} >_{S_8}  (Murnaghan-Nakayama)."""
import itertools
from fractions import Fraction
from math import factorial
from collections import Counter
import sympy as sp

l, m = (6, 2), (3, 2, 2, 1)
d = sum(l)

def schur(lam, xs):
    """Schur polynomial s_lam(xs) via Jacobi-Trudi (complete homogeneous h_k)."""
    n = len(xs)
    def h(k):
        if k < 0: return 0
        return sum(sp.prod(c) for c in itertools.combinations_with_replacement(xs, k)) if k else 1
    lam = list(lam) + [0] * (n - len(lam))
    return sp.expand(sp.Matrix(n, n, lambda i, j: h(lam[i] - i + j)).det())

def CT(expr, vars_):
    """constant term of a Laurent polynomial."""
    P = sp.Poly(sp.expand(expr * sp.prod([v ** 40 for v in vars_])), *vars_)
    return P.coeff_monomial(sp.prod([v ** 40 for v in vars_]))

X = sp.symbols('X0:4')
sl, sm = schur(l, X), schur(m, X)
# ---- dim W
x1, x2, y1, y2, z1, z2, t, s = sp.symbols('x1 x2 y1 y2 z1 z2 t s')
weyl2 = lambda a, b: sp.Rational(1, 2) * (1 - a / b) * (1 - b / a)
sub = lambda f, vals: sp.expand(f.subs(dict(zip(X, vals)), simultaneous=True))
fA = sub(sl, [x1 / y1, x1 / y2, x2 / y1, x2 / y2])
fB = sub(sm, [y1 / z1, y1 / z2, y2 / z1, y2 / z2])
fC = sub(sm, [z1 / x1, z1 / x2, z2 / x1, z2 / x2])
dimW = CT(sp.expand(fA * fB * fC * weyl2(x1, x2) * weyl2(y1, y2) * weyl2(z1, z2)), [x1, x2, y1, y2, z1, z2])
print('dim W = dim (S^l A (x) S^m B (x) S^m C)^{GL2^3} =', dimW)
# ---- tr(tau | W)
gA = sp.expand(sub(sl, [z1, z2, s, -s]))
gA = sp.expand(sum(c * z1 ** a * z2 ** b * (z1 * z2) ** (e // 2) for (a, b, e), c in sp.Poly(gA, z1, z2, s).terms() if e % 2 == 0))
zeta = [-t ** 2, -t ** -2]
gBC = sub(sm, [zz / za for za in (z1, z2) for zz in zeta])
inner = sp.expand(CT(sp.expand(gBC * sp.Rational(1, 2) * (1 - t ** 2) * (1 - t ** -2)), [t]))
trW = CT(sp.expand(gA * inner * weyl2(z1, z2)), [z1, z2])
print('tr(tau | W) =', trW, ' => dim W^+ =', (dimW + trW) / 2, ', dim W^- =', (dimW - trW) / 2)
# ---- S_8 characters (Murnaghan-Nakayama with beta-sets)
def chi(lam, rho):
    lam = [x for x in lam if x]
    k = len(lam); beta = frozenset(lam[i] + k - 1 - i for i in range(k))
    def rec(beta, rho):
        if not rho: return 1
        r, rest = rho[0], rho[1:]; tot = 0
        for b in beta:
            if b - r >= 0 and (b - r) not in beta:
                sgn = (-1) ** sum(1 for c in beta if b - r < c < b)
                tot += sgn * rec((beta - {b}) | {b - r}, rest)
        return tot
    return rec(beta, tuple(rho))
def partitions(n, mx=None):
    mx = n if mx is None else mx
    if n == 0: yield (); return
    for k in range(min(n, mx), 0, -1):
        for q in partitions(n - k, k): yield (k,) + q
def csize(rho):
    c = Counter(rho); den = 1
    for k, e in c.items(): den *= k ** e * factorial(e)
    return Fraction(factorial(sum(rho)), den)
def square(rho):
    out = []
    for c in rho: out += [c // 2, c // 2] if c % 2 == 0 else [c]
    return tuple(sorted(out, reverse=True))
g = sum(csize(r) * chi(l, r) * chi(m, r) ** 2 for r in partitions(d)) / factorial(d)
gp = sum(csize(r) * chi(l, r) * Fraction(chi(m, r) ** 2 + chi(m, square(r)), 2) for r in partitions(d)) / factorial(d)
print('g = dim M =', g, '; swap of the two [m] factors on M: dim M^+ =', gp, ', dim M^- =', g - gp)
print('=> rank of phi -> phi(iso(M2)) <= dim W^+ * [M^- = 0] ... ; lower bound dim K_M2 >=',
      max(0, g - min(g, (dimW + trW) / 2)) if g == gp else 'n/a (M^- != 0)')
