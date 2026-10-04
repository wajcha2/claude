"""specialscan.py -- special subspaces U of the multiplicity space M^* of an isotypic component (PROMPT_specialU.md).

    python3 specialscan.py n d "lam"|all R [method ...]      (env: DIRS, SEED, NLINES, OUT, WORKER/NWORKERS, LIST, ...)
    R = target ranks: 'r' or 'rlo-rhi' (separation r vs r+1 for every r in R)

For a component lam = (l1, l2, l3) of degree d with Kronecker coefficient g >= 2 and a direction t (source factor
l_t), rankscan.Direction chooses g fillings with independent functionals and the sampled evaluation points
(N1 = min(n1, g n23) + 8 source points, K = min(g n1, n23) + 8 target pairs).  For every tensor T the g matrices
F_i(T) (N1 x K) are computed ONCE (Comp.F) and every candidate U is tested on them: for a basis c_1..c_m of U,
phi_j = sum_i c_j[i] F_i, and
    H_U : S^{l_t}V^* -> U^* (x) S^{l_u}V (x) S^{l_v}V  = rank of [phi_1 | ... | phi_m]   (<= min(n1, m n23))
    V_U : U (x) S^{l_t}V^* -> S^{l_u}V (x) S^{l_v}V    = rank of the vertical stack     (<= min(m n1, n23)),
with the prefix ranks of an ordered basis giving the nested subspaces (exact incremental elimination mod p,
rankscan.RREF).  'U separates r' = rank on a general rank-r tensor < rank on a general rank-(r+1) tensor.

Methods (argument list; default 'line flag'):
  line   rank-drop points on random lines a + t b of P(M^*) (complete for g = 2; for g >= 3 it sees the codim-1
         part of the drop locus).  For two independent rank-r tensors Ta, Tb: rho = rank on the line (generic t),
         drop polynomial = minimal polynomial of -B'^{-1}A' (A' = R F_a S, B' = R F_b S, random rho x N1 / K x rho
         projections; its roots are the roots of det(A' + t B'), which contain every drop point), exact mod p with
         python-flint; gcd over Ta and Tb = tensor-independent drop points (plus, rarely, chance coincidences).
         Every irreducible factor f of the gcd (degree e, point theta = root of f in F_{p^e}) is tested on Ta, Tb, a
         third rank-r tensor Tc (a true tensor-independent point must lower Tc too) and a rank-(r+1) tensor, over
         F_{p^e} via the F_p-matrix sum_k G_k (x) C_f^k (rank = e * rank over F_{p^e}).  Then k >= 2: U spanned by
         all rational drop points of the lines (and by the rational drop points of each line), H and V prefixes.
  flag   U_k = {phi : phi(iso_lam(T^{(x)d})) = 0 for T of rank <= k} (null space of probe values of g functionals on
         4 random rank-k tensors, 8 x 64 probe points each), k = 1..d-1, and the eigenspaces E+/E- of the factor
         swaps when two partitions of lam are equal, and their intersections with the U_k.  For each such W
         (0 < dim W < g): ordered basis [random basis of W, random complement] -> prefix ranks: generic subspaces of W
         of every dimension, W itself, W + generic vectors; plus one flag-adapted basis (U_kmax < ... < U_1 < M^*).
  pflag  lines through a generic element of each W of 'flag' and lines inside W (dim W >= 2): drop points as in 'line'.
Ranks are evaluated on tensors of rank r-1 (if r > 1), r (two), r+1 and r+2 for every r in the list
(frontier formats: several r).  Every record (one JSON line per component and direction) lists all cases checked,
wall/CPU time and peak RSS.
Env: DIRS (comma list of directions 1..3, default: distinct ones), SEED (11), NLINES (2), EMAXSIZE (e * max(N1,K)
     cap for extension-field points, default 6000), OUT (default special/res/n<n>_d<d>.jsonl), PRIME (other prime).
"""
import os, sys, time, json, itertools, zlib, collections, glob
import hwv, isoflat
if os.environ.get('PRIME'):
    hwv.p = isoflat.p = int(os.environ['PRIME'])          # before hwv_fast / rankscan import p
import numpy as np
import flint
import rankscan
from rankscan import (Direction, RREF, compute_F, generic_rank, word_minor_size, distinct_dirs, col_lengths,
                      minors_of_points, minors_of_vectors, peak_rss_mb, reset_peak_rss, Infeasible, _mm)
from hwv import random_gs, dim_schur
from isoflat import kronecker

p = rankscan.p
EMAXSIZE = int(os.environ.get('EMAXSIZE', '6000'))
CACHE = int(os.environ.get('CACHE', '5'))
PRB = 8                       # probe grid: PRB source points x PRB^2 target pairs


def log(*a):
    print(*a, flush=True)


# ---------------------------------------------------------------- linear algebra mod p
def fmodp(A):
    return np.fmod(A, p)


def combo(Fs, c):
    """sum_i c[i] Fs[i] mod p (float64; Fs float64 or float32 residues)."""
    A = np.zeros(Fs.shape[1:])
    for i, ci in enumerate(c):
        ci = int(ci) % p
        if ci:
            A += float(ci) * Fs[i].astype(np.float64, copy=False)
            if (i + 1) % 16 == 0:
                A = np.fmod(A, p)
    return np.fmod(A, p)


def rank(M):
    if M.size == 0:
        return 0
    if M.shape[0] > M.shape[1]:
        M = M.T
    return RREF(M.shape[1]).add(M)


def to_flint(M):
    return flint.nmod_mat(np.asarray(M, dtype=np.int64).tolist(), p)


def nullspace(M):
    """rows spanning {x : M x = 0} over F_p (M: (m, g) residues)."""
    M = np.asarray(M, dtype=np.int64) % p
    if M.shape[0] == 0:
        return np.eye(M.shape[1], dtype=np.int64)
    X, k = to_flint(M).nullspace()
    return np.array([[int(X[i, j]) for i in range(M.shape[1])] for j in range(k)], dtype=np.int64).reshape(k, M.shape[1])


def rowspace_basis(C):
    """independent rows spanning the row space of C (mod p)."""
    C = np.asarray(C, dtype=np.int64) % p
    if C.shape[0] == 0:
        return C
    R = to_flint(C).rref()[0]
    rows = [[int(R[i, j]) for j in range(C.shape[1])] for i in range(R.nrows())]
    return np.array([r for r in rows if any(r)], dtype=np.int64).reshape(-1, C.shape[1])


def intersect(A, B, g):
    """basis of rowspan(A) cap rowspan(B)."""
    if len(A) == 0 or len(B) == 0:
        return np.zeros((0, g), dtype=np.int64)
    # x = a A = b B  <=>  [a, -b] in null([A; B]^T)
    N = nullspace(np.vstack([A, B]).T)
    if len(N) == 0:
        return np.zeros((0, g), dtype=np.int64)
    X = (N[:, :len(A)] @ A) % p
    return rowspace_basis(X)


def random_basis(W, m, rng):
    """m random combinations of the rows of W (a random basis if m = dim W)."""
    return (rng.integers(0, p, (m, len(W))) @ W) % p if len(W) else np.zeros((0, W.shape[1]), dtype=np.int64)


def complete_basis(W, g, rng):
    """[random basis of W; random vectors] (g x g, invertible w.h.p.)."""
    B = random_basis(W, len(W), rng)
    return np.vstack([B, rng.integers(0, p, (g - len(W), g))]) if len(W) < g else B


def companion_powers(f):
    """f: monic coefficient list low..high of degree e; returns [C^0, ..., C^(e-1)] (int64), C = companion of f."""
    e = len(f) - 1
    C = np.zeros((e, e), dtype=np.int64)
    C[np.arange(1, e), np.arange(e - 1)] = 1
    C[:, e - 1] = (-np.array(f[:e], dtype=np.int64)) % p
    P = [np.eye(e, dtype=np.int64)]
    for _ in range(e - 1):
        P.append((P[-1] @ C) % p)
    return P


def ext_rank(Gs, f):
    """rank over F_{p^e} = F_p[x]/(f) of sum_k theta^k G_k (G_k: N x K residues, f monic irreducible of degree e)."""
    e = len(f) - 1
    if e == 1:
        th = (-int(f[0])) % p
        M = Gs[0].copy()
        for k in range(1, len(Gs)):
            M = np.fmod(M + float(pow(th, k, p)) * Gs[k], p)
        return rank(M)
    P = companion_powers(f)
    # theta^k for k >= e reduced: use matrix powers C^k directly
    while len(P) < len(Gs):
        P.append((P[-1] @ P[1]) % p if e > 1 else P[0])
    N, K = Gs[0].shape
    M = np.zeros((N * e, K * e))
    for k, G in enumerate(Gs):
        M += np.kron(G, P[k].astype(np.float64))
        M = np.fmod(M, p)
    r = rank(M)
    assert r % e == 0, (r, e)
    return r // e


# ---------------------------------------------------------------- one component, one direction
class Comp:
    """fillings, evaluation points and cached F_i(T) for one component lam and one direction t."""

    def __init__(self, n, lam, t, seed, probe_rank):
        self.n, self.lam, self.t = n, lam, t
        self.g = kronecker(*lam)
        self.seed = seed
        flat = [x for l in lam for x in l]
        self.crng = np.random.default_rng([seed, n, t] + flat)
        self.vecs = {'probe': self.rand_tensor(probe_rank, 'probe')}
        self.D = Direction(n, lam, self.g, t, self.crng, self.vecs, 'probe')
        D = self.D
        assert D.span == self.g, 'fillings span only %d of g = %d' % (D.span, self.g)
        self.lam_p, self.perm = D.lam_p, D.perm
        self.n1, self.n23, self.N1, self.K = D.n1, D.n23, D.N1, D.K
        self.cache = {}
        # probe grid for U_k and swaps: points G[u] (PRB each), pairs (b, c) in PRB x PRB
        G = random_gs(self.crng, n, PRB, PRB)
        self.G = G
        bb, cc = np.meshgrid(np.arange(PRB), np.arange(PRB), indexing='ij')
        self.bb, self.cc = bb.ravel(), cc.ravel()

    def rand_tensor(self, r, name):
        h = zlib.crc32(name.encode())
        rng = np.random.default_rng([self.seed, self.n, r, h, 4242])
        return tuple(rng.integers(0, p, (r, self.n)) for _ in range(3))

    def add_tensor(self, name, r):
        if name not in self.vecs:
            self.vecs[name] = self.rand_tensor(r, name)

    def vm_of(self, V, lam_p):
        return [{L: minors_of_vectors(V[u], L) for L in col_lengths(lam_p[u])} for u in range(3)]

    def F(self, name):
        """(g, N1, K) array of the filling matrices at tensor `name` (computed once)."""
        if name not in self.cache:
            t0 = time.time()
            vm = self.D.vm(name)
            g, N1, K = self.g, self.N1, self.K
            Fs = np.empty((g, N1, K), dtype=np.float64 if g * N1 * K <= (1 << 24) else np.float32)
            for i, fl in enumerate(self.D.fillings):
                Fs[i] = compute_F(fl[0], vm, self.D.pm, fl[1], fl[2])
            # keep at most CACHE tensors (the oldest is dropped; memory g N1 K per tensor)
            while len(self.cache) >= CACHE:
                self.cache.pop(next(iter(self.cache)))
            self.cache[name] = Fs
            self.ftime = getattr(self, 'ftime', 0.0) + time.time() - t0
        return self.cache[name]

    def drop(self, name):
        self.cache.pop(name, None)

    def P(self, r):
        """name of the profile tensor of rank r (one random tensor per rank)."""
        nm = 'P%d' % r
        self.add_tensor(nm, r)
        return nm

    # ---- probes (small grids, for U_k and swaps)
    def probe_cube(self, fill, V):
        """values of filling `fill` (3 column lists, lam_p order) at tensor V (factors in lam_p order) on the cube
        G0 x G1 x G2: Q[a0, a1, a2] (PRB^3)."""
        pm = [{L: minors_of_points(self.G[0], L) for L in col_lengths(self.lam_p[0])},
              {L: minors_of_points(self.G[1][self.bb], L) for L in col_lengths(self.lam_p[1])},
              {L: minors_of_points(self.G[2][self.cc], L) for L in col_lengths(self.lam_p[2])}]
        return compute_F(fill, self.vm_of(V, self.lam_p), pm, cheap=True).reshape(PRB, PRB, PRB).astype(np.int64)

    def probe_matrix(self, V):
        """(PRB^3, g): probe values of the g basis functionals at tensor V (lam_p order)."""
        return np.stack([self.probe_cube(fl[0], V).ravel() for fl in self.D.fillings], axis=1)

    def tensor_p(self, name):
        V = self.vecs[name]
        return tuple(V[u] for u in self.perm)


# ---------------------------------------------------------------- rank profiles over a range of tensor ranks
def resolve_profile(fn, rlo, rhi):
    """fn(r) -> profile (list of lists of ints, componentwise non-decreasing in r).  Evaluates rlo and rhi, then
    bisects every interval whose ends differ (equal ends prove that nothing changes inside).  {r: profile}."""
    prof = {rlo: fn(rlo)}
    if rhi > rlo:
        prof[rhi] = fn(rhi)
    stack = [(rlo, rhi)]
    while stack:
        x, y = stack.pop()
        if y - x < 2 or prof[x] == prof[y]:
            continue
        m = (x + y) // 2
        prof[m] = fn(m)
        stack += [(x, m), (m, y)]
    return dict(sorted(prof.items()))


def value_at(prof, r):
    """profile value at r (from the evaluated points: constant between equal ends)."""
    lo = max(x for x in prof if x <= r)
    return prof[lo]


def separations(prof, targets, g, kind='HV'):
    """['r10:H2 900<902', ...] for r in targets with r, r+1 inside the evaluated range.  Profiles are [H, V] lists
    (kind 'HV') or [[rank]] (kind 'pt').  Prefix g (= all of M^*) and V_1 (= H_1) are skipped."""
    out = []
    lo, hi = min(prof), max(prof)
    for r in targets:
        if not (lo <= r and r + 1 <= hi):
            continue
        A, B = value_at(prof, r), value_at(prof, r + 1)
        if kind == 'pt':
            if A[0][0] < B[0][0]:
                out.append('r%d:%d<%d' % (r, A[0][0], B[0][0]))
            continue
        for typ, i in (('H', 0), ('V', 1)):
            for k in range(len(A[i])):
                if (typ == 'V' and k == 0) or k == g - 1:
                    continue
                if A[i][k] < B[i][k]:
                    out.append('r%d:%s%d %d<%d' % (r, typ, k + 1, A[i][k], B[i][k]))
    return out


def fmt_prof(prof):
    return ' '.join('r%d H%s V%s' % (r, v[0], v[1][1:]) for r, v in prof.items())


def prefix_HV(cp, name, C, H=True, V=True):
    """prefix ranks [H, V] for the ordered basis C (m x g) at tensor `name`."""
    Fs = cp.F(name)
    EH, EV = RREF(cp.N1), RREF(cp.K)
    hs, vs = [], []
    for j in range(len(C)):
        P = None
        if H:
            if EH.rank < cp.n1:
                P = combo(Fs, C[j]); EH.add(P.T)
            hs.append(EH.rank)
        if V:
            if EV.rank < cp.n23:
                P = combo(Fs, C[j]) if P is None else P
                EV.add(P)
            vs.append(EV.rank)
    return [hs, vs]


def ordering_profile(cp, C, R):
    """{r: [H prefixes, V prefixes]} at tensors 'P<r>' for r in [min R, max R + 1] (ends + bisection)."""
    return resolve_profile(lambda r: prefix_HV(cp, cp.P(r), C), min(R), max(R) + 1)


def test_orderings(cp, orderings, R, rec, method='flag'):
    """orderings: list of (name, C (m x g), meaning)."""
    for oname, C, meaning in orderings:
        prof = ordering_profile(cp, C, R)
        seps = separations(prof, R, cp.g)
        rec['cases'].append({'method': method, 'U': oname, 'meaning': meaning, 'dim': len(C),
                             'prof': {str(r): v for r, v in prof.items()}, 'sep': seps})
        if seps:
            rec['hits'].append({'method': method, 'U': oname, 'meaning': meaning, 'sep': seps,
                                'prof': {str(r): v for r, v in prof.items()}})
        log('   %-28s %s%s' % (oname, fmt_prof(prof), ('  *** SEPARATES ' + ' '.join(seps)) if seps else ''))


# ---------------------------------------------------------------- natural subspaces (flag, swaps)
def secant_flag(cp, kmax, ntens=4):
    """{k: basis of U_k} for k = 1..kmax (stops at U_k = 0)."""
    out = {}
    for k in range(1, kmax + 1):
        rows = []
        for j in range(ntens):
            V = cp.rand_tensor(k, 'flag%d_%d' % (k, j))
            rows.append(cp.probe_matrix(tuple(V[u] for u in cp.perm)))
        U = nullspace(np.vstack(rows))
        out[k] = U
        if len(U) == 0:
            break
    return out


def swap_spaces(cp):
    """eigenspaces of the transpositions tau of equal partitions of lam_p: {'sw23+': basis, ...}.
    tau acts on the functionals by Phi_f -> tau_S o Phi_f o tau (tau_S = swap of the two equal Schur factors), which
    is the functional of the filling with the two fillings exchanged: Phi_f^tau = Phi_{f o tau}.  (specialU.py
    permuted the filling AND the tensor and the points, which gives back Phi_f: its Tau was the identity.)"""
    out = {}
    V = cp.tensor_p('probe')
    base = None
    for (i, j) in [(1, 2), (0, 1), (0, 2)]:
        if cp.lam_p[i] != cp.lam_p[j]:
            continue
        if base is None:
            base = cp.probe_matrix(V)
        perm = [0, 1, 2]; perm[i], perm[j] = perm[j], perm[i]
        cols = []
        for fl in cp.D.fillings:
            Q = cp.probe_cube([fl[0][u] for u in perm], V).ravel()
            sol = nullspace(np.hstack([base, Q[:, None]]))
            assert len(sol) == 1 and sol[0][-1] % p, 'swap image not in span'
            s = sol[0]; inv = pow(int((-s[-1]) % p), p - 2, p)
            cols.append((s[:-1] * inv) % p)
        Tau = np.array(cols, dtype=np.int64).T % p        # Tau[:, f] = coordinates of Phi_f o tau
        assert not ((Tau @ Tau - np.eye(cp.g, dtype=np.int64)) % p).any(), 'tau^2 != 1'
        for sign, nm in ((1, '+'), (p - 1, '-')):
            E = nullspace((Tau - sign * np.eye(cp.g, dtype=np.int64)) % p)
            out['sw%d%d%s' % (i + 1, j + 1, nm)] = E
    return out


def natural_orderings(cp, flag, swaps, rng):
    g = cp.g
    spaces = []
    for k, U in flag.items():
        spaces.append(('U%d' % k, U))
    for nm, E in swaps.items():
        spaces.append((nm, E))
        for k, U in flag.items():
            if 0 < len(U) < g:
                spaces.append(('U%d^%s' % (k, nm), intersect(U, E, g)))
    orderings, seen = [], []
    for nm, W in spaces:
        if not (0 < len(W) < g):
            continue
        key = rowspace_basis(W).tobytes()
        if key in seen:
            continue
        seen.append(key)
        orderings.append((nm, complete_basis(W, g, rng), 'prefix <= %d: generic subspaces of %s; = %d: %s; > %d: %s + generic'
                          % (len(W), nm, len(W), nm, len(W), nm)))
    # flag-adapted basis U_kmax < ... < U_1 < M^*
    chain = [(k, U) for k, U in sorted(flag.items(), reverse=True) if 0 < len(U) < g]
    if len(chain) >= 2:
        B = np.zeros((0, g), dtype=np.int64)
        for k, U in chain:
            # extend B to a basis of U by random vectors of U
            while len(B) < len(U):
                v = random_basis(U, 1, rng)
                if len(rowspace_basis(np.vstack([B, v]))) > len(B):
                    B = np.vstack([B, v])
        B = complete_basis(B, g, rng) if len(B) < g else B
        orderings.append(('flag', B, 'flag-adapted: prefixes ' + ', '.join('%d = U%d' % (len(U), k) for k, U in chain)))
    return orderings


# ---------------------------------------------------------------- rank-drop points on lines
def drop_minpoly(FA, FB, rho, rng):
    """nmod_poly whose roots contain the t with rank(FA + t FB) < rho (minimal polynomial of -B'^{-1} A')."""
    N, K = FA.shape
    for attempt in range(3):
        R = rng.integers(0, p, (rho, N)).astype(np.float64)
        S = rng.integers(0, p, (K, rho)).astype(np.float64)
        A2 = _mm(_mm(R, FA), S); B2 = _mm(_mm(R, FB), S)
        Bf = to_flint(B2)
        try:
            X = Bf.solve(to_flint(A2))
        except ZeroDivisionError:
            continue
        return (-X).minpoly()
    raise RuntimeError('singular projection')


def pencil_points(cp, AB, R, rng, tag, size):
    """tensor-independent drop points of a matrix pencil A(X) + t B(X) (AB(X) -> (A, B) for the tensor named X) for
    rank-r_lo tensors (r_lo = min R): Ta = P(r_lo) and Tb derive them (gcd of the minimal polynomials of projected
    pencils), Tc checks them (a true tensor-independent point lowers Tc too); every such point gets its rank profile
    over r_lo..r_hi+1 (ends + bisection; D_r is contained in D_{r_lo} when the generic rank is constant on the range).
    Points over F_{p^e} via ext_rank (skipped when e * size > EMAXSIZE)."""
    t0 = time.time()
    rlo, rhi = min(R), max(R)
    Ta, Tb, Tc = cp.P(rlo), 'D%db' % rlo, 'D%dc' % rlo
    cp.add_tensor(Tb, rlo); cp.add_tensor(Tc, rlo)
    FAB = {X: AB(X) for X in (Ta, Tb, Tc)}
    tg = int(rng.integers(1, p))
    rho = {X: rank(np.fmod(A + tg * B, p)) for X, (A, B) in FAB.items()}
    if len(set(rho.values())) > 1:
        log('   WARNING: rank-r tensors differ on the pencil: %s' % rho)
    polys = [drop_minpoly(FAB[X][0], FAB[X][1], rho[X], rng) for X in (Ta, Tb)]
    tpoly = time.time() - t0
    h = polys[0].gcd(polys[1])
    out = {'line': tag, 'rho': rho[Ta], 'deg': [polys[0].degree(), polys[1].degree()], 'gcd': h.degree(), 'factors': []}
    if h.degree() > 0:
        lead, facs = h.factor()
        for f, mult in facs:
            e = f.degree()
            coeffs = [int(c) for c in f.coeffs()]
            ent = {'e': e, 'mult': mult}
            if e * size > EMAXSIZE:
                ent['skipped'] = 'extension too large'
                out['factors'].append(ent); continue
            rk = {X: ext_rank(list(FAB[X]), coeffs) for X in (Ta, Tb, Tc)}
            ent['ranks'] = [rk[Ta], rk[Tb], rk[Tc]]
            ent['indep'] = rk[Tc] < rho[Tc]
            if ent['indep']:
                def fn(r):
                    if r == rlo:
                        return [[rk[Ta]]]
                    return [[ext_rank(list(AB(cp.P(r))), coeffs)]]
                prof = resolve_profile(fn, rlo, rhi + 1)
                ent['prof'] = {str(r): v[0][0] for r, v in prof.items()}
                ent['sep'] = separations(prof, R, cp.g, 'pt')
                if ent['sep']:
                    ent['r-1,r+2'] = [ext_rank(list(AB(cp.P(rr))), coeffs) if rr >= 1 else None for rr in (rlo - 1, rhi + 2)]
            if e == 1:
                ent['t'] = (-coeffs[0]) % p
                ent['li'] = tag
            out['factors'].append(ent)
    out['time'] = [round(tpoly, 1), round(time.time() - t0, 1)]
    return out


def line_points(cp, a, b, R, rng, tag):
    """drop points of one functional on the line a + t b of P(M^*); matrices sliced to min(n1, n23) + 8 rows and
    columns (enough for one functional).  out['points'] = rational tensor-independent points (vector, entry)."""
    m = min(cp.n1, cp.n23) + 8
    n1s, ks = min(cp.N1, m), min(cp.K, m)

    def AB(X):
        Fs = cp.F(X)[:, :n1s, :ks]
        return combo(Fs, a), combo(Fs, b)
    out = pencil_points(cp, AB, R, rng, tag, max(n1s, ks))
    out['points'] = [((a + ent['t'] * b) % p, ent) for ent in out['factors'] if ent.get('indep') and 't' in ent]
    return out


def run_glines(cp, R, rng, rec, cap=4e7):
    """drop loci of the stacked flattenings in the Grassmannian: for k = 2..g-1 and H, V a random pencil of k-frames
    A + t B (k x g) gives the matrix pencil H_A + t H_B (blocks side by side) resp. V_A + t V_B (stacked); its
    tensor-independent drop points t are special k-dimensional U (basis A + t B)."""
    g = cp.g
    for k in range(2, g):
        for typ in ('H', 'V'):
            if k * cp.N1 * cp.K > cap:
                rec['cases'].append({'method': 'gline', 'k': k, 'typ': typ, 'skipped': 'size %d x %d x %d' % (k, cp.N1, cp.K)})
                log('   gline %s%d: skipped (size)' % (typ, k))
                continue
            A0, B0 = rng.integers(0, p, (k, g)), rng.integers(0, p, (k, g))

            def AB(X, A0=A0, B0=B0, typ=typ):
                Fs = cp.F(X)
                PA = [combo(Fs, c) for c in A0]
                PB = [combo(Fs, c) for c in B0]
                return (np.hstack(PA), np.hstack(PB)) if typ == 'H' else (np.vstack(PA), np.vstack(PB))
            size = max(cp.N1, k * cp.K) if typ == 'H' else max(k * cp.N1, cp.K)
            out = pencil_points(cp, AB, R, rng, 'gline-%s%d' % (typ, k), size)
            out['method'] = 'gline'; out['k'] = k; out['typ'] = typ
            fs = ' '.join('e%d%s:%s%s%s' % (f['e'], ('^%d' % f['mult']) if f['mult'] > 1 else '', f.get('ranks', f.get('skipped')),
                                            (' prof%s' % f['prof']) if 'prof' in f else ('' if 'skipped' in f else '(dep)'),
                                            (' *SEP* %s r-1,r+2:%s' % (f['sep'], f['r-1,r+2'])) if f.get('sep') else '')
                          for f in out['factors'])
            log('   gline %s%d rho %d  minpoly deg %s  gcd deg %d  %s  (%.1fs)' % (typ, k, out['rho'], out['deg'], out['gcd'], fs, out['time'][1]))
            rec['cases'].append(out)
            for f in out['factors']:
                if f.get('sep'):
                    rec['hits'].append({'method': 'gline', 'U': 'Grassmannian pencil %s%d drop point e=%d' % (typ, k, f['e']),
                                        'ranks': f['ranks'], 'prof': f['prof'], 'sep': f['sep'], 'r-1,r+2': f['r-1,r+2'], 't': f.get('t')})


def run_lines(cp, R, nlines, rng, rec, through=None, inside=None, label='line', extend=None):
    """random lines (or lines through the point `through`, or inside the row space of `inside`); if `extend` and
    some line has rational tensor-independent drop points, continue up to `extend` lines (to see whether the points
    of one kind lie on a linear subspace).  Returns the rational tensor-independent points [(vector, entry)]."""
    g = cp.g
    allpts = []
    li = 0
    while li < nlines or (extend and allpts and li < extend):
        if inside is not None:
            a, b = random_basis(inside, 1, rng)[0], random_basis(inside, 1, rng)[0]
        else:
            a = through.copy() if through is not None else rng.integers(0, p, g)
            b = rng.integers(0, p, g)
        res = line_points(cp, a, b, R, rng, '%s%d' % (label, li))
        allpts += res.pop('points')
        fs = ' '.join('e%d%s:%s%s%s' % (f['e'], ('^%d' % f['mult']) if f['mult'] > 1 else '', f.get('ranks', f.get('skipped')),
                                        (' prof%s' % f['prof']) if 'prof' in f else ('' if 'skipped' in f else '(dep)'),
                                        (' *SEP* %s r-1,r+2:%s' % (f['sep'], f['r-1,r+2'])) if f.get('sep') else '')
                      for f in res['factors'])
        log('   %s rho %d  minpoly deg %s  gcd deg %d  %s  (%.1fs)' % (res['line'], res['rho'], res['deg'], res['gcd'], fs, res['time'][1]))
        res['method'] = label
        rec['cases'].append(res)
        for f in res['factors']:
            if f.get('sep'):
                rec['hits'].append({'method': label, 'U': '%s drop point e=%d' % (res['line'], f['e']), 'ranks': f['ranks'],
                                    'prof': f['prof'], 'sep': f['sep'], 'r-1,r+2': f['r-1,r+2'], 't': f.get('t')})
        li += 1
    return allpts


def find_hyperplanes(by_line, amb, cap=4096):
    """linear drop components seen by random lines of an ambient space of dim `amb`: hyperplanes H (dim amb - 1)
    that contain one point of every line.  by_line: list (one entry per line) of lists of point vectors.
    Candidates: one point from each of the first amb - 1 lines (at most `cap` choices), verified on all lines."""
    lines = [l for l in by_line if l]
    if amb < 2 or len(lines) < amb:          # need amb - 1 points to define H and >= 1 more line to verify
        return []
    found = []
    choices = itertools.islice(itertools.product(*[range(len(l)) for l in lines[:amb - 1]]), cap)
    for ch in choices:
        B = rowspace_basis(np.array([lines[i][c] for i, c in enumerate(ch)]))
        if len(B) != amb - 1 or any(np.array_equal(B, H) for H, _ in found):
            continue
        members = []
        for l in lines:
            inl = [v for v in l if len(rowspace_basis(np.vstack([B, v]))) == len(B)]
            if not inl:
                break
            members += inl
        else:
            found.append((B, members))
    return found


def span_tests(cp, pts, R, rec, rng, label, amb_basis=None):
    """k >= 2 from rational tensor-independent drop points, per rank signature (points of one drop component have
    one signature), in an ambient space A (M^* or a linear component W, basis amb_basis):
      * linear drop components: hyperplanes of A containing a point of every line (find_hyperplanes): U = H, its
        generic subspaces and H + generic (ordering [random basis of H, generic completion]); returned, for lines
        inside H;
      * the remaining points: U = span of the first k drop points ([p_1, p_2, ..., generic completion]), secant
        spaces of a non-linear component.
    H and V prefixes over the rank range."""
    g = cp.g
    amb = g if amb_basis is None else len(amb_basis)
    groups = collections.OrderedDict()
    for v, e in pts:
        key = (tuple(e['ranks']), tuple(sorted(e['prof'].items())))
        groups.setdefault(key, collections.OrderedDict()).setdefault(e['li'], []).append(v)
    found = []
    for sig, by_line in groups.items():
        nm = 'sig%s' % list(sig[0])
        allv = [v for l in by_line.values() for v in l]
        hyps = find_hyperplanes(list(by_line.values()), amb)
        inH = []
        for H, members in hyps:
            found.append((nm, H))
            inH += [m.tobytes() for m in members]
            test_orderings(cp, [('%s-span(%d) %s' % (label, len(H), nm), complete_basis(H, g, rng),
                                 'linear drop component: hyperplane through %d drop points (dim %d); prefixes > %d = + generic'
                                 % (len(members), len(H), len(H)))], R, rec, method=label + '-span')
        rest = [v for v in allv if v.tobytes() not in inH]
        if not hyps:
            rec['cases'].append({'method': label + '-span', 'group': nm, 'npts': len(allv), 'nlines': len(by_line),
                                 'note': 'no linear component (no hyperplane of the ambient dim %d through a point of every line)' % amb})
            log('   %s %s: %d points on %d lines, no linear component' % (label, nm, len(allv), len(by_line)))
        # spans of drop points (secant spaces), independent points in the order found
        B = np.zeros((0, g), dtype=np.int64)
        for v in rest:
            if len(B) < amb - 1 and len(rowspace_basis(np.vstack([B, v]))) > len(B):
                B = np.vstack([B, v])
        if len(B) >= 2:
            test_orderings(cp, [('%s-pts(%d) %s' % (label, len(B), nm), complete_basis_ordered(B, g, rng),
                                 'prefix k <= %d: span of k drop points' % len(B))], R, rec, method=label + '-pts')
    return found


def complete_basis_ordered(B, g, rng):
    """[rows of B in order; random vectors] (g x g)."""
    return np.vstack([B, rng.integers(0, p, (g - len(B), g))]) if len(B) < g else B


def generic_baseline(cp, R, rec, rng):
    """generic-U profile; returns the runs of R on which the generic H_1 rank is constant on [r, r+1] for every r of
    the run (drop loci D_r are then contained in D_(min of the run): lines are derived at the run's lowest rank)."""
    C = rng.integers(0, p, (cp.g, cp.g))
    prof = ordering_profile(cp, C, R)
    rec['generic'] = {str(r): v for r, v in prof.items()}
    log('   generic U: %s' % fmt_prof(prof))
    runs, cur = [], []
    for r in R:
        if cur and value_at(prof, r)[0][0] != value_at(prof, cur[0])[0][0]:
            runs.append(cur); cur = []
        cur.append(r)
    runs.append(cur)
    if len(runs) > 1:
        log('   generic H1 not constant on the range: line runs %s' % runs)
    return runs


# ---------------------------------------------------------------- codim-2 drop points on a plane (resultants)
PLANEMAX = int(os.environ.get('PLANEMAX', '160'))     # largest rho for the plane method (cost ~ rho^5)


def interpolate(xs, ys):
    """fmpz_mod_poly through (xs, ys) (distinct xs) by a subproduct tree (python-flint)."""
    ctx = flint.fmpz_mod_poly_ctx(p)
    tree = [[ctx([(-x) % p, 1]) for x in xs]]
    while len(tree[-1]) > 1:
        lv = tree[-1]
        tree.append([lv[i] * lv[i + 1] if i + 1 < len(lv) else lv[i] for i in range(0, len(lv), 2)])
    M = tree[-1][0]
    w = M.derivative().multipoint_evaluate([flint.fmpz_mod(x, flint.fmpz_mod_ctx(p)) for x in xs])
    level = [ctx([int(y) * pow(int(wi), p - 2, p) % p]) for y, wi in zip(ys, w)]
    for k in range(len(tree) - 1):
        T = tree[k]
        level = [level[i] * T[i + 1] + level[i + 1] * T[i] if i + 1 < len(level) else level[i] for i in range(0, len(level), 2)]
    return level[0]


def to_nmod_poly(P):
    return flint.nmod_poly([int(c) for c in P.coeffs()], p)


def plane_resultant(FO, Fb, Fc, rho, rng, log_every=0):
    """For one tensor: r(v) = lc_u(h)^(2(rho-e)) Res_u(Q_1, Q_2) as an nmod_poly in v, where P_i(u, v) =
    det(R_i F(O + u (b + v c)) S_i) (two random rho x rho projections), h = the common (drop-curve) factor of degree e
    on a generic line, Q_i = P_i / h.  Its roots v are the lines through O containing a point where the two
    projections have a further common zero: the isolated drop points of this tensor (codim 2) and projection-
    dependent intersection points.  deg r <= rho^2 - e^2 (isobaric weight), so rho^2 - e^2 + 1 exact samples
    determine it (lines with det(B + v C) = 0 are skipped).  Returns (r, e, nsamples)."""
    N, K = FO.shape
    prj = []
    for i in range(2):
        Rm = rng.integers(0, p, (rho, N)).astype(np.float64)
        Sm = rng.integers(0, p, (K, rho)).astype(np.float64)
        prj.append([to_flint(_mm(_mm(Rm, X), Sm)) for X in (FO, Fb, Fc)])

    def sample(v):
        Ps = []
        for A, B, C in prj:
            Bv = B + C * v
            dB = Bv.det()
            if int(dB) == 0:
                return None
            Ps.append((-(Bv.solve(A))).charpoly() * int(dB))
        return Ps
    # generic curve degree e: minimum gcd degree over a few random lines
    e = None
    for _ in range(3):
        Ps = sample(int(rng.integers(1, p)))
        if Ps is not None:
            dg = Ps[0].gcd(Ps[1]).degree()
            e = dg if e is None else min(e, dg)
    need = rho * rho - e * e + 1 + 4
    xs, ys, used = [], [], set()
    while len(xs) < need:
        v = int(rng.integers(1, p))
        if v in used:
            continue
        used.add(v)
        Ps = sample(v)
        if Ps is None:
            continue
        G = Ps[0].gcd(Ps[1])
        if G.degree() < e:
            raise RuntimeError('curve degree not generic (%d < %d)' % (G.degree(), e))
        if G.degree() > e:
            val = 0
        else:
            val = int((Ps[0] // G).resultant(Ps[1] // G))
        xs.append(v); ys.append(val)
        if log_every and len(xs) % log_every == 0:
            log('      plane samples %d / %d' % (len(xs), need))
    r = to_nmod_poly(interpolate(xs[:-4], ys[:-4]))
    # check on the 4 extra samples
    for x, y in zip(xs[-4:], ys[-4:]):
        if int(r(x)) != y % p:
            raise RuntimeError('plane resultant: interpolation check failed (degree bound?)')
    return r, e, len(xs)


def run_plane(cp, R, rng, rec, label='plane'):
    """isolated (codim-2) tensor-independent drop points of rank-r_lo tensors on a random plane of P(M^*)
    (= all of P(M^*) for g = 3): gcd over two tensors of the plane resultants; every rational root v gives the line
    through O and the point, analysed by line_points (which re-derives the point and tests it)."""
    t0 = time.time()
    g = cp.g
    rlo = min(R)
    Ta, Tb = cp.P(rlo), 'D%db' % rlo
    cp.add_tensor(Tb, rlo)
    m = min(cp.n1, cp.n23) + 8
    n1s, ks = min(cp.N1, m), min(cp.K, m)
    O, b, c = (rng.integers(0, p, g) for _ in range(3))
    res = {'method': label, 'plane': [O, b, c]}
    rs = []
    for X in (Ta, Tb):
        Fs = cp.F(X)[:, :n1s, :ks]
        FO, Fb, Fc = combo(Fs, O), combo(Fs, b), combo(Fs, c)
        rho = rank(np.fmod(FO + 3 * Fb + 5 * Fc, p))
        res['rho'] = rho
        if rho > PLANEMAX:
            res['skipped'] = 'rho %d > PLANEMAX %d' % (rho, PLANEMAX)
            log('   %s: skipped (rho %d > %d)' % (label, rho, PLANEMAX))
            rec['cases'].append(res)
            return
        r, e, ns = plane_resultant(FO, Fb, Fc, rho, rng, log_every=5000 if rho > 100 else 0)
        rs.append(r)
        res.setdefault('curve_deg', []).append(e)
        res.setdefault('res_deg', []).append(r.degree())
    G = rs[0].gcd(rs[1])
    res['gcd_deg'] = G.degree()
    res['lines'] = []
    log('   %s rho %d: drop-curve degrees %s, resultant degrees %s, common %d  (%.0fs)'
        % (label, rho, res['curve_deg'], res['res_deg'], G.degree(), time.time() - t0))
    if G.degree() > 0:
        lead, facs = G.factor()
        res['factor_degs'] = [f.degree() for f, _ in facs]
        for f, mult in facs:
            if f.degree() != 1:
                continue
            v = (-int(f.coeffs()[0])) % p
            Q = (b + v * c) % p
            # roots of the factor lc_u(h)(v) (h = drop curve): Q itself on the curve -- not an isolated point
            Fs = cp.F(Ta)[:, :n1s, :ks]
            if rank(combo(Fs, Q)) < rho:
                res['lines'].append({'v': v, 'note': 'far point on the drop curve (leading-coefficient root)'})
                continue
            # the line through O and Q contains the common point(s); second point generic on it
            out = line_points(cp, O, (Q + int(rng.integers(1, p)) * O) % p, R, rng, '%s-line' % label)
            out.pop('points')
            fs = ' '.join('e%d:%s%s%s' % (ff['e'], ff.get('ranks', ff.get('skipped')),
                                          (' prof%s' % ff['prof']) if 'prof' in ff else ('' if 'skipped' in ff else '(dep)'),
                                          (' *SEP* %s' % ff['sep']) if ff.get('sep') else '') for ff in out['factors'])
            log('   %s v=%d: line rho %d gcd deg %d  %s' % (label, v, out['rho'], out['gcd'], fs))
            out['v'] = v
            res['lines'].append(out)
            for ff in out['factors']:
                if ff.get('sep'):
                    rec['hits'].append({'method': label, 'U': '%s point (line v=%d) e=%d' % (label, v, ff['e']), 'ranks': ff['ranks'],
                                        'prof': ff['prof'], 'sep': ff['sep'], 'r-1,r+2': ff['r-1,r+2'], 't': ff.get('t')})
    res['time'] = round(time.time() - t0, 1)
    rec['cases'].append(res)


# ---------------------------------------------------------------- driver
def run_component(n, d, lam, R, methods, seed, dirs=None, out=None):
    g = kronecker(*lam)
    rgen = generic_rank(n)
    R = sorted(R)
    recs = []
    for t in (dirs if dirs is not None else distinct_dirs(lam)):
        reset_peak_rss()
        T0, C0 = time.time(), time.process_time()
        perm_lam = tuple(lam[u] for u in [t] + [u for u in range(3) if u != t])
        rec = {'n': n, 'd': d, 'lam': lam, 'g': g, 't': t, 'r': R, 'methods': methods, 'seed': seed,
               'p': p, 'cases': [], 'hits': []}
        if word_minor_size(perm_lam, n, max(R) + 1) > rankscan.WCAP:
            log('lam=%s dir %d: rank %d infeasible (word minors)' % (lam, t + 1, max(R) + 1))
            rec['status'] = 'infeasible'
        else:
            rprobe = max([x for x in range(1, rgen + 1) if word_minor_size(perm_lam, n, x) <= rankscan.WCAP])
            try:
                cp = Comp(n, lam, t, seed, rprobe)
            except (AssertionError, Infeasible, MemoryError) as e:
                log('lam=%s dir %d: setup failed: %s' % (lam, t + 1, e))
                cp = None
                rec['status'] = 'setup failed: %s' % str(e)[:200]
            if cp is not None:
                rec['status'] = 'ok'
                try:
                    run_direction(cp, R, methods, seed, rec)
                except (Infeasible, MemoryError) as e:
                    rec['status'] = 'failed: %s' % str(e)[:200]
                    log('   FAILED: %s' % e)
                rec['ftime'] = round(getattr(cp, 'ftime', 0.0), 1)
                del cp
        rec['wall'] = round(time.time() - T0, 1)
        rec['cpu'] = round(time.process_time() - C0, 1)
        rec['rss_peak_mb'] = round(peak_rss_mb(), 1)
        rec['ts'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
        log('   done dir %d: %s, %d cases, %d hits, wall %.1fs (F %.1fs), peak %.0f MB' % (t + 1, rec['status'], len(rec['cases']),
                                                                                     len(rec['hits']), rec['wall'], rec.get('ftime', 0), rec['rss_peak_mb']))
        if out:
            with open(out, 'a') as fh:
                fh.write(json.dumps(rec, default=lambda o: o.tolist() if hasattr(o, 'tolist') else int(o)) + '\n')
        recs.append(rec)
    return recs


def run_direction(cp, R, methods, seed, rec):
    g, n, lam, t = cp.g, cp.n, cp.lam, cp.t
    rng = np.random.default_rng([seed, n, t, 99] + [x for l in lam for x in l])
    # cache size from memory: at most ~1.2 GB of filling matrices
    global CACHE
    per = g * cp.N1 * cp.K * (8 if g * cp.N1 * cp.K <= (1 << 24) else 4)
    CACHE = max(3, min(int(os.environ.get('CACHE', '6')), int(1.2e9 // per)))
    rec.update({'n1': cp.n1, 'n23': cp.n23, 'N1': cp.N1, 'K': cp.K})
    log('lam=%s g=%d dir %d: n1=%d n23=%d N1=%d K=%d  ranks %s' % (lam, g, t + 1, cp.n1, cp.n23, cp.N1, cp.K, R))
    runs = generic_baseline(cp, R, rec, rng)
    flag = swaps = None
    if 'flag' in methods or 'pflag' in methods:
        t1 = time.time()
        flag = secant_flag(cp, sum(cp.lam_p[0]) - 1)
        swaps = swap_spaces(cp)
        rec['flag'] = {k: len(U) for k, U in flag.items()}
        rec['swaps'] = {k: len(E) for k, E in swaps.items()}
        log('   U_k dims %s  swaps %s  (%.1fs)' % (rec['flag'], rec['swaps'], time.time() - t1))
    if 'flag' in methods:
        ords = natural_orderings(cp, flag, swaps, rng)
        if ords:
            test_orderings(cp, ords, R, rec)
        else:
            rec['cases'].append({'method': 'flag', 'U': None, 'note': 'no natural U with 0 < dim < g'})
            log('   no natural U with 0 < dim < g')
    nlines = int(os.environ.get('NLINES', '2'))
    for Rr in runs:
        if 'line' in methods:
            pts = run_lines(cp, Rr, nlines, rng, rec, extend=g + 2)
            todo = [(nm, W, 1) for nm, W in span_tests(cp, pts, Rr, rec, rng, 'line')]
            while todo:                 # lines inside the linear drop components found (depth <= 2)
                nm, W, depth = todo.pop(0)
                if len(W) < 2:
                    continue
                lab = 'in[%s]' % nm
                pts2 = run_lines(cp, Rr, 1 if len(W) == 2 else nlines, rng, rec, inside=W, label=lab,
                                 extend=None if len(W) == 2 else len(W) + 2)
                if depth < 2 and len(W) > 2:
                    todo += [(lab + nm2, W2, depth + 1) for nm2, W2 in span_tests(cp, pts2, Rr, rec, rng, lab, amb_basis=W)]
        if 'plane' in methods and g >= 3:
            run_plane(cp, Rr, rng, rec)
        if 'gline' in methods and g >= 3:
            run_glines(cp, Rr, rng, rec)
        if 'pflag' in methods:
            for nm, W in [('U%d' % k, U) for k, U in flag.items()] + list(swaps.items()):
                if not (0 < len(W) < g):
                    continue
                pt = random_basis(W, 1, rng)[0]
                run_lines(cp, Rr, 1, rng, rec, through=pt, label='thru-%s' % nm)
                if len(W) >= 2:
                    run_lines(cp, Rr, 1, rng, rec, inside=W, label='in-%s' % nm)


def main():
    n, d = int(sys.argv[1]), int(sys.argv[2])
    rs = sys.argv[4]
    rlist = list(range(int(rs.split('-')[0]), int(rs.split('-')[1]) + 1)) if '-' in rs else [int(x) for x in rs.split(',')]
    methods = sys.argv[5:] or ['line', 'flag']
    seed = int(os.environ.get('SEED', '11'))
    dirs = [int(x) - 1 for x in os.environ['DIRS'].split(',')] if os.environ.get('DIRS') else None
    os.makedirs('special/res', exist_ok=True)
    out = os.environ.get('OUT', 'special/res/n%d_d%d.jsonl' % (n, d))
    if sys.argv[3] != 'all':
        lam = tuple(tuple(x) for x in eval(sys.argv[3]))
        if dirs is None:
            # resume: skip directions with a record (same ranks and methods) in any special/res/n<n>_d<d>*.jsonl
            done = set()
            for f in glob.glob(os.path.join(os.environ.get('DONEGLOB', 'special/res'), 'n%d_d%d*.jsonl' % (n, d))):
                for l in open(f):
                    try:
                        rr = json.loads(l)
                    except ValueError:
                        continue
                    if rr['methods'] == methods and rr['r'] == rlist and tuple(tuple(x) for x in rr['lam']) == lam:
                        done.add(rr['t'])
            dirs = [t for t in distinct_dirs(lam) if t not in done]
        run_component(n, d, lam, rlist, methods, seed, dirs, out)
        return
    # all components with g >= 2 (or the list in LIST), cheapest first; WORKER/NWORKERS shard; resume from OUT
    W, NW = int(os.environ.get('WORKER', '0')), int(os.environ.get('NWORKERS', '1'))
    gmin = int(os.environ.get('GMIN', '2'))
    comps = [(lam, g) for li, lam, g in rankscan.components(n, d) if g >= gmin]
    if os.environ.get('LIST'):
        want = [tuple(tuple(x) for x in eval(l)) for l in open(os.environ['LIST']) if l.strip()]
        comps = [(lam, g) for lam, g in comps if lam in want]
    comps.sort(key=lambda c: rankscan.cost_proxy(n, c[0], c[1]))
    done = set()
    if os.path.exists(out):
        for l in open(out):
            try:
                rr = json.loads(l)
                if rr['methods'] == methods and rr['r'] == rlist:
                    done.add((tuple(tuple(x) for x in rr['lam']), rr['t']))
            except Exception:
                pass
    log('# specialscan n=%d d=%d r=%s methods=%s seed=%d worker %d/%d: %d components with g >= %d' % (n, d, rlist, methods, seed, W, NW, len(comps), gmin))
    T0 = time.time()
    for i, (lam, g) in enumerate(comps):
        if i % NW != W:
            continue
        ds = [t for t in (dirs if dirs is not None else distinct_dirs(lam)) if (lam, t) not in done]
        if ds:
            run_component(n, d, lam, rlist, methods, seed, ds, out)
    log('# worker %d done, %.0fs' % (W, time.time() - T0))


if __name__ == '__main__':
    main()
