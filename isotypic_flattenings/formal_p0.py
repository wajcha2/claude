"""Formal-variable test of the d=8 separator lam = ((6,2),(3,2,2,1),(3,2,2,1)), direction 1, with the 1-dim U = P0
(filling 0 of hit_d8_special.py / line_point_M2.py).  Goal: prove rank F_{P0}(T) <= 224 for every T in sigma_6.

Reduction (exact): T = sum_{i<=6} a_i b_i c_i = (alpha (x) 1 (x) 1) T',  T' = sum e_i (x) b_i (x) c_i in C^6 (x) C^4 (x) C^4,
F_T = F_{T'} o (S^{62} alpha)^T, so rank F_T <= rank F_{T'} and a cokernel vector of F_{T'} kills im F_T for all a_i.
The image of F_{T'} depends only on the points [b_i], [c_i] (GL6 acts on the source only) and is GL4 x GL4-equivariant:
b_1..b_5 = c_1..c_5 = projective frame (e_1..e_4, e_1+..+e_4), b6, c6 formal (homogeneous coordinates, 6 parameters).
Target S^{3221}B (x) S^{3221}C (225) in the dual basis of 15 x 15 integer evaluation points (Gram rank 15 checked).
Wanted: psi(b6, c6), bihomogeneous of bidegree (db, dc), 225 polynomial coordinates, with psi^T F_{T'(b6,c6)} == 0.

stages (one prime per process, prime = argv):
  setup                     integer target points (Gram rank 15 on both sides), coordinates J; saved in live/formal_p0/
  search  q                 A-freed rank / cokernel dim k; minimal degree in b6 (c6 fixed), in c6 (b6 fixed), then the
                            minimal joint bidegree (db, dc) of a section, all mod q
  solve   q db dc           sections of bidegree (db, dc) mod q, normalised; full psi (225 x N coefficients) saved
  recon                     CRT + rational reconstruction of psi from all saved primes
  vsetup                    integer source points alpha in {-3..3}^6, beta in {-1,0,1}^6 (7 resp. 3 values: degrees <= 6
                            resp. <= 2 in each variable, so smaller boxes cannot span); rigorous spanning check of every
                            e6-weight part S_j (j = 0..3) of S^{62}C^6 by Gram ranks (pairing D1^4 D2^2)
  verify  lo hi             source rows [lo, hi): F(b6, c6) interpolated exactly mod 4 primes (517 monomials of bidegree
                            (j,j), j <= 3), CRT to the exact integers (a priori bound), then psi^T F == 0 checked mod
                            these and extra primes until the product of the primes exceeds 2 x (bound on the product)
  fullrank                  exact rank 225 of F_{P0} at an explicit integer rank-7 tensor
usage: python3 formal_p0.py <stage> [args]"""
import sys, os, time, itertools, numpy as np
os.environ.setdefault('MEMLIMIT_GB', '10')
STAGE = sys.argv[1] if len(sys.argv) > 1 else 'search'
p = int(sys.argv[2]) if len(sys.argv) > 2 and STAGE in ('search', 'solve') else 524287
import hwv, isoflat, hwv_fast
def set_prime(q):
    global p
    p = hwv.p = isoflat.p = hwv_fast.p = int(q)
set_prime(p)
import flatlib

OUT = 'live/formal_p0'; os.makedirs(OUT, exist_ok=True)
F0 = [[[0, 6], [1, 7], [2], [3], [4], [5]], [[3, 5, 7, 4], [6, 1, 2], [0]], [[2, 6, 7, 0], [1, 3, 5], [4]]]
FRAME = np.vstack([np.eye(4, dtype=np.int64), np.ones((1, 4), dtype=np.int64)])
E6 = np.eye(6, dtype=np.int64)
MU_EXP = (1, 0, 1, 1)        # S^{3221}: <v*, X v> = D1 D3 D4 (leading principal minors)
T0 = time.time()
def log(*a):
    print('[%6.0fs]' % (time.time() - T0), *a); sys.stdout.flush()

# ---------------- modular linear algebra (explicit prime) ----------------
def mm(A, B):
    """A @ B mod p, exact in float64 (inner dimension <= 2^15, entries < p < 2^19.1)."""
    A = np.asarray(A, dtype=np.float64); B = np.asarray(B, dtype=np.float64)
    L = A.shape[-1]; out = None; step = 1 << 14
    for s in range(0, L, step):
        part = np.fmod(A[..., s:s + step] @ B[s:s + step], p)
        out = part if out is None else np.fmod(out + part, p)
    return out.astype(np.int64)

def rref(M):
    A = np.array(M, dtype=np.int64) % p; m, n = A.shape; piv = []; r = 0
    for c in range(n):
        if r == m: break
        nz = np.nonzero(A[r:, c])[0]
        if nz.size == 0: continue
        i = r + nz[0]
        if i != r: A[[r, i]] = A[[i, r]]
        A[r] = (A[r] * pow(int(A[r, c]), p - 2, p)) % p
        rows = np.nonzero(A[:, c])[0]; rows = rows[rows != r]
        if rows.size: A[rows] = (A[rows] - np.outer(A[rows, c], A[r]) % p) % p
        piv.append(c); r += 1
    return A[:r], piv

def nullspace(M):
    """rows x with M x = 0 (mod p)."""
    M = np.asarray(M); n = M.shape[1]
    if M.shape[0] > n + 64:       # random row compression (keeps the null space with high probability)
        R = np.random.default_rng(0).integers(0, p, (n + 64, M.shape[0]))
        M = mm(R, M % p)
    R_, piv = rref(M); free = [c for c in range(n) if c not in set(piv)]
    out = np.zeros((len(free), n), dtype=np.int64)
    for k, f in enumerate(free):
        out[k, f] = 1
        for i, c in enumerate(piv): out[k, c] = (-R_[i, f]) % p
    return out

def rank(M):
    return len(rref(M)[1])

def inv(M):
    n = M.shape[0]; R_, piv = rref(np.hstack([np.asarray(M) % p, np.eye(n, dtype=np.int64)]))
    assert piv[:n] == list(range(n)), 'singular'
    return R_[:n, n:]

# ---------------- data ----------------
def det_obj(X):
    """exact determinants of a batch X (..., k, k) of Python integers (permutation expansion, k <= 4)."""
    k = X.shape[-1]; tot = 0
    for perm in itertools.permutations(range(k)):
        sgn = (-1) ** sum(1 for i in range(k) for j in range(i + 1, k) if perm[i] > perm[j])
        term = sgn
        for i in range(k): term = term * X[..., i, perm[i]]
        tot = tot + term
    return tot

def lead_minor_prod(X, expo):
    """prod_k det(X[..., :k, :k])^expo[k-1] (exact)."""
    out = 1
    for k, e in enumerate(expo, 1):
        if e: out = out * det_obj(X[..., :k, :k]) ** e
    return out

def gram_rank(G, expo, rng, ndual=None):
    """rank mod p of <G_i v*, H_j v> = prod_k D_k(G_i^T H_j)^expo  (independence of the evaluation functionals)."""
    n = G.shape[1]; H = rng.integers(0, p, ((ndual or len(G) + 5), n, n))
    A = np.zeros((len(G), len(H)), dtype=np.int64)
    for i in range(len(G)):
        X = np.einsum('ab,jbc->jac', G[i].T.astype(object), H.astype(object)) % p
        A[i] = np.array([int(v) % p for v in lead_minor_prod(X, expo)], dtype=np.int64)
    return rank(A)

def setup():
    rng = np.random.default_rng(2026)
    pts = {}
    for side in ('B', 'C'):
        chosen = []
        while len(chosen) < 15:
            cand = rng.integers(-1, 2, (4, 4))
            if round(abs(np.linalg.det(cand))) == 0: continue
            if gram_rank(np.array(chosen + [cand]) % p, MU_EXP, rng) == len(chosen) + 1:
                chosen.append(cand)
        pts[side] = np.array(chosen, dtype=np.int64)
        log('target points %s: 15 integer 4x4 matrices with entries in {-1,0,1}, Gram rank %d' % (side, gram_rank(pts[side] % p, MU_EXP, rng)))
    np.save(OUT + '/setup.npy', {'Gb': pts['B'], 'Gc': pts['C']}, allow_pickle=True)

def load_setup():
    D = np.load(OUT + '/setup.npy', allow_pickle=True).item()
    Gb, Gc = D['Gb'], D['Gc']
    return np.repeat(Gb, 15, axis=0) % p, np.tile(Gc, (15, 1, 1)) % p, D

def coker(b6, c6, G6, Zb, Zc):
    b = np.vstack([FRAME, b6]) % p; c = np.vstack([FRAME, c6]) % p
    F = flatlib.flat(F0, (E6, b, c), (G6, Zb, Zc)) % p
    return nullspace(F)            # rows psi with F psi = 0

def monomials(d, nv=4):
    return [e for e in itertools.product(range(d + 1), repeat=nv) if sum(e) == d]

def mono_matrix(pts, monos):
    """pts: (S, nv) mod p; monos: list of exponent tuples -> (S, N) values mod p."""
    S, nv = pts.shape; dmax = max(max(m) for m in monos) if monos else 0
    pw = np.ones((dmax + 1, S, nv), dtype=np.int64)
    for e in range(1, dmax + 1): pw[e] = (pw[e - 1] * pts) % p
    V = np.ones((S, len(monos)), dtype=np.int64)
    for j, m in enumerate(monos):
        for v, e in enumerate(m):
            if e: V[:, j] = (V[:, j] * pw[e][:, v]) % p
    return V

def sections(V, Nn, J):
    """unknown lambda_r (r < k) with coefficient vectors X_r (N each); constraint: for every coordinate q not in J the
    values sum_r lambda_r(t) Nn[t, r, q] (t = sample points) are those of a polynomial in the span of V's columns."""
    S, N = V.shape; k = Nn.shape[1]
    Q = nullspace(V.T)                               # (S - rank V) x S, Q V = 0
    if len(Q) == 0: return None
    notJ = [q for q in range(Nn.shape[2]) if q not in set(J)]
    blocks = []
    for r in range(k):
        Y = Nn[:, r, :][:, notJ]                     # S x (225 - k)
        QY = (Q[:, :, None] * Y[None, :, :]) % p     # (S-N) x S x (225-k)
        QY = QY.transpose(2, 0, 1).reshape(-1, S)
        blocks.append(mm(QY, V))
    return nullspace(np.hstack(blocks))              # rows: (X_0 | X_1 | ... | X_{k-1})

def stable_sections(sm, monos, k, start=None, step=None):
    """too few sample points only ADD spurious solutions; grow the sample until the dimension is the same twice."""
    N = len(monos); S = start or (N + max(20, N // 3)); step = step or max(20, N // 4); last = None
    while True:
        pts, Nn = sm.grow(S)
        X = sections(mono_matrix(pts, monos), Nn, sm.J)
        d = 0 if X is None else len(X)
        if last is not None and d == last: return X, S
        last = d; S += step

class Sampler:
    """random sample points with normalised cokernel bases n_t (n_t[:, J] = identity)."""
    def __init__(self, rng, G6, Zb, Zc, J=None, fix_b=None, fix_c=None):
        self.rng, self.G6, self.Zb, self.Zc, self.J = rng, G6, Zb, Zc, J
        self.fix_b, self.fix_c = fix_b, fix_c; self.pts, self.Nn = [], []
    def grow(self, S):
        while len(self.pts) < S:
            b6 = self.fix_b if self.fix_b is not None else self.rng.integers(0, p, 4)
            c6 = self.fix_c if self.fix_c is not None else self.rng.integers(0, p, 4)
            K = coker(b6, c6, self.G6, self.Zb, self.Zc)
            if self.J is None:
                self.J = sorted(int(x) for x in self.rng.choice(K.shape[1], len(K), replace=False))
            try: Ninv = inv(K[:, self.J])
            except AssertionError: continue
            self.pts.append(np.concatenate([b6, c6]) % p); self.Nn.append(mm(Ninv, K))
        return np.array(self.pts[:S]), np.array(self.Nn[:S])

def search():
    Zb, Zc, _ = load_setup()
    rng = np.random.default_rng(7)
    G6 = rng.integers(0, p, (245, 6, 6))
    k = len(coker(rng.integers(0, p, 4), rng.integers(0, p, 4), G6, Zb, Zc))
    log('prime %d: A-freed P0 flattening with frames, generic (b6, c6): cokernel dim k = %d (rank %d)' % (p, k, 225 - k))
    res = {}
    for name, fixed in (('b6 (c6 fixed)', 'c'), ('c6 (b6 fixed)', 'b')):
        fb = rng.integers(0, p, 4) if fixed == 'b' else None; fc = rng.integers(0, p, 4) if fixed == 'c' else None
        sm = Sampler(rng, G6, Zb, Zc, fix_b=fb, fix_c=fc)
        for d in range(0, 9):
            monos = [(m + (0,) * 4) if fixed == 'c' else ((0,) * 4 + m) for m in monomials(d)]
            X, S = stable_sections(sm, monos, k)
            log('  sections in %s of degree %d: dimension %d  (%d sample points)' % (name, d, 0 if X is None else len(X), S))
            if X is not None and len(X): res[fixed] = d; break
    db0, dc0 = res.get('c', 0), res.get('b', 0)
    log('lower bounds: degree >= %d in b6, >= %d in c6' % (db0, dc0))
    cands = sorted([(db, dc) for db in range(db0, 9) for dc in range(dc0, 9)],
                   key=lambda t: (len(monomials(t[0])) * len(monomials(t[1])), t))
    sm = Sampler(rng, G6, Zb, Zc)
    for db, dc in cands:
        mb, mc = monomials(db), monomials(dc)
        monos = [a + b for a in mb for b in mc]; N = len(monos)
        if k * N > 9000: log('stopping: bidegree (%d,%d) needs %d unknowns' % (db, dc, k * N)); break
        t1 = time.time(); X, S = stable_sections(sm, monos, k)
        dim = 0 if X is None else len(X)
        log('joint bidegree (%d,%d): %d monomials, %d sample points (dimension stable), sections: dimension %d  (%.0fs)'
            % (db, dc, N, S, dim, time.time() - t1))
        if dim:
            np.save(OUT + '/search_%d.npy' % p, {'k': k, 'db': db, 'dc': dc, 'J': sm.J, 'dim': dim}, allow_pickle=True)
            log('MINIMAL JOINT BIDEGREE (%d, %d), %d independent section(s), J = %s' % (db, dc, dim, sm.J))
            return

def psi_from_lambda(X, V, Nn, k):
    """full coefficient matrices (N x 225) of the sections with lambda-coefficients X (rows), by exact interpolation."""
    N = V.shape[1]; idx = rref(V.T)[1]; Vi = inv(V[idx]); out = []
    for x in X:
        lam = np.stack([mm(V, x[r * N:(r + 1) * N][:, None])[:, 0] for r in range(k)], 1)
        vals = np.einsum('tr,trq->tq', lam, Nn) % p
        C = mm(Vi, vals[idx])
        assert np.array_equal(mm(V, C), vals), 'interpolation inconsistent'
        out.append(C)
    return np.array(out)

def solve(db, dc):
    Zb, Zc, _ = load_setup()
    rng = np.random.default_rng(1000 + p % 1000)
    G6 = rng.integers(0, p, (245, 6, 6))
    sm = Sampler(rng, G6, Zb, Zc)
    monos = [a + b for a in monomials(db) for b in monomials(dc)]
    k = len(coker(rng.integers(0, p, 4), rng.integers(0, p, 4), G6, Zb, Zc))
    X, S = stable_sections(sm, monos, k)
    pts, Nn = sm.grow(S)
    C = psi_from_lambda(X, mono_matrix(pts, monos), Nn, k)           # (s, N, 225)
    flatC = C.transpose(0, 2, 1).reshape(len(C), -1)                # index = coordinate * N + monomial
    B, piv = rref(flatC)
    ok = True
    for t in range(4):                                              # fresh points, fresh source points
        b6, c6 = rng.integers(0, p, 4), rng.integers(0, p, 4)
        Fm = flatlib.flat(F0, (E6, np.vstack([FRAME, b6]) % p, np.vstack([FRAME, c6]) % p), (rng.integers(0, p, (245, 6, 6)), Zb, Zc)) % p
        mv = mono_matrix(np.concatenate([b6, c6])[None] % p, monos)[0]
        Ps = np.einsum('sqn,n->sq', B.reshape(len(B), 225, len(monos)), mv) % p
        ok &= not mm(Fm, Ps.T).any(); rk = rank(Ps)
    log('prime %d: bidegree (%d,%d): %d sections (stable at %d sample points), canonical basis pivots %s; fresh points: '
        'F psi = 0 %s, rank of the sections at a fresh point %d' % (p, db, dc, len(B), S, piv, ok, rk))
    np.save(OUT + '/psi_%d.npy' % p, {'B': B, 'piv': piv, 'monos': monos, 'db': db, 'dc': dc}, allow_pickle=True)

def ratrec(a, M):
    r0, r1, s0, s1 = M, int(a) % M, 0, 1
    while 2 * r1 * r1 > M:
        q = r0 // r1; r0, r1, s0, s1 = r1, r0 - q * r1, s1, s0 - q * s1
    return (r1, s1) if 2 * s1 * s1 <= M else None

def recon():
    import glob
    from fractions import Fraction
    from math import gcd
    D = {int(f.split('_')[-1][:-4]): np.load(f, allow_pickle=True).item() for f in glob.glob(OUT + '/psi_*.npy')}
    primes = sorted(D); assert all(D[q]['piv'] == D[primes[0]]['piv'] for q in primes), 'pivot structure differs'
    def rec(qs):
        M = 1
        for q in qs: M *= q
        X = np.zeros(D[qs[0]]['B'].shape, dtype=object)
        for q in qs:
            Mq = M // q; X = X + D[q]['B'].astype(object) * (Mq * pow(Mq, -1, q))
        X = X % M
        out = np.empty(X.shape, dtype=object); fail = 0
        for idx, v in np.ndenumerate(X):
            r = ratrec(v, M)
            if r is None: fail += 1; out[idx] = None
            else: out[idx] = Fraction(r[0], r[1])
        return out, fail
    held = primes[-1]
    R, fail = rec(primes[:-1])
    agree = fail == 0 and all((x.numerator * pow(x.denominator, -1, held)) % held == int(y) for x, y in zip(R.ravel(), D[held]['B'].ravel()))
    log('rational reconstruction from %d primes: %d failures; agrees with the held-out prime %d: %s' % (len(primes) - 1, fail, held, agree))
    if not agree: return
    R, fail = rec(primes)
    ints = []
    for row in R:
        den = 1
        for x in row: den = den * x.denominator // gcd(den, x.denominator)
        v = [int(x * den) for x in row]; g_ = 0
        for x in v: g_ = gcd(g_, x)
        ints.append([x // g_ for x in v])
    mx = max(abs(x) for row in ints for x in row)
    log('exact sections over Q: %d, primitive integer coefficient vectors, max |coefficient| = %d (%d digits)' % (len(ints), mx, len(str(mx))))
    np.save(OUT + '/psi_exact.npy', {'ints': ints, 'monos': D[primes[0]]['monos'], 'primes': primes}, allow_pickle=True)

PRIMES = [524287, 524269, 524261, 524257, 524243, 524231, 524221, 524219, 524203, 524201, 524197, 524189, 524171,
          524149, 524123, 524119, 524113, 524099, 524087, 524081, 524071, 524063, 524057, 524053]
DJ = {0: 1500, 1: 1560, 2: 1050, 3: 525}          # dim of the m6 = j part of S^{62}C^6 (branching to C^5 + C)
N1V = 1700

def source_parts_gram(alpha, beta, rng, NH=1600):
    """for each j <= 3: rank mod p of <x_{g_i}^{(j)}, x'_{H_l}>, x_g = (alpha^beta)^2 alpha^4, pairing D1^4 D2^2."""
    H = rng.integers(0, p, (NH, 6, 2))
    vals = []
    for s_ in range(9):
        a = alpha.copy(); b = beta.copy(); a[:, 5] *= s_; b[:, 5] *= s_
        m = [mm(x % p, H[:, :, c].T) for x in (a, b) for c in (0, 1)]       # m11, m12, m21, m22  (N1 x NH)
        d2 = (m[0] * m[3] - m[1] * m[2]) % p; d1 = m[0]
        v = (d1 * d1) % p; v = (v * v) % p; v = (v * ((d2 * d2) % p)) % p
        vals.append(v)
    Vs = np.array([[pow(s_, j, p) for j in range(9)] for s_ in range(9)], dtype=np.int64)
    coef = mm(inv(Vs), np.array(vals).reshape(9, -1)).reshape(9, *vals[0].shape)
    return [rank(coef[j]) for j in range(4)]

def bound_F(amax, bmax):
    """a priori bound on |coefficient of F(b6, c6)| for integer source points (|alpha| <= amax, |beta| <= bmax), target
    points with entries in {-1,0,1} and the 0/1 frame: (number of words s: [8] -> [6] whose A-, B- and C-columns use
    distinct terms) * max|A-part| * max||B-part||_1 * max||C-part||_1, with ||det||_1 <= l! 4^l per column of length l."""
    from math import factorial
    W = np.array(list(itertools.product(range(6), repeat=8)), dtype=np.int8); ok = np.ones(len(W), bool)
    for cols in [F0[0], F0[1], F0[2]]:
        for col in cols:
            for a, b in itertools.combinations(col, 2): ok &= W[:, a] != W[:, b]
    maxA = (2 * amax * bmax) ** 2 * amax ** 4
    maxB = 1
    for col in F0[1]: maxB *= factorial(len(col)) * 4 ** len(col)
    return int(ok.sum()) * maxA * maxB * maxB

def vsetup():
    rng = np.random.default_rng(31)
    alpha = rng.integers(-3, 4, (N1V, 6)); beta = rng.integers(-1, 2, (N1V, 6))
    while True:                                   # a point with alpha_6 = beta_6 = 0 has no S_1, S_2, S_3 component
        bad = (alpha[:, 5] == 0) & (beta[:, 5] == 0)
        if not bad.any(): break
        alpha[bad, 5] = rng.integers(-3, 4, bad.sum()); beta[bad, 5] = rng.integers(-1, 2, bad.sum())
    t1 = time.time(); rk = source_parts_gram(alpha, beta, rng)
    log('source points: %d integer pairs (alpha in {-3..3}^6, beta in {-1,0,1}^6); Gram ranks of the parts S_0..S_3 = %s, dimensions %s: %s  (%.0fs)'
        % (N1V, rk, [DJ[j] for j in range(4)], 'SPANNING' if rk == [DJ[j] for j in range(4)] else 'NOT spanning', time.time() - t1))
    np.save(OUT + '/vsetup.npy', {'alpha': alpha, 'beta': beta, 'gram_ranks': rk}, allow_pickle=True)

MONO_F = [a + b for j in range(4) for a in monomials(j) for b in monomials(j)]        # 517 monomials of F
def F_coeffs(G6, Zb, Zc, rng):
    """exact coefficients mod p of F(b6, c6) (rows = source points, 225 target points) in the basis MONO_F (int32)."""
    while True:
        pts = rng.integers(0, p, (len(MONO_F), 8)); V = mono_matrix(pts, MONO_F)
        if rank(V) == len(MONO_F): break
    Vi = inv(V); vals = np.zeros((len(MONO_F), G6.shape[0] * 225), dtype=np.float64)
    for t, pt in enumerate(pts):
        b = np.vstack([FRAME, pt[:4]]) % p; c = np.vstack([FRAME, pt[4:]]) % p
        vals[t] = flatlib.flat(F0, (E6, b, c), (G6, Zb, Zc)).ravel() % p
    C = np.fmod(np.asarray(Vi, dtype=np.float64) @ vals, p).astype(np.int32)
    return C.reshape(len(MONO_F), G6.shape[0], 225)

_PIDX = None
def product_zero(C, psis):
    """psi^T F mod p (C: (517, rows, 225) coefficients of F; psis: (s, 225, Npsi) mod p); True iff all vanish."""
    global _PIDX
    if _PIDX is None:
        mono_psi = [a + b for a in monomials(2) for b in monomials(2)]
        prod = {}; idx = np.zeros((len(mono_psi), len(MONO_F)), dtype=np.int64)
        for i, mu in enumerate(mono_psi):
            for j, nu in enumerate(MONO_F):
                key = tuple(x + y for x, y in zip(mu, nu)); idx[i, j] = prod.setdefault(key, len(prod))
        _PIDX = (idx, len(prod))
    idx, nprod = _PIDX; ok = True
    for r0 in range(0, C.shape[1], 40):
        Cb = C[:, r0:r0 + 40, :].astype(np.float64)                                        # (517, rows, 225)
        P = np.fmod(np.tensordot(psis.astype(np.float64), Cb, axes=([1], [2])), p)        # (s, Npsi, 517, rows)
        I = np.zeros((P.shape[0], P.shape[3], nprod))
        for j in range(len(MONO_F)):
            I[:, :, idx[:, j]] += P[:, :, j, :].transpose(0, 2, 1)
        ok &= not np.fmod(I, p).any()
    return ok

def garner(rs, qs):
    """mixed-radix digits of the CRT lift of the residues rs (int arrays) modulo qs."""
    ds = []
    for i, q in enumerate(qs):
        x = rs[i].astype(np.int64) % q
        for j in range(i):
            x = ((x - ds[j]) % q) * pow(qs[j], -1, q) % q
        ds.append(x)
    return ds

def lift_mod(ds, qs, q2, M):
    """symmetric CRT lift (|x| < M/2) reduced mod q2, plus float magnitudes."""
    x = ds[-1] % q2; xf = ds[-1].astype(np.float64)
    for i in range(len(qs) - 2, -1, -1):
        x = (x * (qs[i] % q2) + ds[i]) % q2; xf = xf * qs[i] + ds[i]
    neg = xf > M / 2
    x = np.where(neg, (x - M % q2) % q2, x); xf = np.where(neg, xf - M, xf)
    return x, xf

def verify(lo, hi):
    from math import prod as mprod
    D = np.load(OUT + '/vsetup.npy', allow_pickle=True).item()
    E = np.load(OUT + '/psi_exact.npy', allow_pickle=True).item()
    ints = E['ints']; s_ = len(ints); Npsi = len(E['monos'])
    alpha, beta = D['alpha'][lo:hi], D['beta'][lo:hi]
    G6 = np.zeros((hi - lo, 6, 6), dtype=np.int64); G6[:, :, 0] = alpha; G6[:, :, 1] = beta
    BF = bound_F(int(np.abs(alpha).max()), int(np.abs(beta).max()))     # a priori bound on |coefficient of F|
    qs = PRIMES[:4]; M = mprod(qs); assert M > 2 * BF, (M, BF)
    psis_mod = lambda q: np.array([[[x % q for x in row[k * Npsi:(k + 1) * Npsi]] for k in range(225)] for row in ints], dtype=np.int64)
    Cs = []
    for q in qs:
        set_prime(q); Zb, Zc, _ = load_setup(); rng = np.random.default_rng(q)
        t1 = time.time(); Cs.append(F_coeffs(G6 % q, Zb, Zc, rng))
        log('rows %d-%d, prime %d: F interpolated (%.0fs); psi^T F == 0 mod %d: %s' % (lo, hi, q, time.time() - t1, q, product_zero(Cs[-1], psis_mod(q))))
    maxF = 0.0
    for r0 in range(0, hi - lo, 40):
        ds = garner([C[:, r0:r0 + 40, :] for C in Cs], qs)
        _, xf = lift_mod(ds, qs, qs[0], M); maxF = max(maxF, float(np.abs(xf).max()))
    maxF = int(maxF * (1 + 1e-9)) + 1
    assert maxF <= BF, 'a priori bound violated?'
    maxpsi = max(abs(x) for row in ints for x in row)
    bound = 225 * Npsi * maxpsi * maxF
    log('rows %d-%d: exact F by CRT (|F| < %.1e a priori, prod of 4 primes %.1e), max |coefficient of F| <= %d; bound on psi^T F: %.2e'
        % (lo, hi, BF, M, maxF, bound))
    used = list(qs); extra = [q for q in PRIMES if q not in qs]; allok = True
    while mprod(used) <= 2 * bound:
        q = extra.pop(0); set_prime(q); okq = True; pq = psis_mod(q)
        for r0 in range(0, hi - lo, 40):
            ds = garner([C[:, r0:r0 + 40, :] for C in Cs], qs)
            x, _ = lift_mod(ds, qs, q, M)
            okq &= product_zero(x, pq)
        allok &= okq; used.append(q)
        log('rows %d-%d, extra prime %d: psi^T F == 0: %s' % (lo, hi, q, okq))
    log('rows %d-%d: RESULT psi^T F == 0 over Z for all %d sections: %s (primes used %d, product %.2e > 2*bound %.2e)'
        % (lo, hi, s_, allok, len(used), mprod(used), 2 * bound))

def fullrank():
    rng = np.random.default_rng(77)
    Zb, Zc, _ = load_setup()
    T7 = tuple(rng.integers(-3, 4, (7, 4)) for _ in range(3))           # explicit integer rank-7 tensor
    G4 = rng.integers(-3, 4, (400, 4, 4))     # integer source points (first two columns used); no spanning needed:
                                              # rank of the evaluation matrix <= rank of the flattening
    F = flatlib.flat(F0, tuple(x % p for x in T7), (G4 % p, Zb, Zc)) % p
    log('explicit integer rank-7 tensor (entries in {-3..3}, seed 77): rank of F_{P0} mod %d = %d  => rank over Q >= %d'
        % (p, rank(F), rank(F)))
    E = np.load(OUT + '/psi_exact.npy', allow_pickle=True).item(); ints = E['ints']; Npsi = len(E['monos'])
    b6, c6 = np.array([2, -1, 3, 1]), np.array([1, 3, -2, 2])                # explicit integer point
    mv = mono_matrix(np.concatenate([b6, c6])[None] % p, E['monos'])[0]
    Ps = np.array([[sum(int(row[k * Npsi + n]) * int(mv[n]) for n in range(Npsi)) % p for k in range(225)] for row in ints])
    log('the %d exact sections at (b6, c6) = (%s, %s): rank mod %d = %d  => rank over Q >= %d' % (len(ints), [int(x) for x in b6], [int(x) for x in c6], p, rank(Ps), rank(Ps)))
    np.save(OUT + '/fullrank.npy', {'T7': T7, 'b6': b6, 'c6': c6}, allow_pickle=True)

if __name__ == '__main__':
    if STAGE == 'setup': setup()
    elif STAGE == 'search': search()
    elif STAGE == 'solve': solve(int(sys.argv[3]), int(sys.argv[4]))
    elif STAGE == 'recon': recon()
    elif STAGE == 'vsetup': vsetup()
    elif STAGE == 'verify': verify(int(sys.argv[2]), int(sys.argv[3]))
    elif STAGE == 'fullrank': fullrank()
