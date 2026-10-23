"""test_speedup.py -- checks of the 2026-10-23 speed-ups of rankscan.py (SPEEDUP_rankscan.md):
  1. compute_F planned evaluation (NEWEVAL) == old block search, entry by entry, unblocked and tiled (small MEMCAP),
     into float64 and float32 destinations, and through a checkpoint interruption (resume by new and by old code);
  2. _rref_blocked == RREF._gauss_jordan (rows sorted by pivot) on random and rank-deficient matrices;
  3. cheap_basis: the evaluation basis mapped back by Ainv gives exactly the old matrices F_i (g = 1 and g >= 2),
     and Direction.profile is identical with and without it.
python3 test_speedup.py   (a few minutes; OPENBLAS_NUM_THREADS=1 or 2)"""
import os, sys, tempfile, time
import numpy as np
import rankscan as rs

p = rs.p
fails = 0


def check(name, ok):
    global fails
    print(('ok   ' if ok else 'FAIL ') + name, flush=True)
    fails += not ok


def setup(n, d, lam, t, seed=5):
    rgen = rs.generic_rank(n)
    vecs = {r: tuple(np.random.default_rng([seed, n, r, u]).integers(0, p, (r, n)) for u in range(3)) for r in range(1, rgen + 1)}
    allc = {l: (li, g) for li, l, g in rs.components(n, d)}
    li, g = allc[lam]
    crng = np.random.default_rng([seed, n, d, li])
    for u in rs.distinct_dirs(lam):
        perm_lam = tuple(lam[v] for v in [u] + [v for v in range(3) if v != u])
        rmax = max([q for q in range(1, rgen + 1) if rs.word_minor_size(perm_lam, n, q) <= rs.WCAP] or [0])
        D = rs.Direction(n, lam, g, u, crng, vecs, min(rmax, rgen))
        if u == t:
            return D


def F_with(D, r, fill, memcap, new, dest=None, ckpt=None):
    rs.MEMCAP, rs.NEWEVAL = memcap, new
    rs._plan_cache.clear()
    return np.array(rs.compute_F(fill, D.vm(r), D.pm, None, None, ckpt=ckpt, dest=dest), dtype=np.float64)


# ---- 1. planned evaluation
MEM0, NEW0, FP0 = rs.MEMCAP, rs.NEWEVAL, rs.FILLPOOL
rs.FILLPOOL = 0
rs.PLANMIN = 0.0                     # plan even the tiny test networks
cases = [(4, 4, ((2, 2), (2, 1, 1), (2, 1, 1)), 0, 5), (4, 6, ((3, 1, 1, 1), (2, 2, 1, 1), (2, 2, 1, 1)), 0, 6),
         (5, 5, ((3, 2), (3, 1, 1), (3, 1, 1)), 1, 7), (4, 6, ((4, 2), (4, 2), (3, 2, 1)), 2, 6)]
for n, d, lam, t, r in cases:
    D = setup(n, d, lam, t)
    f = D.fillings[0][0]
    ref = F_with(D, r, f, 1 << 25, False)
    for mc in (1 << 25, 1 << 16, 1 << 13, 1 << 11):
        try:
            Fo = F_with(D, r, f, mc, False)
        except rs.Infeasible:
            Fo = None
        Fn = F_with(D, r, f, mc, True)
        Fd = np.empty(Fn.shape, dtype=np.float32)
        F_with(D, r, f, mc, True, dest=Fd)
        check('planned F n=%d d=%d %s dir %d r=%d MEMCAP=2^%d (old %s)' % (n, d, lam, t, r, mc.bit_length() - 1,
              'infeasible' if Fo is None else 'equal' if np.array_equal(Fo, ref) else 'DIFF'),
              np.array_equal(Fn, ref) and np.array_equal(Fd.astype(np.float64), ref) and (Fo is None or np.array_equal(Fo, ref)))

# checkpoint: interrupt the planned block loop, resume with new and with old code
with tempfile.TemporaryDirectory() as td:
    n, d, lam, t, r = 4, 6, ((3, 1, 1, 1), (2, 2, 1, 1), (2, 2, 1, 1)), 0, 6
    D = setup(n, d, lam, t)
    f = D.fillings[0][0]
    ref = F_with(D, r, f, 1 << 25, False)
    for resume_new in (True, False):
        ck = os.path.join(td, 'ck%d' % resume_new)
        rs.CKPT_EVERY = -1.0                                    # save after every block
        orig = rs.hwv_fast.single_reduce
        calls = [0, 10 ** 9]

        def count(*a, **k):
            calls[0] += 1
            return orig(*a, **k)
        rs.hwv_fast.single_reduce = count
        F_with(D, r, f, 1 << 11, True)                          # number of calls of an uninterrupted evaluation
        rs.hwv_fast.single_reduce = orig
        calls[:] = [0, calls[0] // 2]

        def boom(*a, **k):
            calls[0] += 1
            if calls[0] == calls[1]:
                raise KeyboardInterrupt
            return orig(*a, **k)
        rs.hwv_fast.single_reduce = boom
        try:
            F_with(D, r, f, 1 << 11, True, ckpt=ck)
            interrupted = False
        except KeyboardInterrupt:
            interrupted = True
        rs.hwv_fast.single_reduce = orig
        import json
        meta = json.load(open(ck + '.json'))
        Fr = F_with(D, r, f, 1 << 11, resume_new, ckpt=ck)
        rs.CKPT_EVERY = 1800.0
        check('checkpoint of the planned loop (order %s, next %d / next2 %d) resumed by %s code' %
              (meta.get('order'), meta['next'], meta['next2'], 'new' if resume_new else 'old'),
              interrupted and np.array_equal(Fr, ref))
    # forced tiling with Z blocks outside and Y blocks inside (order 'Z': the old loop must restart, not skip)
    vm = D.vm(r)
    ops, out = rs.build_network(f, vm, D.pm)
    cap = max(1 << 25, max(A.size for _, A in ops))
    for resume_new in (True, False):
        rs.MEMCAP, rs.NEWEVAL = 1 << 25, True
        rs._plan_cache.clear()
        pl = rs.plan_eval(ops, out, cap)
        P = pl[1]
        key = (repr(rs._plain(f)), tuple((i, A.shape) for i, A in ops), cap, False)
        forced = (pl[0], P, 2, -(-P.N[2] // 3), -(-P.N[1] // 4))
        ck = os.path.join(td, 'ckz%d' % resume_new)
        rs.CKPT_EVERY = -1.0
        orig = rs.hwv_fast.single_reduce
        calls = [0]

        def boom(*a, **k):
            calls[0] += 1
            if calls[0] == 6:
                raise KeyboardInterrupt
            return orig(*a, **k)
        rs.hwv_fast.single_reduce = boom
        rs._plan_cache[key] = forced
        try:
            rs.compute_F(f, vm, D.pm, ckpt=ck)
            interrupted = False
        except KeyboardInterrupt:
            interrupted = True
        rs.hwv_fast.single_reduce = orig
        meta = json.load(open(ck + '.json'))
        rs._plan_cache[key] = forced
        rs.NEWEVAL = resume_new
        Fr = np.array(rs.compute_F(f, vm, D.pm, ckpt=ck), dtype=np.float64)
        rs.CKPT_EVERY = 1800.0
        check('checkpoint of a Z-outer tiling (order %s, next %d / next2 %d) resumed by %s code' %
              (meta.get('order'), meta['next'], meta['next2'], 'new' if resume_new else 'old'),
              interrupted and meta['order'] == 'Z' and meta['next'] == 0 and np.array_equal(Fr, ref))
rs.MEMCAP, rs.NEWEVAL = MEM0, NEW0

# ---- 2. blocked RREF
rng = np.random.default_rng(1)
for (m, N, rk) in [(5, 7, 3), (128, 1000, 128), (128, 1000, 50), (200, 150, 150), (128, 3000, 100), (64, 64, 64), (130, 300, 129)]:
    Y = (rng.integers(0, p, (m, rk)).astype(object).dot(rng.integers(0, p, (rk, N)).astype(object)) % p).astype(np.float64)
    Y[:, 3] = 0
    R0, p0 = rs.RREF._gauss_jordan(Y.copy())
    R1, p1 = rs._rref_blocked(Y)
    o = np.argsort(p0)
    check('rref %dx%d rank %d' % (m, N, len(p1)), np.array_equal(p0[o], p1) and np.array_equal(R0[o], R1))
for (N, rows) in [(300, 700), (1000, 400)]:
    X = rng.integers(0, p, (rows, N)).astype(np.float64)
    X[rows // 2:] = X[:rows - rows // 2]                         # duplicated rows
    ranks = []
    for old in (True, False):
        rs.RREF_OLD = old
        E = rs.RREF(N)
        ranks.append([E.add(X[s:s + 97]) for s in range(0, rows, 97)])
    rs.RREF_OLD = False
    check('RREF prefix ranks %s' % ranks[1], ranks[0] == ranks[1])

# ---- 3. evaluation basis
rs.FILLPOOL, rs.FILLMIN, rs.FILLMIN_GREEDY, rs.FILLGAIN = 1500, 0.0, 0.0, 10.0      # always switch (test)
for n, d, lam, t, r in [(4, 6, ((3, 1, 1, 1), (2, 2, 1, 1), (2, 2, 1, 1)), 0, 6), (4, 6, ((5, 1), (3, 2, 1), (3, 2, 1)), 0, 6),
                        (5, 5, ((3, 2), (3, 1, 1), (3, 1, 1)), 1, 7), (4, 6, ((4, 2), (4, 2), (3, 2, 1)), 2, 6)]:
    rs.FILLPOOL = 1500
    D = setup(n, d, lam, t)
    vm = D.vm(r)
    eb = D.eval_basis(r, vm, D.pm)
    if eb is None:
        check('evaluation basis chosen for %s' % (lam,), False)
        continue
    Fold = np.stack([rs.compute_F(fl[0], vm, D.pm) for fl in D.fillings]).astype(np.float32)
    Fe = np.stack([rs.compute_F(fl[0], vm, D.pm) for fl in eb[0]]).astype(np.float32)
    D.to_old_basis(Fe, eb[1])
    P1 = D.profile(r)
    rs.FILLPOOL = 0
    P0 = D.profile(r)
    check('evaluation basis g=%d %s dir %d (%s): F_old = Ainv E exactly; profile %s' %
          (D.span, lam, t, 'new fillings' if [f[0] for f in eb[0]] != [f[0] for f in D.fillings] else 'same fillings', P1),
          np.array_equal(Fold, Fe) and P0 == P1)
rs.FILLPOOL = FP0
print('%d failure(s)' % fails)
sys.exit(1 if fails else 0)
