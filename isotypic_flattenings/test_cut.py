"""python3 test_cut.py <empty dir>   rankscan: (1) the leading-block rank used for adjacent ends,
min(cut, rank F), against full evaluations (every adjacent pair of a few g = 1 directions, block mode forced by a small
MEMCAP); (2) a finished profile is reused from its cache file by a new worker; (3) resolve() with adjacent ends gives
the same separations with and without the cut."""
import os, sys, shutil, numpy as np
CK = sys.argv[1]
shutil.rmtree(CK, ignore_errors=True)
os.environ.update(MEMCAP=str(2 ** 12), CKPT=CK, CKPT_EVERY='0', OPENBLAS_NUM_THREADS='1')
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rankscan as R
from hwv import p
from isoflat import kronecker
SEED = 5


def direction(n, d, lam, t, rprobe):
    g = kronecker(*lam)
    rgen = R.generic_rank(n)
    vecs = {s: tuple(np.random.default_rng([SEED, n, s, u]).integers(0, p, (s, n)) for u in range(3)) for s in range(1, rgen + 1)}
    return R.Direction(n, lam, g, t, np.random.default_rng([SEED, n, d, 0]), vecs, rprobe)


ok = True
# (1) leading block vs full rank, every adjacent pair with rank(r) + EXTRA < min(N1, K)
for n, d, lam, t, rs in [(4, 3, ((3,), (1, 1, 1), (1, 1, 1)), 0, range(2, 8)),
                         (5, 5, ((4, 1), (2, 1, 1, 1), (2, 1, 1, 1)), 0, range(5, 11)),
                         (5, 6, ((4, 2), (2, 2, 2), (2, 1, 1, 1, 1)), 0, range(6, 11))]:
    D = direction(n, d, lam, t, max(rs))
    R.CKPT = ''
    full = {r: D.profile(r)['H'][0] for r in rs}
    R.CKPT = CK
    print('(1)', n, d, lam, 'N1 K', D.N1, D.K, 'full ranks', full)
    for r in rs:
        if r + 1 not in full or full[r] + R.EXTRA >= min(D.N1, D.K):
            continue
        cut = full[r] + R.EXTRA
        part = D.profile(r + 1, cut)['H'][0]
        good = part == min(cut, full[r + 1]) and (part > full[r]) == (full[r + 1] > full[r])
        ok &= good
        print('    r=%d vs %d: rank %d / %d, leading %d-block %d  %s' % (r, r + 1, full[r], full[r + 1], cut, part,
                                                                            'ok' if good else 'MISMATCH'))
left = [x for x in os.listdir(CK) if not x.endswith('_prof.json') and '_prof_' not in x]
print('    checkpoint files left (should be none):', left)
ok &= not left

# (2) cached profile: a new worker (new Direction) returns it without evaluating
shutil.rmtree(CK, ignore_errors=True)
lam = ((4, 1), (2, 1, 1, 1), (2, 1, 1, 1))
A = direction(5, 5, lam, 0, 10)
PA = A.profile(8)
B = direction(5, 5, lam, 0, 10)
calls = {'k': 0}
orig = R.compute_F
def counting(*a, **kw):
    calls['k'] += 1
    return orig(*a, **kw)
R.compute_F = counting
PB = B.profile(8)
R.compute_F = orig
good = PA == PB and calls['k'] == 0 and B.prof_files == A.prof_files
ok &= good
print('(2) cached profile reused:', PA, PB, 'evaluations', calls['k'], 'ok' if good else 'MISMATCH')

# (3) resolve with adjacent ends (rmax_feasible = rlo + 1): cut and no cut agree
for n, d, lam, rlo in [(5, 5, ((4, 1), (2, 1, 1, 1), (2, 1, 1, 1)), 7), (5, 5, ((4, 1), (2, 1, 1, 1), (2, 1, 1, 1)), 9)]:
    shutil.rmtree(CK, ignore_errors=True)
    out = []
    for cut in (False, True):
        R.CUT = cut
        D = direction(n, d, lam, 0, rlo + 1)
        prof, sep, unknown, sat = R.resolve(D, [rlo], rlo, rlo + 1)
        out.append((sep, unknown, sat, dict(D.cuts)))
    good = out[0][:3] == out[1][:3]
    ok &= good
    print('(3) rlo=%d  no cut: sep %s unknown %s sat %s | cut: sep %s unknown %s sat %s cuts %s  %s'
          % (rlo, *out[0][:3], *out[1], 'ok' if good else 'MISMATCH'))
print('ALL OK' if ok else 'FAILURES')
