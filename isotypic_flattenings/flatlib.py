"""flat(filling, vecs, gs): HWV flattening matrix with hwv_fast, memory-safe: process address space capped (MEMLIMIT_GB,
default 4: MemoryError instead of an OOM kill), contraction path cached per filling and shapes, evaluation points split
into blocks (Z first, then Y) until the path's largest intermediate is below MEMCAP, minors only for the column
lengths the filling uses (factors may have different dimensions)."""
import sys, os, resource, numpy as np
_lim = int(float(os.environ.get('MEMLIMIT_GB', '4')) * 2 ** 30)
resource.setrlimit(resource.RLIMIT_AS, (_lim, _lim))     # fail with MemoryError instead of an OOM kill
sys.path.insert(0, '/home/user/claude/isotypic_flattenings')
import opt_einsum as oe
from hwv_fast import prepare, build_network, find_path, execute
MEMCAP = 1 << 24

def slice_pm(pm, ys, zs):
    return [{l: A[ys] for l, A in pm[0].items()}, {l: A[zs] for l, A in pm[1].items()}, {l: A[zs] for l, A in pm[2].items()}]

_paths = {}
def flat(f, vecs, gs, key=None):
    vm, pm = prepare(vecs, gs, ells=sorted({len(col) for cols in f for col in cols}))   # only the column lengths used
    N1, K = gs[0].shape[0], gs[1].shape[0]
    k0 = (tuple(tuple(tuple(int(x) for x in col) for col in cols) for cols in f), tuple(v.shape for v in vecs), N1, K)   # path depends on the filling
    if k0 not in _paths:
        yb, zb = N1, K
        while True:
            ops, out = build_network(f, vm, slice_pm(pm, slice(0, yb), slice(0, zb)))
            path, info = find_path(ops, out, None, oe.RandomGreedy(max_repeats=64))
            if int(info.largest_intermediate) <= MEMCAP: break
            if zb <= 8 and yb <= 8:
                raise MemoryError('no block split keeps intermediates below MEMCAP (%d)' % int(info.largest_intermediate))
            if zb > 8: zb = (zb + 1) // 2
            else: yb = (yb + 1) // 2
        _paths[k0] = (yb, zb, path)
    yb, zb, path = _paths[k0]
    F = np.zeros((N1, K), dtype=np.int64)
    for y0 in range(0, N1, yb):
        for z0 in range(0, K, zb):
            ys, zs = slice(y0, min(N1, y0 + yb)), slice(z0, min(K, z0 + zb))
            ops, out = build_network(f, vm, slice_pm(pm, ys, zs))
            F[ys, zs] = execute(ops, out, path)       # a path is valid for any block shape; smaller blocks only shrink it
    return F
