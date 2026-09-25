"""Faster exact (mod p) evaluation of the HWV flattening matrices of hwv.py -- same numbers, different contraction.

hwv.flattening_matrix(lam, fillings, vecs, gs) returns F[Y, Z] = sum over words s in [r]^d of
    prod_{columns c of filling 1} D(g1_Y, a_{s_c}) * prod_{c of filling 2} D(g2_Z, b_{s_c}) * prod_{c of filling 3} D(g3_Z, c_{s_c}),
D(g, v_{s_c}) = det(V_{s_c} g[:, :|c|]) (|c| x |c|).  Here, as in hwv.py, all arithmetic is mod p, but
 (1) every column determinant is factored by Cauchy-Binet through Lambda^{|c|} C^n:
         D(g_b, v_{s_c}) = sum_{I in binom([n], |c|)} P[b, I] * M[I, s_c],
     P[b, I] = det g_b[I, :|c|] (minors of the evaluation point), M[I, s_c] = det V[s_c, I] (minors of the rank-one
     factors).  For |c| = n = 4 the factor is det(g_b) * det(V[s_c]) and I has size 1.  The network then has small
     bonds (C(n,|c|) <= 6 instead of r^|c|);
 (2) the pairwise contraction order is found by opt_einsum (flop count, with a cap on the intermediate size);
 (3) all tensors are float64 arrays holding the residues 0..p-1 and every pairwise contraction is a float64 BLAS
     matmul: products are < p^2 < 2^38, so a dot product of at most 2^15 terms is < 2^53 and computed exactly
     (longer ones are split), then reduced with fmod.
flattening_matrix_fast(...) is a drop-in replacement for hwv.flattening_matrix (checked equal entry by entry in
test_fast.py)."""
import numpy as np, itertools
from itertools import combinations
import opt_einsum as oe
from hwv import p, col_dets

NCMAX = 1 << 15          # max number of summands per exact float64 dot product: 2^15 * p^2 < 2^53
MEMCAP = 1 << 25         # default cap (elements) on intermediates of a contraction path

def _fmod(A):
    return np.fmod(A, p, out=A) if isinstance(A, np.ndarray) and A.dtype == np.float64 else np.fmod(A, p)

def fmatmul(A, B):
    """exact (nb, na, nc) @ (nb, nc, nbb) mod p on float64 arrays holding integers in [0, p)."""
    nc = A.shape[-1]
    if nc <= NCMAX:
        return _fmod(np.matmul(A, B))
    out = None
    for i in range(0, nc, NCMAX):
        C = _fmod(np.matmul(A[..., i:i + NCMAX], B[..., i:i + NCMAX, :]))
        out = C if out is None else _fmod(out + C)
    return out

def matmul_mod(A, B):
    """int64 interface: exact (nb, na, nc) @ (nb, nc, nbb) mod p."""
    return fmatmul((np.asarray(A) % p).astype(np.float64), (np.asarray(B) % p).astype(np.float64)).astype(np.int64)

def pair_contract(ia, A, ib, B, keep):
    """contract A (index string ia) with B (ib); result has index string `keep` (sub-multiset of ia+ib).
    A, B float64 with integer entries in [0, p); result likewise."""
    for idx in list(ia):
        if idx not in ib and idx not in keep:
            A = _fmod(A.sum(axis=ia.index(idx))); ia = ia.replace(idx, '')
    for idx in list(ib):
        if idx not in ia and idx not in keep:
            B = _fmod(B.sum(axis=ib.index(idx))); ib = ib.replace(idx, '')
    batch = [i for i in ia if i in ib and i in keep]
    contr = [i for i in ia if i in ib and i not in keep]
    fa = [i for i in ia if i not in ib]; fb = [i for i in ib if i not in ia]
    dims = dict(zip(ia, A.shape)); dims.update(zip(ib, B.shape))
    A = np.transpose(A, [ia.index(i) for i in batch + fa + contr])
    B = np.transpose(B, [ib.index(i) for i in batch + contr + fb])
    size = lambda idx: int(np.prod([dims[i] for i in idx])) if idx else 1
    nb, na, nc, nbb = size(batch), size(fa), size(contr), size(fb)
    R = fmatmul(np.ascontiguousarray(A).reshape(nb, na, nc), np.ascontiguousarray(B).reshape(nb, nc, nbb))
    res_idx = ''.join(batch + fa + fb)
    R = R.reshape([dims[i] for i in res_idx])
    return np.transpose(R, [res_idx.index(i) for i in keep])

def single_reduce(ia, A, keep):
    for idx in list(ia):
        if idx not in keep:
            A = _fmod(A.sum(axis=ia.index(idx))); ia = ia.replace(idx, '')
    return np.transpose(A, [ia.index(i) for i in keep])

def execute(ops, out, path):
    """run an opt_einsum path with exact pairwise contractions (float64 arrays of residues); returns float64."""
    ops = list(ops)
    for step in path:
        step = sorted(step, reverse=True)
        taken = [ops.pop(k) for k in step]
        rest = set(''.join(i for i, _ in ops)) | set(out)
        while len(taken) > 1:
            (ia, A), (ib, B) = taken.pop(), taken.pop()
            others = rest | set(''.join(i for i, _ in taken))
            keep = ''.join(dict.fromkeys(i for i in ia + ib if i in others))
            taken.append((keep, pair_contract(ia, A, ib, B, keep)))
        ia, A = taken[0]
        keep = ''.join(dict.fromkeys(i for i in ia if i in rest))
        if keep != ia:
            A = single_reduce(ia, A, keep); ia = keep
        ops.append((ia, A))
    assert len(ops) == 1
    ia, A = ops[0]
    return single_reduce(ia, A, out)

_minor_cache = {}
def minors_of_points(G, ell):
    """P[b, I] = det G[b][I, :ell] for I in combinations(range(n), ell)  (G: (B, n, n))."""
    n = G.shape[1]
    D = col_dets(np.ascontiguousarray(G[:, :, :ell]), ell)           # (B, n, ..., n): rows i_1..i_ell
    subs = list(combinations(range(n), ell))
    return (np.stack([D[(slice(None),) + I] for I in subs], axis=1) % p).astype(np.float64)

def minors_of_vectors(V, ell):
    """M[I, s_1..s_ell] = det V[s_*, I]  (V: (r, n))."""
    n = V.shape[1]
    return (np.stack([col_dets(np.ascontiguousarray(V[None][:, :, list(I)]), ell)[0]
                     for I in combinations(range(n), ell)], axis=0) % p).astype(np.float64)

def build_network(fillings, vecs, pts):
    """ops (index string, array) and output string for F[Y, Z]; pts = (P-dicts) for the three factors."""
    sym = oe.get_symbol
    Y, Z = sym(0), sym(1)
    d = sum(len(c) for c in fillings[0])
    s = [sym(2 + j) for j in range(d)]
    nxt = 2 + d
    ops = []
    for t in range(3):
        batch = Y if t == 0 else Z
        for col in fillings[t]:
            ell = len(col); I = sym(nxt); nxt += 1
            ops.append((batch + I, pts[t][ell]))
            ops.append((I + ''.join(s[b] for b in col), vecs[t][ell]))
    return ops, Y + Z

def prepare(vecs, gs, ells=None, lams=None):
    """precompute minors: vm[t][ell] (vectors) and pm[t][ell] (evaluation points), for every column length ell of
    factor t: the column lengths of lams[t] if given, else `ells` (default: all 1..n_t; the factors may have
    different dimensions n_t = vecs[t].shape[1])."""
    def lengths(t):
        n_t = vecs[t].shape[1]
        if lams is not None: return sorted({sum(1 for r in lams[t] if r > j) for j in range(lams[t][0])})
        return [l for l in (ells if ells is not None else range(1, n_t + 1)) if l <= n_t]
    vm = [{l: minors_of_vectors(vecs[t], l) for l in lengths(t)} for t in range(3)]
    pm = [{l: minors_of_points(gs[t], l) for l in lengths(t)} for t in range(3)]
    return vm, pm

def find_path(ops, out, memcap=MEMCAP, optimize='auto-hq'):
    eq = ','.join(i for i, _ in ops) + '->' + out
    shapes = [A.shape for _, A in ops]
    path, info = oe.contract_path(eq, *shapes, shapes=True, optimize=optimize, memory_limit=memcap)
    return path, info

def largest_intermediate(ops, out, path):
    """largest number of elements of any intermediate produced along `path` (opt_einsum convention)."""
    idx = [i for i, _ in ops]; shapes = [A.shape for _, A in ops]; big = 0
    for step in path:
        step = sorted(step, reverse=True)
        ia = [idx[k] for k in step]; sh = [shapes[k] for k in step]
        dims = {}
        for i, s_ in zip(ia, sh): dims.update(zip(i, s_))
        for k in step: idx.pop(k); shapes.pop(k)
        others = set(''.join(idx)) | set(out)
        keep = ''.join(dict.fromkeys(c for i in ia for c in i if c in others))
        size = 1
        for c in keep: size *= dims[c]
        big = max(big, size)
        idx.append(keep); shapes.append(tuple(dims[c] for c in keep))
    return big

def _slice_pm(pm, t, lo, hi):
    return [({l: A[lo:hi] for l, A in pm[u].items()} if u == t else pm[u]) for u in range(3)]

def flattening_matrix_fast(lam, fillings, vecs, gs, memcap=MEMCAP, optimize='auto-hq', pre=None, return_info=False):
    """drop-in for hwv.flattening_matrix (lam is unused except for documentation; fillings carry the shapes).
    If the largest intermediate of the chosen path exceeds `memcap` elements (opt_einsum's memory_limit is only a
    hint), the row batch or the column batch is halved and the halves are computed recursively."""
    vm, pm = pre if pre is not None else prepare(vecs, gs)
    ops, out = build_network(fillings, vm, pm)
    path, info = find_path(ops, out, memcap, optimize)
    N1 = next(iter(pm[0].values())).shape[0]; K = next(iter(pm[1].values())).shape[0]
    if largest_intermediate(ops, out, path) > memcap and max(N1, K) > 1:
        if N1 >= K:
            h = N1 // 2
            F = np.vstack([flattening_matrix_fast(lam, fillings, vecs, gs, memcap, optimize, (vm, _slice_pm(pm, 0, 0, h))),
                           flattening_matrix_fast(lam, fillings, vecs, gs, memcap, optimize, (vm, _slice_pm(pm, 0, h, N1)))])
        else:
            h = K // 2
            pmA = _slice_pm(_slice_pm(pm, 1, 0, h), 2, 0, h); pmB = _slice_pm(_slice_pm(pm, 1, h, K), 2, h, K)
            F = np.hstack([flattening_matrix_fast(lam, fillings, vecs, gs, memcap, optimize, (vm, pmA)),
                           flattening_matrix_fast(lam, fillings, vecs, gs, memcap, optimize, (vm, pmB))])
        return (F, info) if return_info else F
    F = execute(ops, out, path).astype(np.int64)
    return (F, info) if return_info else F

def path_cost(fillings, shapes_vm, shapes_pm, memcap=MEMCAP, optimize='greedy'):
    """estimated (flops, largest intermediate) for a filling without computing anything (dummy arrays of the shapes)."""
    ops, out = build_network(fillings, shapes_vm, shapes_pm)
    path, info = find_path(ops, out, memcap, optimize)
    return int(info.opt_cost), int(info.largest_intermediate), path
