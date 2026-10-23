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
from isoflat import perm_sign

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

def pair_contract_ref(ia, A, ib, B, keep):
    """contract A (index string ia) with B (ib); result has index string `keep` (sub-multiset of ia+ib).
    A, B float64 with integer entries in [0, p); result likewise.  Reference version (before 2026-10-23): both
    operands transposed to (batch, free, contracted) copies and one batched np.matmul."""
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

_LETTERS = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ'

def pair_contract_fast(ia, A, ib, B, keep):
    """same result as pair_contract_ref (bit for bit: every entry is the exact integer sum of < 2^15 products < p^2,
    so any summation order gives the same float64, then fmod), faster (2026-10-23, measured 2-3x on the C^5 d = 14
    block loops):
     * numpy's batched np.matmul (batch > 1) does not reach BLAS speed (1.9 s vs 0.14 s for 3 x (4908x9 @ 9x3125));
       the batch is now a Python loop of 2-D np.dot calls into a preallocated result;
     * an operand already laid out as (batch, free, contracted) or (batch, contracted, free) is passed as a (transposed)
       view instead of being copied; the contracted order follows the larger operand, so only the smaller one is copied;
     * products without a summed index are one broadcast np.multiply into the output layout;
     * when a rough time model (BLAS loop: per-batch call overhead + transposed copies + fast MACs; einsum: slow MACs,
       no copies) prefers it, np.einsum works directly on the operands' layouts: the old code transposed a
       (4908, ...) operand of 47M elements to move the batch index first (2.8 s of a 7 s block) for a sum of 5 terms."""
    for idx in list(ia):
        if idx not in ib and idx not in keep:
            A = _fmod(A.sum(axis=ia.index(idx))); ia = ia.replace(idx, '')
    for idx in list(ib):
        if idx not in ia and idx not in keep:
            B = _fmod(B.sum(axis=ib.index(idx))); ib = ib.replace(idx, '')
    dims = dict(zip(ia, A.shape)); dims.update(zip(ib, B.shape))
    batch = [i for i in ia if i in ib and i in keep]
    contr = [i for i in ia if i in ib and i not in keep]
    fa = [i for i in ia if i not in ib]; fb = [i for i in ib if i not in ia]
    size = lambda idx: int(np.prod([dims[i] for i in idx])) if idx else 1
    nb, na, nc, nbb = size(batch), size(fa), size(contr), size(fb)
    if not contr:
        # no summation (outer / Hadamard product over the batch): broadcast multiply straight into the output layout
        def view(idx, X):
            Xt = np.transpose(X, [idx.index(i) for i in keep if i in idx])
            return np.expand_dims(Xt, tuple(k for k, i in enumerate(keep) if i not in idx))
        R = np.empty([dims[i] for i in keep])
        np.multiply(view(ia, A), view(ib, B), out=R)
        return _fmod(R)
    contr = [i for i in (ia if A.size >= B.size else ib) if i in contr]
    def layout(idx, free):
        """0: idx is batch+free+contr, 1: batch+contr+free (both usable as views), None: needs a copy"""
        n = list(range(len(idx)))
        if [idx.index(i) for i in batch + free + contr] == n: return 0
        if [idx.index(i) for i in batch + contr + free] == n: return 1
        return None
    la, lb = layout(ia, fa), layout(ib, fb)
    macs = float(nb) * na * nc * nbb
    t_blas = nb * 4e-6 + ((A.size if la is None else 0) + (B.size if lb is None else 0)) / 1e8 + macs / 4e9
    t_einsum = macs / 4e8
    allidx = list(dict.fromkeys(ia + ib))
    if t_einsum < t_blas and nc <= NCMAX and len(allidx) <= len(_LETTERS):
        # small contraction, many batches or a layout that would need a large transposed copy: sum of products
        # straight from the operands' layouts
        m = {c: _LETTERS[k] for k, c in enumerate(allidx)}
        eq = ''.join(m[c] for c in ia) + ',' + ''.join(m[c] for c in ib) + '->' + ''.join(m[c] for c in keep)
        return _fmod(np.einsum(eq, A, B))
    def as3(idx, X, free, lay):
        """X as an (nb, n_free, n_contr) array, a view (possibly transposed) when the layout allows"""
        nf, ncc = size(free), size(contr)
        if lay == 0:
            return X.reshape(nb, nf, ncc)
        if lay == 1:
            return np.swapaxes(X.reshape(nb, ncc, nf), 1, 2)
        return np.ascontiguousarray(np.transpose(X, [idx.index(i) for i in batch + free + contr])).reshape(nb, nf, ncc)
    A3 = as3(ia, A, fa, la)                              # (nb, na, nc)
    B3 = np.swapaxes(as3(ib, B, fb, lb), 1, 2)           # (nb, nc, nbb)
    R = np.empty((nb, na, nbb))
    if nc <= NCMAX:
        for i in range(nb):
            np.dot(A3[i], B3[i], out=R[i])           # np.dot, not np.matmul: matmul with out= and a transposed operand
        _fmod(R)                                     # leaves BLAS (1.3 s vs 0.16 s for 176 x (50x1000 @ 1000x100))
    else:
        for i in range(nb):
            acc = None
            for c0 in range(0, nc, NCMAX):
                C = _fmod(np.matmul(A3[i][:, c0:c0 + NCMAX], B3[i][c0:c0 + NCMAX]))
                acc = C if acc is None else _fmod(acc + C)
            R[i] = acc
    del A3, B3
    res_idx = ''.join(batch + fa + fb)
    R = R.reshape([dims[i] for i in res_idx])
    return np.transpose(R, [res_idx.index(i) for i in keep])

import os as _os
pair_contract = pair_contract_ref if _os.environ.get('HWV_PC', 'fast') == 'ref' else pair_contract_fast

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
            del A, B                                     # free the operands before the next contraction
        ia, A = taken[0]
        keep = ''.join(dict.fromkeys(i for i in ia if i in rest))
        if keep != ia:
            A = single_reduce(ia, A, keep); ia = keep
        ops.append((ia, A))
    assert len(ops) == 1
    ia, A = ops[0]
    return single_reduce(ia, A, out)

_minor_cache = {}
def minors_of_points_ref(G, ell):
    """P[b, I] = det G[b][I, :ell] for I in combinations(range(n), ell)  (G: (B, n, n)).  Reference: col_dets builds
    all n^ell ordered row tuples over all ell! permutations (2 min for B = 4716 points of 5x5 at ell = 5)."""
    n = G.shape[1]
    D = col_dets(np.ascontiguousarray(G[:, :, :ell]), ell)           # (B, n, ..., n): rows i_1..i_ell
    subs = list(combinations(range(n), ell))
    return (np.stack([D[(slice(None),) + I] for I in subs], axis=1) % p).astype(np.float64)

def minors_of_points(G, ell):
    """P[b, I] = det G[b][I, :ell] for I in combinations(range(n), ell)  (G: (B, n, n)); same values as
    minors_of_points_ref (2026-10-22, degree-9 combined agent), but only the C(n, ell) row subsets, each by the
    Leibniz expansion over ell! permutations, products reduced mod p after every factor (int64 exact)."""
    n = G.shape[1]
    Gm = np.asarray(G[:, :, :ell], dtype=np.int64) % p
    perms = [(pi, perm_sign(pi)) for pi in itertools.permutations(range(ell))]
    subs = list(combinations(range(n), ell))
    out = np.zeros((G.shape[0], len(subs)), dtype=np.int64)
    for k, I in enumerate(subs):
        acc = np.zeros(G.shape[0], dtype=np.int64)
        for pi, sg in perms:
            term = Gm[:, I[0], pi[0]]
            for i in range(1, ell):
                term = (term * Gm[:, I[i], pi[i]]) % p
            acc = (acc + sg * term) % p
        out[:, k] = acc
    return out.astype(np.float64)

_vminor_cache = {}
def minors_of_vectors(V, ell):
    """M[I, s_1..s_ell] = det V[s_*, I]  (V: (r, n)).  Memoized on (V, ell) (2026-10-23): a sweep calls prepare() for
    every direction, rank and probe with the same few tensors (3 s of a 31 s C^5 d = 13 component); the returned array
    is shared, which is safe because nothing writes into the minors."""
    V = np.asarray(V)
    key = (V.shape, V.dtype.str, V.tobytes(), ell)
    hit = _vminor_cache.get(key)
    if hit is None:
        if len(_vminor_cache) > 256:
            _vminor_cache.clear()
        hit = _vminor_cache[key] = _minors_of_vectors(V, ell)
    return hit

def _minors_of_vectors(V, ell):
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
    # no memory_limit: with it opt_einsum returns multi-operand steps whose pairwise execution can be huge;
    # memory is enforced afterwards by largest_intermediate + batch splitting in flattening_matrix_fast
    path, info = oe.contract_path(eq, *shapes, shapes=True, optimize=optimize)
    return path, info

def largest_intermediate(ops, out, path):
    """largest number of elements of any intermediate that execute() will allocate along `path`
    (simulates execute exactly, including the pairwise expansion of multi-operand steps)."""
    ops = [(i, A.shape) for i, A in ops]; big = 0
    def sz(idx, dims): 
        r = 1
        for c in idx: r *= dims[c]
        return r
    for step in path:
        step = sorted(step, reverse=True)
        taken = [ops.pop(k) for k in step]
        rest = set(''.join(i for i, _ in ops)) | set(out)
        while len(taken) > 1:
            (ia, sa), (ib, sb) = taken.pop(), taken.pop()
            others = rest | set(''.join(i for i, _ in taken))
            keep = ''.join(dict.fromkeys(i for i in ia + ib if i in others))
            dims = dict(zip(ia, sa)); dims.update(zip(ib, sb))
            big = max(big, sz(keep, dims), sz(ia, dims), sz(ib, dims))
            taken.append((keep, tuple(dims[c] for c in keep)))
        ia, sa = taken[0]
        keep = ''.join(dict.fromkeys(i for i in ia if i in rest))
        ops.append((keep, tuple(dict(zip(ia, sa))[c] for c in keep)))
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
