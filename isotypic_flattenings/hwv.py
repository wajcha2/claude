"""Fast isotypic-flattening ranks via highest-weight-vector evaluation (HIL style), exact mod p.
Tensor given as rank-one decomposition A,B,C of shape (r,n). Flattening S^{l1}V^* -> S^{l2}V (x) S^{l3}V
is evaluated in spanning sets g.v_{l1} and g'.v_{l2} (x) g''.v_{l3}: entry = sum over words s in [r]^d
of products of column determinants (columns of the three tableau fillings)."""
import numpy as np, itertools, os
from itertools import permutations
from isoflat import partitions, kronecker, perm_sign
p = 524287
import isoflat; isoflat.p = p
try:
    import opt_einsum as oe          # contraction-path optimiser (pip install opt_einsum); optional
except ImportError:
    oe = None
PATHOPT = os.environ.get('PATHOPT', 'dp' if oe is not None else 'greedy')   # 'dp' = optimal path (smallest largest intermediate), 'greedy' = original heuristic
MEMCAP = int(os.environ.get('MEMCAP', '40000000'))   # largest intermediate allowed (int64 elements, 4e7 = 0.32 GB); above it the batch is split

def dim_schur(lam, n):
    num = den = 1
    for i, r in enumerate(lam):
        for j in range(r):
            num *= (n + j - i)
            den *= (r - j - 1) + sum(1 for k in range(i + 1, len(lam)) if lam[k] > j) + 1
    return num // den

def canonical_columns(lam):
    rows, c = [], 0
    for r in lam:
        rows.append(list(range(c, c + r))); c += r
    return [[row[j] for row in rows if j < len(row)] for j in range(lam[0])]

def relabel(cols, sigma):
    return [[sigma[b] for b in col] for col in cols]

def col_dets(V, ell):
    """V: (B, r, n) mod p.  returns D[b, s_1..s_ell] = det [V[b, s_i, j]]_{i,j<ell}."""
    B, r, n = V.shape
    out = np.zeros((B,) + (r,) * ell, dtype=np.int64)
    for pi in permutations(range(ell)):
        term = np.ones((B,) + (1,) * ell, dtype=np.int64)
        for i in range(ell):
            shape = [B] + [1] * ell; shape[1 + i] = r
            term = (term * V[:, :, pi[i]].reshape(shape)) % p
        out = (out + perm_sign(pi) * term) % p
    return out

def pair_contract(ia, A, ib, B, keep):
    """modular contraction of A (indices ia) with B (ib), keeping indices in `keep` (order: as in keep)."""
    # sum out indices private to one operand that are not kept
    for idx in list(ia):
        if idx not in ib and idx not in keep:
            A = A.sum(axis=ia.index(idx)) % p; ia = ia.replace(idx, '')
    for idx in list(ib):
        if idx not in ia and idx not in keep:
            B = B.sum(axis=ib.index(idx)) % p; ib = ib.replace(idx, '')
    batch = [i for i in ia if i in ib and i in keep]
    contr = [i for i in ia if i in ib and i not in keep]
    fa = [i for i in ia if i not in ib]; fb = [i for i in ib if i not in ia]
    dims = dict(zip(ia, A.shape)); dims.update(zip(ib, B.shape))
    A = np.transpose(A, [ia.index(i) for i in batch + fa + contr])
    B = np.transpose(B, [ib.index(i) for i in batch + contr + fb])
    nb = int(np.prod([dims[i] for i in batch])) if batch else 1
    na = int(np.prod([dims[i] for i in fa])) if fa else 1
    nc = int(np.prod([dims[i] for i in contr])) if contr else 1
    nbb = int(np.prod([dims[i] for i in fb])) if fb else 1
    R = np.matmul(A.reshape(nb, na, nc), B.reshape(nb, nc, nbb)) % p
    res_idx = ''.join(batch + fa + fb)
    R = R.reshape([dims[i] for i in res_idx] or [1]) if res_idx else R.reshape(())
    # reorder to `keep` order
    order = [res_idx.index(i) for i in keep]
    return np.transpose(R, order) if res_idx else R

def _prod(xs):
    q = 1
    for x in xs: q *= int(x)
    return q

def _keep(ops_idx, x, y, out):
    ia, ib = ops_idx[x], ops_idx[y]
    others = set(''.join(i for k, i in enumerate(ops_idx) if k not in (x, y))) | set(out)
    return ''.join(dict.fromkeys(i for i in ia + ib if i in others))

def greedy_path(idx, shapes, out):
    """the original heuristic of contract(): pairwise, smallest result first (then most shared indices, then cost)."""
    idx, shapes, path = list(idx), list(shapes), []
    while len(idx) > 1:
        best = None
        for x in range(len(idx)):
            for y in range(x + 1, len(idx)):
                ia, ib = idx[x], idx[y]
                keep = _keep(idx, x, y, out)
                dims = dict(zip(ia, shapes[x])); dims.update(zip(ib, shapes[y]))
                key = (_prod(dims[i] for i in keep), -len(set(ia) & set(ib)), _prod(dims[i] for i in dict.fromkeys(ia + ib)))
                if best is None or key < best[0]:
                    best = (key, x, y, keep, dims)
        _, x, y, keep, dims = best
        path.append((x, y))
        idx = [i for k, i in enumerate(idx) if k not in (x, y)] + [keep]
        shapes = [s for k, s in enumerate(shapes) if k not in (x, y)] + [tuple(dims[i] for i in keep)]
    return path

def find_path(idx, shapes, out):
    """pairwise contraction path (opt_einsum convention: contract positions (x,y) of the current list, append result)."""
    if PATHOPT == 'dp' and oe is not None and len(idx) > 1:
        path, _ = oe.contract_path(','.join(idx) + '->' + out, *shapes, shapes=True, optimize=oe.DynamicProgramming(minimize='size'))
        path = [tuple(sorted(pr)) for pr in path]
        if all(len(pr) == 2 for pr in path):
            return path
    return greedy_path(idx, shapes, out)

def largest_intermediate(idx, shapes, out, path):
    """(size in elements, index string) of the largest intermediate produced along `path`."""
    idx, shapes, big = list(idx), list(shapes), (0, '')
    for x, y in path:
        keep = _keep(idx, x, y, out)
        dims = dict(zip(idx[x], shapes[x])); dims.update(zip(idx[y], shapes[y]))
        shape = tuple(dims[i] for i in keep)
        big = max(big, (_prod(shape), keep))
        idx = [i for k, i in enumerate(idx) if k not in (x, y)] + [keep]
        shapes = [s for k, s in enumerate(shapes) if k not in (x, y)] + [shape]
    return big

def contract(ops, out, path=None):
    """ops: list of (indices, array). Returns array with indices `out`, mod p, contracting pairwise along `path`
    (default: find_path = optimal path by largest-intermediate size, or the original greedy order)."""
    ops = list(ops)
    if path is None:
        path = find_path([i for i, _ in ops], [A.shape for _, A in ops], out)
    for x, y in path:
        keep = _keep([i for i, _ in ops], x, y, out)
        (ia, A), (ib, B) = ops[x], ops[y]
        ops = [o for k, o in enumerate(ops) if k not in (x, y)]
        ops.append((keep, pair_contract(ia, A, ib, B, keep)))
    i, A = ops[0]
    for idx in list(i):
        if idx not in out:
            A = A.sum(axis=i.index(idx)) % p; i = i.replace(idx, '')
    return np.transpose(A, [i.index(x) for x in out])

LET = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ'

def operand_specs(fillings, N1, K, r):
    idx, shapes = [], []
    for t in range(3):
        B = N1 if t == 0 else K; batch = LET[50] if t == 0 else LET[51]
        for col in fillings[t]:
            idx.append(batch + ''.join(LET[b] for b in col)); shapes.append((B,) + (r,) * len(col))
    return idx, shapes

def flattening_matrix(lam, fillings, vecs, gs):
    """lam=(l1,l2,l3); fillings = 3 column lists (boxes 0..d-1); vecs=(A,B,C) each (r,n) mod p;
    gs = (G1 (N1,n,n), G2 (K,n,n), G3 (K,n,n)).  Returns F (N1,K): flattening S^{l1}V^* -> S^{l2}V (x) S^{l3}V.
    The contraction path is chosen first from the shapes alone; if its largest intermediate exceeds MEMCAP elements,
    the row batch (Y) or the column batch (Z) is halved and the two halves are computed recursively."""
    out = LET[50] + LET[51]
    N1, K, r = gs[0].shape[0], gs[1].shape[0], vecs[0].shape[0]
    idx, shapes = operand_specs(fillings, N1, K, r)
    path = find_path(idx, shapes, out)
    big, which = largest_intermediate(idx, shapes, out, path)
    if big > MEMCAP:
        split_Y = LET[50] in which and N1 > 1 and (LET[51] not in which or K == 1 or N1 >= K)
        if split_Y:
            h = N1 // 2
            return np.vstack([flattening_matrix(lam, fillings, vecs, (gs[0][:h], gs[1], gs[2])),
                              flattening_matrix(lam, fillings, vecs, (gs[0][h:], gs[1], gs[2]))])
        if LET[51] in which and K > 1:
            h = K // 2
            return np.hstack([flattening_matrix(lam, fillings, vecs, (gs[0], gs[1][:h], gs[2][:h])),
                              flattening_matrix(lam, fillings, vecs, (gs[0], gs[1][h:], gs[2][h:]))])
    ops = []
    for t in range(3):
        G = gs[t]; V = vecs[t]
        W = np.einsum('bji,sj->bsi', G, V) % p            # (B, r, n): g^T v_s
        batch = LET[50] if t == 0 else LET[51]             # 'Y' rows, 'Z' columns
        for col in fillings[t]:
            D = col_dets(W, len(col))
            ops.append((batch + ''.join(LET[b] for b in col), D))
    return contract(ops, out, path)

def random_gs(rng, n, N1, K):
    return (rng.integers(0, p, (N1, n, n)), rng.integers(0, p, (K, n, n)), rng.integers(0, p, (K, n, n)))

def random_fillings(rng, lam):
    d = sum(lam[0]); cols = [canonical_columns(l) for l in lam]
    return [cols[0]] + [relabel(cols[t], list(rng.permutation(d))) for t in (1, 2)]
