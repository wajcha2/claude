"""Koszul flattenings of the STACKED isotypic tensor (full multiplicity space U = M_lambda, g >= 2).
The isotypic tensor with U = M_lambda is a 4-tensor in U^* (x) S^{l1} (x) S^{l2} (x) S^{l3}.  Grouping U^* with one
factor gives three 3-tensors; we take all their Koszul flattenings  Lambda^p A' (x) B^* -> Lambda^{p+1} A' (x) C:
  W  : the wedged factor is the stacked one (U^* (x) S^{ls});
  V/H: the wedged factor is a plain one; U^* sits on the source (V: rows stacked) or target (H: columns stacked).
The generic 1-dim U case is koszul.py / koszul_fast.py.  Exact mod p = 524287; rank drop on two independent
rank-r_low samples but not on a rank-r_high sample = separation.
usage: python3 koszul_stack.py n d r_low,r_high maxprod      env: KBUDGET, RESUME (colon-separated logs)"""
import numpy as np, sys, time, itertools, os
import hwv, hwv_fast
hwv.flattening_matrix = hwv_fast.flattening_matrix_fast
from hwv import *
from isoflat import modrank
from specialU import probe3
from koszul import iso_tensor, koszul_dim
from math import comb

def koszul_matrix(Y, factor, pk, rng, swap=False, M=None):
    """(m, K, M): Koszul matrix of the 3-way array Y with `factor` wedged (projected to m dims by M when needed)."""
    Y = np.moveaxis(Y, factor, 0)
    if swap: Y = np.swapaxes(Y, 1, 2)
    nA, nB, nC = Y.shape
    m = koszul_dim(nA, nB, nC, pk)
    if m >= nA: Z = Y % p; m = nA; M = None
    else:
        if M is None: M = rng.integers(0, p, (m, nA))
        Z = np.tensordot(M, Y, axes=([1], [0])) % p
    rows = list(itertools.combinations(range(m), pk)); cols = list(itertools.combinations(range(m), pk + 1))
    K = np.zeros((len(rows) * nB, len(cols) * nC), dtype=np.int64)
    for i, I in enumerate(rows):
        for j, J in enumerate(cols):
            extra = set(J) - set(I)
            if len(extra) != 1: continue
            k = extra.pop(); sign = (-1) ** sorted(J).index(k)
            K[i * nB:(i + 1) * nB, j * nC:(j + 1) * nC] = (sign * Z[k]) % p
    return m, K, M

def analyse(lam, n, r_low, r_high, rng, pks=(1, 2), extra=2):
    g = kronecker(*lam); dims = tuple(dim_schur(l, n) for l in lam)
    G = tuple(rng.integers(0, p, (8, n, n)) for _ in range(3))
    def rvecs(r): return tuple(rng.integers(0, p, (r, n)) for _ in range(3))
    tens = {'low': rvecs(r_low), 'low2': rvecs(r_low), 'high': rvecs(r_high)}
    fills, probes, tries = [], [], 0
    while len(fills) < g and tries < 100 * g:
        f = random_fillings(rng, lam); tries += 1
        P = probe3(lam, f, tens['high'], G)
        if np.any(P) and modrank(np.array([q.ravel() for q in probes] + [P.ravel()])) == len(fills) + 1:
            fills.append(f); probes.append(P)
    assert len(fills) == g
    gsA, gsB, gsC = (rng.integers(0, p, (dims[i] + extra, n, n)) for i in range(3))
    res = {}
    Ms = {}
    for k, v in tens.items():
        Y4 = np.stack([iso_tensor(lam, [f], [1], v, gsA, gsB, gsC) for f in fills])   # (g, nA, nB, nC)
        out = {}
        # W: wedge the stacked factor
        for s in range(3):
            Z = np.moveaxis(Y4, s + 1, 1); Z = Z.reshape(g * Z.shape[1], Z.shape[2], Z.shape[3])
            for sw in (0, 1):
                for pk in pks:
                    key = ('W', s, sw, pk)
                    m, K, M = koszul_matrix(Z, 0, pk, rng, swap=bool(sw), M=Ms.get(key))
                    Ms[key] = M; out[key] = (m, K.shape, modrank(K))
        # V/H: wedge a plain factor f; stack the g Koszul matrices by rows (U on source) or columns (U on target)
        for f in range(3):
            for sw in (0, 1):
                for pk in pks:
                    key = ('K', f, sw, pk)
                    Ks = []
                    for j in range(g):
                        m, K, M = koszul_matrix(Y4[j], f, pk, rng, swap=bool(sw), M=Ms.get(key))
                        Ms[key] = M; Ks.append(K)
                    out[('V', f, sw, pk)] = (m, (g * K.shape[0], K.shape[1]), modrank(np.vstack(Ks)))
                    out[('H', f, sw, pk)] = (m, (K.shape[0], g * K.shape[1]), modrank(np.hstack(Ks)))
        res[k] = out
    sep = [key for key in res['high'] if res['low'][key][2] < res['high'][key][2] and res['low2'][key][2] < res['high'][key][2]]
    fmt = lambda r: {k: v[2] for k, v in r.items()}
    return "lam=%s g=%d dims=%s | stack-koszul (kind,factor,swap,p): low=%s low2=%s high=%s | m,shape=%s%s" % (
        lam, g, dims, fmt(res['low']), fmt(res['low2']), fmt(res['high']), {k: v[:2] for k, v in res['high'].items()},
        "  *** STACK-KOSZUL SEPARATES %s" % sep if sep else "")

if __name__ == "__main__":
    n = int(sys.argv[1]); d = int(sys.argv[2]); rl, rh = [int(x) for x in sys.argv[3].split(',')]
    maxprod = float(sys.argv[4]) if len(sys.argv) > 4 else 3e6
    rng = np.random.default_rng(71)
    DONE = set()
    for lf in os.environ.get('RESUME', '').split(':'):
        if lf and os.path.exists(lf):
            DONE |= {l.split(' g=')[0] for l in open(lf) if l.startswith('lam=') and 'SKIPPED' not in l}
    for lam in itertools.combinations_with_replacement(partitions(d, n), 3):
        g = kronecker(*lam)
        if g < 2: continue
        if ('lam=%s' % (lam,)) in DONE: continue
        dims = tuple(dim_schur(l, n) for l in lam)
        if g * np.prod([x + 2 for x in dims]) > maxprod:
            print("lam=%s g=%d dims=%s SKIPPED (size)" % (lam, g, dims)); sys.stdout.flush(); continue
        t0 = time.time()
        try: line = analyse(lam, n, rl, rh, rng, pks=(1, 2))
        except Exception as ex: line = "lam=%s g=%d ERROR %r" % (lam, g, ex)
        print(line + " (%.0fs)" % (time.time() - t0)); sys.stdout.flush()
