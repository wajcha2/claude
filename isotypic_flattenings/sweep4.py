import sys, isoflat
isoflat.n = 4
from isoflat import *
d = int(sys.argv[1]); R = 6
rng = np.random.default_rng(777)
NINST = 2
t0 = time.time()
tens = {'gen': [general_tensor(rng) for _ in range(NINST)], 'rk6': [rank_r_tensor(rng, R) for _ in range(NINST)]}
Xs = {k: [tensor_power(T, d) for T in v] for k, v in tens.items()}
caches = {k: [dict() for _ in v] for k, v in tens.items()}
print("== C^4, d=%d, powers built %.1fs" % (d, time.time() - t0)); sys.stdout.flush()
found = []
for lam in itertools.combinations_with_replacement(partitions(d, 4), 3):
    g = kronecker(*lam)
    if g == 0: continue
    dims = tuple(dim_schur(l) for l in lam)
    pairs = [(tuple(rng.permutation(d)), tuple(rng.permutation(d))) for _ in range(min(4 * g + 4, factorial(d) ** 2))]
    coeffs = rng.integers(1, p, size=len(pairs))
    Ys = {k: [isotypic_tensors(Xs[k][i], d, lam, pairs, caches[k][i]) for i in range(NINST)] for k in Xs}
    def ranks_of(Yl, combo):
        Y = sum(int(c) * Yj for c, Yj in zip(combo, Yl)) % p
        F = flattenings(Y); return tuple(modrank(F[i]) for i in (1, 2, 3))
    res = {k: [ranks_of(Ys[k][i], coeffs) for i in range(NINST)] for k in Xs}
    line = "lam=%s dims=%s g=%d span=%s/%s gen=%s rk6=%s" % (lam, dims, g, [span_dim(Ys['gen'][i]) for i in range(NINST)], [span_dim(Ys['rk6'][i]) for i in range(NINST)], res['gen'], res['rk6'])
    sep = [i + 1 for i in range(3) if len({r[i] for r in res['gen']}) == 1 and len({r[i] for r in res['rk6']}) == 1 and res['rk6'][0][i] < res['gen'][0][i]]
    if g >= 2:
        st = {k: [stacked_flattenings(Ys[k][i]) for i in range(NINST)] for k in Xs}
        for key in st['gen'][0]:
            rg = [modrank(st['gen'][i][key]) for i in range(NINST)]; r6 = [modrank(st['rk6'][i][key]) for i in range(NINST)]
            line += " | st%s gen=%s rk6=%s" % (key, rg, r6)
            if len(set(rg)) == 1 and len(set(r6)) == 1 and r6[0] < rg[0]: sep.append(key)
    if sep: line += "  *** SEPARATES %s" % sep; found.append((lam, sep))
    print(line); sys.stdout.flush()
print("d=%d done %.1fs FOUND: %s" % (d, time.time() - t0, found))
