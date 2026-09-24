from isoflat import *
import sys
dmin = int(sys.argv[1]); dmax = int(sys.argv[2])
rng = np.random.default_rng(12345)
NINST = 2
found = []
for d in range(dmin, dmax + 1):
    t0 = time.time()
    tensors = {'gen': [general_tensor(rng) for _ in range(NINST)],
               'rk4': [rank_r_tensor(rng, 4) for _ in range(NINST)]}
    Xs = {k: [tensor_power(T, d) for T in v] for k, v in tensors.items()}
    caches = {k: [dict() for _ in v] for k, v in tensors.items()}
    parts = partitions(d, 3)
    print("==== d = %d  (tensor powers built in %.1fs) ====" % (d, time.time() - t0)); sys.stdout.flush()
    for lam in itertools.combinations_with_replacement(parts, 3):
        g = kronecker(*lam)
        if g == 0:
            continue
        dims = tuple(dim_schur(l) for l in lam)
        npairs = min(4 * g + 4, factorial(d) ** 2)
        allpairs = None
        if factorial(d) ** 2 <= 64:
            allpairs = [(s2, s3) for s2 in permutations(range(d)) for s3 in permutations(range(d))]
            pairs = allpairs
        else:
            pairs = [(tuple(rng.permutation(d)), tuple(rng.permutation(d))) for _ in range(npairs)]
        coeffs = rng.integers(1, p, size=len(pairs))
        Ys = {k: [isotypic_tensors(Xs[k][i], d, lam, pairs, caches[k][i]) for i in range(NINST)] for k in Xs}
        spans = {k: [span_dim(Ys[k][i]) for i in range(NINST)] for k in Xs}
        # generic functional
        def ranks_of(Ylist, combo):
            Y = sum(int(c) * Yj for c, Yj in zip(combo, Ylist)) % p
            F = flattenings(Y)
            return tuple(modrank(F[i]) for i in (1, 2, 3))
        res_generic = {k: [ranks_of(Ys[k][i], coeffs) for i in range(NINST)] for k in Xs}
        line = "d=%d lam=%s dims=%s g=%d span gen=%s rk4=%s | generic phi ranks gen=%s rk4=%s" % (
            d, lam, dims, g, spans['gen'], spans['rk4'], res_generic['gen'], res_generic['rk4'])
        sep = []
        for i in range(3):
            rg = set(r[i] for r in res_generic['gen']); r4 = set(r[i] for r in res_generic['rk4'])
            if len(rg) == 1 and len(r4) == 1 and max(r4) < max(rg):
                sep.append(("generic", i + 1, max(rg), max(r4)))
        if g >= 2:
            # individual natural functionals (Young symmetrizer pairs)
            for j, pr in enumerate(pairs):
                unit = [0] * len(pairs); unit[j] = 1
                rg = [ranks_of(Ys['gen'][i], unit) for i in range(NINST)]
                r4 = [ranks_of(Ys['rk4'][i], unit) for i in range(NINST)]
                line += "\n    pair %s: gen=%s rk4=%s" % (pr, rg, r4)
                for i in range(3):
                    sg = set(r[i] for r in rg); s4 = set(r[i] for r in r4)
                    if len(sg) == 1 and len(s4) == 1 and max(s4) < max(sg):
                        sep.append(("pair%d" % j, i + 1, max(sg), max(s4)))
            # stacked
            st = {k: [stacked_flattenings(Ys[k][i]) for i in range(NINST)] for k in Xs}
            for key in st['gen'][0]:
                rg = [modrank(st['gen'][i][key]) for i in range(NINST)]
                r4 = [modrank(st['rk4'][i][key]) for i in range(NINST)]
                line += "\n    stacked %s: gen=%s rk4=%s" % (key, rg, r4)
                if len(set(rg)) == 1 and len(set(r4)) == 1 and r4[0] < rg[0]:
                    sep.append(("stacked%s" % (key,), None, rg[0], r4[0]))
        if sep:
            line += "\n    *** SEPARATES: %s" % sep
            found.append((d, lam, sep))
        print(line); sys.stdout.flush()
    print("---- d=%d done in %.1fs" % (d, time.time() - t0))
print("FOUND:", found)
