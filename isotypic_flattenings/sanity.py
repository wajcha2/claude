from isoflat import *
rng = np.random.default_rng(0)
# rank-1 tensor: every isotypic flattening has rank <= 1 (and is 0 unless all lam_i = (d))
T1 = rank_r_tensor(rng, 1)
for d in (2, 3, 4):
    X = tensor_power(T1, d)
    for lam in itertools.combinations_with_replacement(partitions(d, 3), 3):
        if kronecker(*lam) == 0: continue
        pairs = [(tuple(rng.permutation(d)), tuple(rng.permutation(d))) for _ in range(3)]
        Ys = isotypic_tensors(X, d, lam, pairs)
        print("rank1 d=%d lam=%s max flattening ranks=%s" % (d, lam, [max(modrank(F) for F in flattenings(Y).values()) for Y in Ys]))
# rank-2 tensor, lam = ((d),(d),(d)): flattening rank = d+1 (number of monomials in 2 vars)
T2 = rank_r_tensor(rng, 2)
for d in (2, 3, 4):
    X = tensor_power(T2, d)
    Ys = isotypic_tensors(X, d, ((d,),) * 3, [(tuple(range(d)), tuple(range(d)))])
    print("rank2 d=%d symmetric flattening ranks=%s (expect %d)" % (d, [modrank(F) for F in flattenings(Ys[0]).values()], d + 1))
# span dimension equals Kronecker coefficient for a general tensor
Tg = general_tensor(rng)
for d in (3, 4):
    X = tensor_power(Tg, d)
    for lam in itertools.combinations_with_replacement(partitions(d, 3), 3):
        g = kronecker(*lam)
        pairs = [(tuple(rng.permutation(d)), tuple(rng.permutation(d))) for _ in range(6)]
        Ys = isotypic_tensors(X, d, lam, pairs)
        print("general d=%d lam=%s span=%d kronecker=%d" % (d, lam, span_dim(Ys), g))
