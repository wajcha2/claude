"""shared helpers for the C^4x5x5 sweep tools: cached component enumeration (Kronecker coefficients at d=9 take minutes)."""
import itertools, os, pickle, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hwv import dim_schur
from isoflat import partitions, kronecker
ns = (4, 5, 5)
_CACHE = os.path.join(os.path.dirname(os.path.abspath(__file__)), '.comps455_cache.pkl')
def components(d):
    """[(lam, g)] for lam = (l1; {l2,l3}) with g = Kronecker coefficient > 0, in the enumeration order of sweep_fast."""
    cache = pickle.load(open(_CACHE, 'rb')) if os.path.exists(_CACHE) else {}
    if d not in cache:
        cache[d] = [((l1, l2, l3), kronecker(l1, l2, l3)) for l1 in partitions(d, ns[0])
                    for l2, l3 in itertools.combinations_with_replacement(partitions(d, ns[1]), 2)]
        cache[d] = [(lam, g) for lam, g in cache[d] if g]
        pickle.dump(cache, open(_CACHE, 'wb'))
    return cache[d]
def dims_of(lam): return tuple(dim_schur(l, ns[t]) for t, l in enumerate(lam))
def cost(lam, g): return g * sum((x + 4) ** 2 for x in dims_of(lam))
