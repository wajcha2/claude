"""a_exclude.py -- family-A members known to be saturated, from family-B logs (for comb_search.py --a-exclude).

A family-B summary line 'famB mn=MU|NU ... singles: LAM:[1/g:]d_r1/d_r2 ...' gives the level-1 rank of the flattening of
the component (LAM, MU, NU) on the rank-r1 and rank-r2 tensors (the same tensors, sample points and fillings as family A
with the same seed and dir: the cached flattenings are shared).  The rank of a matrix does not depend on the side it is
viewed from, so when d_r1 = n1(LAM) = dim S_LAM C^n the member (MU, NU) of the family-A lattice of LAM (aux 1) is
saturated on rank r1 (both families use one generic functional at level 1).  comb_search.search() drops such members;
leaving them out beforehand saves computing their flattenings.

usage: python3 a_exclude.py N_SOURCE OUT.json LOG [LOG ...]"""
import sys, re, json, glob
from fractions import Fraction


def dim_schur(lam, n):
    """dim S_lam C^n (hook content formula)."""
    conj = [sum(1 for x in lam if x > j) for j in range(lam[0])]
    r = Fraction(1)
    for i, li in enumerate(lam):
        for j in range(li):
            r *= Fraction(n + j - i, (li - j - 1) + (conj[j] - i - 1) + 1)
    return int(r)


n, out, logs = int(sys.argv[1]), sys.argv[2], [f for a in sys.argv[3:] for f in sorted(glob.glob(a))]
excl, seen, kept = {}, set(), {}
for f in logs:
    for l in open(f):
        m = re.match(r'famB mn=(\S+) members=\d+ .*?singles: (.*?)  named', l)
        if not m or m.group(1) in seen:
            continue
        seen.add(m.group(1))
        toks, i = m.group(2).split(), 0
        while i < len(toks):
            a = toks[i].split(':')
            lam = a[0]
            if len(a) == 3:                       # 'LAM:1/g:d/d' (level 1 of g > 1), followed by the level-g token
                d1, i = int(a[2].split('/')[0]), i + 2
            else:                                 # 'LAM:d/d' (g = 1)
                d1, i = int(a[1].split('/')[0]), i + 1
            if d1 >= dim_schur(tuple(int(c) for c in lam), n):
                excl.setdefault(lam, []).append(m.group(1))
            else:
                kept.setdefault(lam, []).append(m.group(1))
json.dump({k: sorted(v) for k, v in excl.items()}, open(out, 'w'), indent=0)
print('%d targets from %d logs; saturated / not saturated per source: %s' % (
    len(seen), len(logs), ', '.join('%s %d/%d' % (k, len(excl.get(k, [])), len(kept.get(k, []))) for k in sorted(set(excl) | set(kept)))))
