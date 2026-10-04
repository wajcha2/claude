"""python3 m2classify2.py log [log ...]   -- verdicts for m2cmp2.py output (one line per component and direction).
 NOSEP  K(R6) = K(R7) or K'(R6) = K'(R7) (same subspaces): the rank-6 and rank-7 tensor have the same rank at every U,
        so no U separates and none can give rank(M2) > rank(R6) (rank(M2) <= rank of a general tensor).
 EXCL   K(R6) <= K(M2) or K'(R6) <= K'(M2) (containment test, valid sample sizes): rank_U(M2) <= rank_U(R6) for every U, type.
 DROP   not EXCL, but rho6 := rank of F_phi(R6) at generic phi >= m := max over all U and types of rank_U(M2)
        (= max(generic phi, H_g, V_g) on M2).  A U with rank_U(M2) > rank_U(R6) must then lie inside the common rank-6
        drop locus D6 = {phi : rank F_phi(T) < rho6 for all rank-6 T}, since H(U), V(U) >= rank F_phi for phi in U.
        For g = 2 D6 is finite and m2lines.py decides it completely.
 OPEN   neither (or a needed V_g was not computed): needs a stack-level analysis.
Flags SEP (rank 6 < rank 7 for a generic U of some type/dim) and WIN (rank M2 > rank 6) are listed separately."""
import sys, re
from collections import Counter

def parse(line):
    m = re.match(r'lam=(.*?) dir(\d) g=(\d+) n1=(\d+) n23=(\d+) N1=(\d+) K=(\d+) span\((.*?)\)=([\d,]+) \| (.*?) \| (.*?) \| (.*?) \(eval', line)
    if not m: return None
    lam, dirn, g, n1, n23, N1, K, tn, span, body, inc, flags = m.groups()
    vals = {}
    for tok in body.split():
        mm = re.match(r'([gHV])(\d+):(\d+),(\d+)/(\d+)/M2=(\d+)', tok)
        t, k, a, b, r7, m2 = mm.groups()
        vals[(t, int(k))] = (min(int(a), int(b)), int(r7), int(m2))
    return dict(lam=lam, dirn=int(dirn), g=int(g), n1=int(n1), n23=int(n23), K=int(K), vals=vals, inc=inc, flags=flags,
                span=dict(zip(tn.split(','), span.split(','))))

def verdict(r):
    g, v = r['g'], r['vals']
    if 'EXCL' in r['inc'] and '?' not in r['inc']: return 'EXCL'
    if 'NOSEP' in r['inc'] and '?' not in r['inc']: return 'NOSEP'
    rho6 = v[('g', 1)][0]
    if ('V', g) not in v and g > 1: return 'OPEN'
    m = max(x[2] for (t, k), x in v.items() if (t, k) in (('g', 1), ('H', g), ('V', g)))
    return 'DROP' if rho6 >= m else 'OPEN'

if __name__ == '__main__':
    rows = []
    for fn in sys.argv[1:]:
        for line in open(fn):
            if 'ERROR' in line and line.startswith('lam='): print('ERROR:', line.strip()[:200])
            elif line.startswith('lam='):
                r = parse(line)
                if r: rows.append(r)
                else: print('unparsed:', line[:150])
    cnt = Counter()
    for r in rows: r['v'] = verdict(r); cnt[r['v']] += 1
    print('%d (component, direction) pairs: %s' % (len(rows), dict(sorted(cnt.items()))))
    for flag in ('WIN', 'SEP'):
        fl = [r for r in rows if flag in r['flags'].split()]
        print('%s: %d' % (flag, len(fl)))
        for r in fl:
            print('   %s dir%d g=%d n1=%d n23=%d [%s] %s' % (r['lam'], r['dirn'], r['g'], r['n1'], r['n23'], r['v'],
                  ' '.join('%s%d=%d/%d/M2=%d' % (t, k, *x) for (t, k), x in sorted(r['vals'].items()) if x[0] < x[1] or x[2] > x[0])))
    for vv in ('DROP', 'OPEN'):
        print('%s cases:' % vv)
        for r in rows:
            if r['v'] == vv:
                v = r['vals']; g = r['g']
                key = [('g', 1), ('H', g), ('V', g)]
                print('   %s dir%d g=%d n1=%d n23=%d K=%d %s | %s' % (r['lam'], r['dirn'], r['g'], r['n1'], r['n23'], r['K'], r['inc'],
                      ' '.join('%s%d=%d/%d/M2=%d' % (t, k, *v[(t, k)]) for t, k in key if (t, k) in v)))
