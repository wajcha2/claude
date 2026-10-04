"""python3 m2classify.py log [log ...]   -- classify the (component, direction) results of m2cmp.py.
Let rho = rank of F_phi(R6) for generic phi (1-dim U).
 A (tall, excluded):  rho = n1 and the full V-stack M^* (x) S^{l1}V^* -> rest is injective on R6 (V_g = g n1).  Then for every
   U (1-dim, H- or V-stack) the rank-6 tensor has the maximal possible rank (F_phi x = 0 <=> phi (x) x in ker V_g), so no U
   gives rank(M2) > rank(R6).
 B (wide, excluded):  rho = n23 and the full H-stack S^{l1}V^* -> M (x) rest is surjective on R6 (H_g = g n23): the transposed
   statement.
 A? / B?: as A / B but the full stack was not computed (K or N1 cap) -- undecided.
 C: everything else (rank-6 flattening degenerate or the full stack not of maximal rank) -- needs a special-U analysis.
Also prints, per type, the M2 maxima over all U (1-dim: generic phi; H/V: U = M^*), which bound rank(M2) at every U."""
import sys, re
from collections import Counter, defaultdict

def parse(line):
    m = re.match(r'lam=(.*?) dir(\d) g=(\d+) n1=(\d+) n23=(\d+) N1=(\d+) K=(\d+) span\(.*?\)=([\d,]+) \| (.*?) \| (.*?) \(eval', line)
    if not m: return None
    lam, dirn, g, n1, n23, N1, K, span, body, flags = m.groups()
    g, n1, n23 = int(g), int(n1), int(n23)
    vals = {}
    for tok in body.split():
        mm = re.match(r'([gHV])(\d+):(\d+),(\d+)/(\d+)/M2=(\d+)', tok)
        t, k, a, b, r7, m2 = mm.groups()
        vals[(t, int(k))] = (max(int(a), int(b)), min(int(a), int(b)), int(r7), int(m2))
    return dict(lam=lam, dirn=int(dirn), g=g, n1=n1, n23=n23, vals=vals, flags=flags, span=span)

def classify(r):
    g, n1, n23, v = r['g'], r['n1'], r['n23'], r['vals']
    rho = v[('g', 1)][1]
    if rho == n1 and n1 <= n23:
        if g * n1 <= n23:
            if ('V', g) not in v: return 'A?'
            return 'A' if v[('V', g)][1] == g * n1 else 'C'
        return 'C'           # g n1 > n23: the full V-stack cannot be injective
    if rho == n23 and n23 <= n1:
        if g * n23 <= n1:
            if ('H', g) not in v: return 'B?'
            return 'B' if v[('H', g)][1] == g * n23 else 'C'
        return 'C'
    return 'C'

if __name__ == '__main__':
    rows = []
    for fn in sys.argv[1:]:
        for line in open(fn):
            if line.startswith('lam=') and 'ERROR' not in line:
                r = parse(line)
                if r: rows.append(r)
            elif 'ERROR' in line:
                print('ERROR line:', line.strip()[:200])
    cnt = Counter(); flagged = []
    for r in rows:
        c = classify(r); r['case'] = c; cnt[c] += 1
        if r['flags'] != '-': flagged.append(r)
    print('%d (component, direction) pairs: %s' % (len(rows), dict(sorted(cnt.items()))))
    print('flagged (SEP = rank6 < rank7 for a generic U of some dim; M2WIN = rank M2 > rank 6):', len(flagged))
    for r in flagged: print('  ', r['lam'], 'dir%d' % r['dirn'], r['flags'], r['vals'])
    print('cases C / undecided:')
    for r in rows:
        if r['case'] != 'A' and r['case'] != 'B':
            v = r['vals']
            print('  %-4s %s dir%d g=%d n1=%d n23=%d span=%s  rank6/rank7/M2: %s' % (r['case'], r['lam'], r['dirn'], r['g'], r['n1'], r['n23'], r['span'],
                  ' '.join('%s%d=%d/%d/%d' % (t, k, x[0], x[2], x[3]) for (t, k), x in sorted(v.items()) if (t, k) in (('g', 1), ('H', r['g']), ('V', r['g'])) or t == 'V' and k == max(kk for tt, kk in v if tt == 'V'))))
