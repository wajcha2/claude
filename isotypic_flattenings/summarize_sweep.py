"""python3 summarize_sweep.py n d out.md log1 [log2 ...]
Markdown summary of sweep_fast.py / sweep_hwv.py logs: one row per checked component (dims, g, ranks
low/high for every flattening), hits, total compute time, and the list of components NOT (yet) checked."""
import sys, re, itertools
from hwv import dim_schur
from isoflat import partitions, kronecker

n, d, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
logs = sys.argv[4:]
comps = {}
for lam in itertools.combinations_with_replacement(partitions(d, n), 3):
    g = kronecker(*lam)
    if g:
        comps['lam=%s' % (lam,)] = (lam, g)
rows, hits, total = {}, [], 0.0
for lf in logs:
    for l in open(lf):
        if not l.startswith('lam='):
            continue
        key = l.split(' g=')[0]
        fields = dict(((k, i), (int(a), int(b))) for k, i, a, b in re.findall(r'\b([gHV])(\d):(\d+)/(\d+)', l))
        t = float(re.findall(r'\(([\d.]+)s\)', l)[-1])
        span = re.findall(r'span=([\d,]+)', l)
        rows[key] = (fields, t, span[0] if span else '', 'SEPARATES' in l)
        total += t
        if 'SEPARATES' in l:
            hits.append(l.strip())
fmt = lambda v: '%d/%d' % v if v else ''
lines = ['# Isotypic flattening sweep n=%d d=%d: summary' % (n, d), '',
         'Checked %d of %d components (g > 0); total compute time %.0f s = %.1f h (sum over components, all workers).'
         % (len(rows), len(comps), total, total / 3600), '',
         'Entries a/b = rank of the flattening on the random rank-6 / rank-7 tensor. gN: generic functional on the '
         'multiplicity space, flattening from factor N; HN: full multiplicity space U = M (g >= 2), '
         'S^{l_N}V^* -> U^* (x) rest.', '']
lines += ['## Hits', ''] + (['    ' + h for h in hits] if hits else ['None: no flattening had smaller rank on the rank-6 tensor.']) + ['']
lines += ['## Checked components', '', '| component | dims | g | g1 | g2 | g3 | H1 | H2 | H3 | span | time (s) |',
          '|---|---|---|---|---|---|---|---|---|---|---|']
order = sorted(rows, key=lambda k: (comps[k][1] * sum((dim_schur(l, n) + 4) ** 2 for l in comps[k][0]) if k in comps else 0))
for k in order:
    fields, t, span, sep = rows[k]
    lam, g = comps.get(k, (k[4:], '?'))
    dims = tuple(dim_schur(l, n) for l in lam) if k in comps else ''
    lines.append('| %s%s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %.1f |' % (
        '**SEP** ' if sep else '', str(lam).replace(' ', ''), str(dims).replace(' ', ''), g,
        fmt(fields.get(('g', '1'))), fmt(fields.get(('g', '2'))), fmt(fields.get(('g', '3'))),
        fmt(fields.get(('H', '1'))), fmt(fields.get(('H', '2'))), fmt(fields.get(('H', '3'))), span, t))
missing = [comps[k] for k in comps if k not in rows]
lines += ['', '## Not (yet) checked: %d components' % len(missing), '']
lines += ['- %s g=%d dims=%s' % (str(lam).replace(' ', ''), g, str(tuple(dim_schur(l, n) for l in lam)).replace(' ', ''))
          for lam, g in missing]
open(out, 'w').write('\n'.join(lines) + '\n')
print('%d/%d checked, %d hits, %.1f h compute, %d not checked -> %s' % (len(rows), len(comps), len(hits), total / 3600, len(missing), out))
