"""python3 special_report.py  -> special/RESULTS.md from special/res/*.jsonl (specialscan.py records).

One row per (format, degree, component, direction): Kronecker coefficient g, dims, target ranks, generic H_1 rank,
natural subspaces (U_k flag dims, swap eigenspaces) and their outcome, rank-drop points on lines (kinds of points with
their rank profiles; linear drop components), outcome, wall time and peak memory.  Hits (special U separating a
target rank r vs r + 1) first."""
import json, glob, os, collections

FILES = sorted(glob.glob('special/res/*.jsonl'))


def lamstr(lam):
    return '(' + ','.join(''.join(str(x) for x in l) for l in lam) + ')'


def load():
    recs = {}
    for f in FILES:
        if f.endswith('controls.jsonl') or '/verify' in f:
            continue
        for l in open(f):
            try:
                r = json.loads(l)
            except ValueError:
                continue
            key = (r['n'], r['d'], tuple(tuple(x) for x in r['lam']), r['t'], tuple(r['r']))
            if key not in recs:
                recs[key] = r
                r['methods'] = list(r['methods'])
                continue
            q = recs[key]                       # merge runs of other methods (a rerun of the same method replaces)
            if set(r['methods']) <= set(q['methods']) and set(r['methods']) != set(q['methods']):
                pass
            for c in r['cases']:
                q['cases'].append(c)
            q['hits'] += r['hits']
            q['methods'] = sorted(set(q['methods']) | set(r['methods']))
            q['wall'] = q.get('wall', 0) + r.get('wall', 0)
            q['rss_peak_mb'] = max(q.get('rss_peak_mb', 0), r.get('rss_peak_mb', 0))
            for k in ('flag', 'swaps', 'generic', 'n1', 'n23'):
                if k not in q and k in r:
                    q[k] = r[k]
            if r.get('status') != 'ok':
                q['status'] = r.get('status')
    return recs


def profstr(prof):
    return ', '.join('%s:%s' % (r, v) for r, v in sorted(prof.items(), key=lambda kv: int(kv[0])))


def summarize(r):
    """(natural-U text, lines text, hits list)"""
    nat, lines = [], []
    if 'flag' in r:
        fl = ' '.join('U%s=%d' % (k, v) for k, v in sorted(r['flag'].items(), key=lambda kv: int(kv[0])))
        sw = ' '.join('%s=%d' % (k, v) for k, v in r.get('swaps', {}).items())
        nat.append(fl + ((' ; ' + sw) if sw else ''))
        tested = [c['U'] for c in r['cases'] if c.get('method') == 'flag' and c.get('U')]
        nat.append(('tested ' + ', '.join(tested)) if tested else 'no natural U with 0 < dim < g')
    kinds = collections.OrderedDict()
    nl = 0
    for c in r['cases']:
        if 'line' not in c:
            continue
        nl += 1
        for f in c['factors']:
            if f.get('indep'):
                key = (c['method'].split('[')[0].split('-')[0], f['e'], profstr(f['prof']))
                kinds[key] = kinds.get(key, 0) + 1
    planes = [c for c in r['cases'] if c.get('method') == 'plane']
    for c in planes:
        if 'skipped' in c:
            lines.append('plane: %s.' % c['skipped'])
        else:
            pl = []
            for L in c.get('lines', []):
                for f in L.get('factors', []):
                    if f.get('indep'):
                        pl.append('e=%d [%s]' % (f['e'], profstr(f['prof'])))
            lines.append('plane (rho %d, curve deg %s, common resultant deg %d, factor degs %s): %s.' % (
                c['rho'], c['curve_deg'], c['gcd_deg'], c.get('factor_degs', []), '; '.join(pl) if pl else 'no isolated point'))
    spans = [c for c in r['cases'] if c.get('method', '').endswith('-span') and 'prof' in c]
    pts = [c for c in r['cases'] if c.get('method', '').endswith('-pts')]
    if nl:
        s = '%d lines' % nl
        if kinds:
            s += ': ' + '; '.join('%s e=%d x%d [%s]' % (m, e, k, pp) for (m, e, pp), k in kinds.items())
        else:
            s += ': no tensor-independent drop point'
        if spans:
            s += '; linear components: ' + ', '.join(c['U'].split(' ', 1)[0].replace('line-span', 'W') for c in spans)
        if pts:
            s += '; point spans: %d' % len(pts)
        lines.insert(0, s + '.')
    return ' '.join(nat), ' '.join(lines), r['hits']


def main():
    recs = load()
    rows, hits = [], []
    for key in sorted(recs, key=lambda k: (k[0], k[1], k[4], k[2], k[3])):
        r = recs[key]
        n, d, lam, t, R = key
        nat, lines, hs = summarize(r)
        gen = r.get('generic', {})
        g1 = ', '.join('%s:%s' % (x, v[0][0]) for x, v in sorted(gen.items(), key=lambda kv: int(kv[0])))
        out = 'HIT' if hs else ('none' if r.get('status') == 'ok' else r.get('status', '?'))
        rows.append('| %dx%dx%d | %d | %s | %d | %d | %s | %s | %s | %s | %s | %s | %.0f s / %.0f MB |' % (
            n, n, n, d, lamstr(lam), r['g'], t + 1, '%s, %s' % (r.get('n1', '?'), r.get('n23', '?')),
            '%d-%d' % (R[0], R[-1]) if len(R) > 1 else str(R[0]), g1, nat or '-', lines or '-', out,
            r.get('wall', 0), r.get('rss_peak_mb', 0)))
        for h in hs:
            hits.append('| %dx%dx%d | %d | %s | %d | %d | %s | %s | %s | %s |' % (
                n, n, n, d, lamstr(lam), r['g'], t + 1, h.get('U'), ' '.join(h.get('sep', [])),
                profstr(h['prof']) if isinstance(h.get('prof'), dict) and h['prof'] and not isinstance(next(iter(h['prof'].values())), list)
                else '; '.join('r%s H%s V%s' % (x, v[0], v[1][1:]) for x, v in sorted(h.get('prof', {}).items(), key=lambda kv: int(kv[0]))),
                '%s' % h.get('r-1,r+2', '')))
    # coverage summary
    cov = collections.defaultdict(lambda: [0, 0, set(), 0.0])
    for key, r in recs.items():
        c = cov[(key[0], key[1], key[4])]
        c[0] += 1; c[1] += bool(r['hits']); c[2].add(key[2]); c[3] += r.get('wall', 0)
    with open('special/RESULTS.md', 'w') as fh:
        fh.write('# Special subspaces U: results (specialscan.py, see agents/special.md)\n\n')
        fh.write('Generated by special_report.py from special/res/*.jsonl.  Target: rank r vs r + 1 for r in the "ranks" column; '
                 '"H1 generic" = rank of one generic functional at the evaluated tensor ranks.  Line points: kind (line = random '
                 'line, in = line inside a linear drop component, thru = line through a natural point), e = degree of the point\'s '
                 'field F_{p^e}, multiplicity over all lines, [rank profile r:rank].  W(k) = linear drop component of '
                 'dimension k (tested as U with H and V prefixes).\n\n')
        fh.write('## Coverage\n\n| format | d | ranks | components | directions | directions with hits | wall |\n|---|---|---|---|---|---|---|\n')
        for (n, d, R), c in sorted(cov.items()):
            fh.write('| %dx%dx%d | %d | %s | %d | %d | %d | %.0f s |\n' % (n, n, n, d, '%d-%d' % (R[0], R[-1]) if len(R) > 1 else R[0],
                                                                        len(c[2]), c[0], c[1], c[3]))
        fh.write('\n## Hits (special U separating a target rank)\n\n')
        if hits:
            fh.write('| format | d | component | g | dir | U | separation | profile | ranks r-1, r+2 |\n|---|---|---|---|---|---|---|---|---|\n')
            fh.write('\n'.join(hits) + '\n')
        else:
            fh.write('None so far.\n')
        fh.write('\n## All cases\n\n| format | d | component | g | dir | n1, n23 | ranks | H1 generic | natural U (dims; tested) | '
                 'rank-drop points on lines | outcome | time / peak |\n|---|---|---|---|---|---|---|---|---|---|---|---|\n')
        fh.write('\n'.join(rows) + '\n')
    print('special/RESULTS.md: %d rows, %d hits' % (len(rows), len(hits)))


if __name__ == '__main__':
    main()
