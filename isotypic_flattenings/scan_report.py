"""python3 scan_report.py  ->  <SCAN>/STATUS.md and <SCAN>/summary.json from <SCAN>/state.json and the result files
(SCAN = scan/live by default)."""
import json, os, time, collections
from rankscan import generic_rank, components, cost_proxy

SCAN = os.environ.get('SCAN', 'scan/live')


def compress(cfgs):
    """['1H2','1H3','1H4','2V3'] -> '1H2-4 2V3'  (direction, H|V, dim U)."""
    by = collections.defaultdict(list)
    for c in cfgs:
        by[c[:2]].append(int(c[2:]))
    out = []
    for key in sorted(by):
        ks = sorted(set(by[key])); runs = []
        for k in ks:
            if runs and k == runs[-1][1] + 1:
                runs[-1][1] = k
            else:
                runs.append([k, k])
        out.append(key + ','.join('%d' % a if a == b else '%d-%d' % (a, b) for a, b in runs))
    return ' '.join(out)


def fmt_lam(lam):
    return '(' + ','.join(''.join(map(str, l)) if max(l) < 10 else '.'.join(map(str, l)) for l in lam) + ')'


def ranges(rs):
    rs = sorted(rs); out = []
    for r in rs:
        if out and r == out[-1][1] + 1:
            out[-1][1] = r
        else:
            out.append([r, r])
    return ', '.join('%d' % a if a == b else '%d-%d' % (a, b) for a, b in out)


def main():
    st = json.load(open(os.path.join(SCAN, 'state.json')))
    recs = collections.defaultdict(list)            # n -> records
    for name, job in st['jobs'].items():
        if os.path.exists(job['out']):
            for l in open(job['out']):
                try:
                    rec = json.loads(l)
                except ValueError:
                    continue
                rec['job'] = name
                recs[job['n']].append(rec)
    lines = ['# Isotypic-flattening rank scan (n x n x n): status', '',
             'Updated %s.  For each format and rank r: the lowest degree d in which some isotypic flattening has smaller rank on a '
             'random rank-r tensor than on a random rank-(r+1) tensor, and all components that do it in that degree.  '
             'Configurations: `1H1` = direction 1 (source S^{l1}V^*), one generic functional (dim U = 1); `1H2-4` = stacked '
             'flattening S^{l1}V^* -> U^* (x) S^{l2}V (x) S^{l3}V for a generic U of dim 2..4; `1V3` = U (x) S^{l1}V^* -> S^{l2}V (x) S^{l3}V, dim U = 3.  '
             'Partitions are written without commas, e.g. (62,3221,3221).  Method and code: SCAN.md, rankscan.py.'
             % time.strftime('%Y-%m-%d %H:%M UTC', time.gmtime()), '']
    summary = {}
    detail = []
    cover_rows = []
    for nkey in sorted(st['n'], key=int):
        n = int(nkey); ns = st['n'][nkey]; rgen = ns['rgen']
        R = recs.get(n, [])
        dmin, seps = {}, collections.defaultdict(list)
        for rec in R:
            for r, cfg in rec['sep'].items():
                r = int(r)
                if rec['d'] < dmin.get(r, 99):
                    dmin[r] = rec['d']
        for rec in R:
            for r, cfg in rec['sep'].items():
                r = int(r)
                if rec['d'] == dmin[r]:
                    seps[r].append((fmt_lam(rec['lam']), rec['g'], rec['dims'], compress(cfg)))
        # coverage per degree
        jobs_n = {nm: j for nm, j in st['jobs'].items() if j['n'] == n}
        dmax_seen = max([j['d'] for j in jobs_n.values()] or [0])
        cov = {}
        for d in range(1, dmax_seen + 1):
            comps = components(n, d)
            done = [rec for rec in R if rec['d'] == d]
            jd = [j for j in jobs_n.values() if j['d'] == d]
            cap = max([j['cap'][1] for j in jd] or [0])
            running = any(j['status'] == 'running' for j in jd)
            partial = [rec for rec in done if rec['status'] != 'ok']
            failed = sum(len(j['failed']) for j in jd)
            cpu = sum(rec['cpu'] for rec in done) / 3600.0
            mw = max([rec['wall'] for rec in done] or [0]); mr = max([rec['rss_peak_mb'] for rec in done] or [0])
            cov[d] = dict(total=len(comps), done=len(done), cap=cap, running=running, partial=len(partial), failed=failed)
            cover_rows.append('| %d | %d | %d | %d | %s | %d | %d | %.2f | %.0f | %.0f |' % (
                n, d, len(comps), len(done), '%.0e' % cap if cap else '-', len(comps) - len(done), len(partial) + failed, cpu, mw, mr))
        sep_r = sorted(dmin)
        skipped = [r for r in ns.get('skip', []) if r not in dmin]
        not_sep = [r for r in range(1, rgen) if r not in dmin and r not in skipped]
        # one-line progress statement
        complete = [d for d in cov if cov[d]['done'] == cov[d]['total'] and not cov[d]['partial'] and not cov[d]['failed']]
        dfull = 0
        while dfull + 1 in complete:
            dfull += 1
        reached = [d for d in cov if cov[d]['done']]
        dtop = max(reached or [0])
        part = ['d <= %d complete' % dfull] if dfull else []
        for d in sorted(cov):
            if d > dfull and cov[d]['done']:
                part.append('d = %d: %d of %d components%s' % (d, cov[d]['done'], cov[d]['total'], ' (running)' if cov[d]['running'] else ''))
        bydeg = collections.defaultdict(list)
        for r in sep_r:
            bydeg[dmin[r]].append(r)
        sep_txt = '; '.join('r = %s at d = %d' % (ranges(rs), d) for d, rs in sorted(bydeg.items()))
        stmt = '**%dx%dx%d** (generic rank %d): with d up to %d [%s] separated %s' % (
            n, n, n, rgen, dtop, '; '.join(part) or 'nothing run yet', sep_txt or 'nothing')
        if not_sep:
            stmt += ', but NOT r = %s (vs r + 1)' % ranges(not_sep)
        if skipped:
            stmt += '; r = %s not pursued (%s)' % (ranges(skipped), ns.get('skip_reason', ''))
        if not_sep or skipped:
            pass
        else:
            stmt += ' -- every rank up to r_gen - 1 = %d is separated (max rank reached at d = %d)' % (rgen - 1, dmin[rgen - 1])
        if ns.get('finished'):
            stmt += '.  Finished.'
        lines.append('* ' + stmt)
        summary[n] = {'rgen': rgen, 'dmin': dmin, 'not_separated': not_sep, 'coverage': cov,
                      'separators': {r: seps[r] for r in sep_r}}
        detail += ['', '## %dx%dx%d (generic rank %d)' % (n, n, n, rgen), '',
                   '| r vs r+1 | lowest d | # components | separating components at that degree: partitions, g, dims, configurations |',
                   '|---|---|---|---|']
        for r in range(1, rgen):
            if r in dmin:
                S = seps[r]
                shown = '; '.join('%s g=%d %s %s' % (l, g, 'x'.join(map(str, dm)), c) for l, g, dm, c in S[:10])
                if len(S) > 10:
                    shown += '; ... (+%d more, see summary.json)' % (len(S) - 10)
                detail.append('| %d vs %d | %d | %d | %s |' % (r, r + 1, dmin[r], len(S), shown))
            elif r in ns.get('skip', []):
                detail.append('| %d vs %d | not pursued: %s | 0 | |' % (r, r + 1, ns.get('skip_reason', '')))
            else:
                detail.append('| %d vs %d | not yet (checked up to d = %d) | 0 | |' % (r, r + 1, dtop))
    lines += detail
    lines += ['', '## Coverage, time and memory per (n, d)', '',
              'checked = components with a result (all three directions, every needed rank); remaining = not yet run '
              '(cost proxy above the current band, or job still running); partial = some direction or rank infeasible '
              '(memory caps) or worker failure.  CPU h = sum over components; wall s / RSS MB = largest single component.', '',
              '| n | d | components (g>0) | checked | cost band reached | remaining | partial/failed | CPU h | max wall s | max RSS MB |',
              '|---|---|---|---|---|---|---|---|---|---|'] + cover_rows
    mon = os.path.join(SCAN, 'monitor.log')  # noqa
    if os.path.exists(mon):
        tail = open(mon).read().strip().splitlines()[-3:]
        lines += ['', '## Last resource samples (scan/monitor.log)', '', '```'] + tail + ['```']
    open(os.path.join(SCAN, 'STATUS.md'), 'w').write('\n'.join(lines) + '\n')
    json.dump(summary, open(os.path.join(SCAN, 'summary.json'), 'w'), indent=1, default=str)


if __name__ == '__main__':
    main()
