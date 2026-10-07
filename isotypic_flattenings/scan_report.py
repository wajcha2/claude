"""python3 scan_report.py  ->  <SCAN>/STATUS.md and <SCAN>/summary.json from <SCAN>/state.json and the result files
(SCAN = scan/live by default)."""
import json, os, time, collections
from rankscan import generic_rank, components, cost_proxy
from hwv import dim_schur

SCAN = os.environ.get('SCAN', 'scan/live')


def dir_sat(n, lam, x):
    """rank from which direction x of a record is at its bounds (H_k = min(n1, k n23), V_k = min(k n1, n23)): the stored
    'sat_from', else (records of the closed-form families, wedge_family.py) the smallest evaluated rank whose profile
    is at the bounds; None if not saturated or not evaluated."""
    if x.get('sat_from') is not None:
        return x['sat_from']
    if x.get('status') == 'infeasible' or not x.get('prof') or x.get('t') is None:
        return None
    t = x['t']
    n1 = dim_schur(tuple(lam[t]), n)
    n23 = 1
    for u in range(3):
        if u != t:
            n23 *= dim_schur(tuple(lam[u]), n)
    for r in sorted(x['prof'], key=int):
        P = x['prof'][r]
        if all(h == min(n1, (k + 1) * n23) for k, h in enumerate(P['H'])) and \
           all(v == min((k + 1) * n1, n23) for k, v in enumerate(P['V'])):
            return int(r)
    return None


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
    # a component can have several records (a rerun with other limits, e.g. a larger WCAP): merge them -- a rank is
    # unknown only if no record resolved it (resolved = need minus unknown), separations are united
    for n in list(recs):
        merged = {}
        for rec in recs[n]:
            key = (rec['d'], tuple(tuple(x) for x in rec['lam']))
            m = merged.get(key)
            sats = [dir_sat(n, rec['lam'], x) for x in rec['dirs']]
            rsat = max(sats) if sats and all(v is not None for v in sats) else None   # every direction at its bound
            if m is None:
                m = dict(rec); m['sep'] = {k: list(v) for k, v in rec['sep'].items()}
                m['_need'] = set(rec['need']); m['_res'] = set(rec['need']) - set(rec['unknown'])
                m['_sat'] = rsat
                m['dirs'] = list(rec['dirs']); merged[key] = m
                continue
            if rsat is not None and (m['_sat'] is None or rsat < m['_sat']):
                m['_sat'] = rsat
            for k, v in rec['sep'].items():
                m['sep'].setdefault(k, []).extend(c for c in v if c not in m['sep'].get(k, []))
            m['_need'] |= set(rec['need']); m['_res'] |= set(rec['need']) - set(rec['unknown'])
            m['cpu'] += rec['cpu']; m['wall'] = max(m['wall'], rec['wall']); m['rss_peak_mb'] = max(m['rss_peak_mb'], rec['rss_peak_mb'])
        for m in merged.values():
            # saturation certificate: if a record has every direction at its rank bound from rank s on, the flattening
            # ranks are equal for all r >= s, so no rank r >= s is separated by this component -- resolved even when that
            # record was run for fewer ranks (e.g. the WCAP reruns n*_x1 asked only for the then-frontier rank)
            if m.get('_sat') is not None:
                m['_res'] |= {r for r in m['_need'] if r >= m['_sat']}
            m['unknown'] = sorted(m['_need'] - m['_res'])
            m['status'] = 'ok' if not m['unknown'] else 'partial'
        recs[n] = list(merged.values())
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
    timeouts = []
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
            tmo = [(t[0], t[1]) for j in jd for t in j.get('timeout', [])]
            failed += len(tmo)
            for lam_t, sec in tmo:
                timeouts.append('| %d | %d | %s | %.1f h |' % (n, d, fmt_lam(lam_t), sec / 3600.0))
            cpu = sum(rec['cpu'] for rec in done) / 3600.0
            mw = max([rec['wall'] for rec in done] or [0]); mr = max([rec['rss_peak_mb'] for rec in done] or [0])
            cov[d] = dict(total=len(comps), done=len(done), cap=cap, running=running, partial=len(partial), failed=failed)
            cover_rows.append('| %d | %d | %d | %d | %s | %d | %d | %.2f | %.0f | %.0f |' % (
                n, d, len(comps), len(done), '%.0e' % cap if cap else '-', len(comps) - len(done), len(partial) + failed, cpu, mw, mr))
        sep_r = sorted(dmin)
        skipped = [r for r in ns.get('skip', []) if r not in dmin]
        not_sep = [r for r in range(1, rgen) if r not in dmin and r not in skipped]
        # one-line progress statement
        skipped0 = set(ns.get('skip', []))
        open0 = [r for r in range(1, rgen) if r not in dmin and r not in skipped0]
        r0 = min(open0) if open0 else None
        def complete_for(d):
            if r0 is None:
                return cov[d]['done'] == cov[d]['total'] and not cov[d]['failed']
            ok = [rec for rec in R if rec['d'] == d and r0 not in rec['unknown']]
            return len(ok) == cov[d]['total'] and not cov[d]['failed']
        complete = [d for d in cov if complete_for(d)]
        dfull = 0
        while dfull + 1 in complete:
            dfull += 1
        reached = [d for d in cov if cov[d]['done']]
        dtop = max(reached or [0])
        part = ['d <= %d complete%s' % (dfull, ' for r = %d' % r0 if r0 else '')] if dfull else []
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
              '(memory caps), worker failure or time limit.  CPU h = sum over components; wall s / RSS MB = largest single component.', '',
              '| n | d | components (g>0) | checked | cost band reached | remaining | partial/failed | CPU h | max wall s | max RSS MB |',
              '|---|---|---|---|---|---|---|---|---|---|'] + cover_rows
    if timeouts:
        lines += ['', '## Components stopped by the time limit (not checked)', '', '| n | d | component | ran for |', '|---|---|---|---|'] + timeouts
    mon = os.path.join(SCAN, 'monitor.log')  # noqa
    if os.path.exists(mon):
        tail = open(mon).read().strip().splitlines()[-3:]
        lines += ['', '## Last resource samples (scan/monitor.log)', '', '```'] + tail + ['```']
    open(os.path.join(SCAN, 'STATUS.md'), 'w').write('\n'.join(lines) + '\n')
    json.dump(summary, open(os.path.join(SCAN, 'summary.json'), 'w'), indent=1, default=str)


if __name__ == '__main__':
    main()
