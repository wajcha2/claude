"""python3 scan_runner.py            (start with: setsid nohup python3 -u scan_runner.py >> scan/live/runner.log 2>&1 &)

Orchestrates rankscan.py over the formats n x n x n (n in NS) and degrees d = 1..DMAX, see SCAN.md.

Job (n, d, stage) covers the components of degree d whose cost proxy lies in (CAPS[stage-1], CAPS[stage]] and
resolves the ranks NEED = {r < r_gen : no separator of r vs r+1 is known in a degree < d, r not skipped}.
Per format the jobs are run in the order (d, stage): degree d is completed in every cost band before degree d + 1
is started (that is what the lowest separating degree needs); degrees above d_min(target rank) are not run (target
= r_gen - 1 unless skipped in state.json).  Across formats, a free worker slot goes to the format with the fewest
running workers, then to a format with <= 10 unchecked components left in its current degree, then round robin (the
format whose last worker start is oldest; fair share since 2026-10-06 18:30, round robin since 2026-10-07 07:10; before:
the order (stage, n)).  A worker is started only if the estimated peak memory of the component it
will take plus that of the running components fits MEMBUDGET MB (<SCAN>/membudget overrides); otherwise no worker is
started until enough memory is free (formats listed in <SCAN>/pause start no workers; the next component waits, it is not skipped; cheap or small components may
backfill past it, but once only backfilled components keep it out, for at most BFWAIT s more (<SCAN>/bfwait
overrides); after that nothing backfills until it starts).  A component running longer than TLIMIT seconds is stopped and recorded as 'timeout' (not checked,
listed in the report).  Running jobs that are not the current job of their format (after a change of the ordering)
are 'deferred': their unclaimed components get a placeholder claim so that no worker takes them, until the format
reaches that job again.  On a restart, workers that are still running are adopted (not killed).
A resource line (memory, per-worker RSS, load) goes to <SCAN>/monitor.log every MONITOR s, and scan_report.py writes
<SCAN>/STATUS.md after every job and every REPORT s.  State: <SCAN>/state.json (SCAN = scan/live, untracked;
scan_autosave.sh copies everything into scan/ and commits)."""
import os, sys, json, time, subprocess, itertools, signal, collections, calendar
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rankscan import generic_rank, components, cost_proxy, is_onerow, word_minor_size
from hwv import dim_schur
from colwedge_family import is_colwedge

NS = [int(x) for x in os.environ.get('NS', '3,4,5,6,7,8,9,10').split(',')]
DMAX = int(os.environ.get('DMAX', '10'))
NCORES = int(os.environ.get('NCORES', '4'))
LONGRUN = float(os.environ.get('LONGRUN', '14400'))  # s: a blocking backfill running longer counts as long (see launch)
BFWAIT = float(os.environ.get('BFWAIT', '1800'))   # s a waiting component lets cheap/small components backfill past it
CAPS = [0] + [float(x) for x in os.environ.get('CAPS', '3e5,3e6,3e7,3e8,3e9').split(',')]
TLIMIT = float(os.environ.get('TLIMIT', '7200'))
F32_SINCE = 1792731484.0     # 2026-10-23 04:58:04 UTC: rankscan.py keeps flattenings and elimination bases in float32
EVALMARGIN = float(os.environ.get('EVALMARGIN', '0'))       # MB over the calibrated evaluation phase (see est_peak_mb)
MEMBUDGET = float(os.environ.get('MEMBUDGET', '15000'))     # MB for the workers (container: 16 GB, no swap)
MONITOR = int(os.environ.get('MONITOR', '300'))
REPORT = int(os.environ.get('REPORT', '900'))
SCAN = os.environ.get('SCAN', 'scan/live')
STATE = os.path.join(SCAN, 'state.json')
WENV = {'OPENBLAS_NUM_THREADS': '1', 'OMP_NUM_THREADS': '1', 'PYTHONDONTWRITEBYTECODE': '1',
        'PYTHONHASHSEED': '0'}   # reproducible path-search tie-breaking, hence filling choice (checkpoints)
WENV['CKPT'] = os.path.join(SCAN, 'ckpt')   # rankscan.py checkpoints long block evaluations here (since 2026-10-20: a
                                            # container restart had cost the 8x8x8 hook rerun 24.7 h of work)
MARKS = ('failed', 'deferred', 'timeout', 'done')       # claim files that are not held by a worker ('done': restored claim of a finished component)


def log(msg):
    print(time.strftime('%Y-%m-%d %H:%M:%S ', time.gmtime()) + msg, flush=True)


def load_state():
    if os.path.exists(STATE):
        return json.load(open(STATE))
    return {'jobs': {}, 'n': {str(n): {'rgen': generic_rank(n), 'stage': 1, 'd': 1, 'finished': False} for n in NS}}


def save_state(st):
    tmp = STATE + '.tmp'
    json.dump(st, open(tmp, 'w'), indent=1)
    os.replace(tmp, STATE)


def results(out):
    done = {}
    if os.path.exists(out):
        for l in open(out):
            try:
                rec = json.loads(l)
            except ValueError:
                continue
            done[tuple(tuple(x) for x in rec['lam'])] = rec
    return done


_dm_cache = {}


def dmin_map(st, n):
    """r -> lowest degree with a separator, over all jobs of n (cached until a job changes)."""
    if n in _dm_cache:
        return _dm_cache[n]
    dm = {}
    for jn, job in st['jobs'].items():
        if job['n'] != n:
            continue
        for rec in results(job['out']).values():
            for r in rec['sep']:
                r = int(r)
                dm[r] = min(dm.get(r, 99), rec['d'])
    _dm_cache[n] = dm
    return dm


def nlines(path):
    try:
        with open(path, 'rb') as fh:
            return sum(1 for _ in fh)
    except FileNotFoundError:
        return 0


_comp_cache = {}


def comp_list(n, d):
    if (n, d) not in _comp_cache:
        _comp_cache[(n, d)] = [(cost_proxy(n, lam, g), li, lam, g) for li, lam, g in components(n, d)]
    return _comp_cache[(n, d)]


_empty = set()          # (n, d, stage) known to have no components in the band


def make_job(st, n, d, stage):
    """create job (n, d, stage); returns its name, or None if it has nothing to do."""
    if (n, d, stage) in _empty:
        return None
    ns = st['n'][str(n)]
    rgen = ns['rgen']
    dm = dmin_map(st, n)
    skip = set(ns.get('skip', []))
    need = [r for r in range(1, rgen) if dm.get(r, 99) >= d and r not in skip]
    name = 'n%d_d%d_s%d' % (n, d, stage)
    if not need:
        return None
    lo, hi = CAPS[stage - 1], CAPS[stage]
    comps = sorted(c for c in comp_list(n, d) if lo < c[0] <= hi)
    total = len(comp_list(n, d))
    if not comps:
        _empty.add((n, d, stage))
        return None
    os.makedirs(os.path.join(SCAN, 'jobs'), exist_ok=True)
    lst = os.path.join(SCAN, 'jobs', name + '.txt')
    with open(lst, 'w') as fh:
        for c in comps:
            fh.write(repr(c[2]) + '\n')
    st['jobs'][name] = {'n': n, 'd': d, 'stage': stage, 'need': need, 'list': lst, 'ncomp': len(comps),
                        'ncomp_degree': total, 'cap': [lo, hi], 'out': os.path.join(SCAN, 'res', name + '.jsonl'),
                        'claims': os.path.join(SCAN, 'claims', name), 'status': 'running',
                        't_start': time.time(), 'failed': [], 'timeout': []}
    os.makedirs(os.path.join(SCAN, 'res'), exist_ok=True)
    os.makedirs(st['jobs'][name]['claims'], exist_ok=True)
    log('job %s created: %d components (cost %.0e..%.0e of %d in degree %d), need=%s' % (name, len(comps), lo, hi, total, d, need))
    return name


def advance(st, n):
    """the current job of n: the first job in the order (d, stage) that is running or can be created; marks n
    finished when there is none."""
    ns = st['n'][str(n)]
    if ns['finished']:
        return None
    rgen = ns['rgen']
    dm = dmin_map(st, n)
    skip = set(ns.get('skip', []))               # ranks not pursued for this n (state.json, with a reason)
    target = max(r for r in range(1, rgen) if r not in skip)
    dtop = min(DMAX, dm.get(target, 99))          # degrees beyond d_min(target rank) are not needed
    for d in range(1, dtop + 1):
        for s in range(1, len(CAPS)):
            name = 'n%d_d%d_s%d' % (n, d, s)
            job = st['jobs'].get(name)
            if job is not None:
                if job['status'] == 'running':
                    if (ns['d'], ns['stage']) != (d, s):
                        ns['d'], ns['stage'] = d, s
                    return name
                continue
            name = make_job(st, n, d, s)
            if name is not None:
                ns['d'], ns['stage'] = d, s
                return name
    ns['finished'] = True
    log('n=%d finished (every degree up to %d in every cost band)' % (n, dtop))
    return None


def read_claim(path):
    try:
        parts = open(path).read().split()
        return parts[0], int(parts[1])
    except (ValueError, IndexError, OSError):
        return None, None


def claimed(job):
    try:
        return len(os.listdir(job['claims']))
    except FileNotFoundError:
        return 0


_done_cache, _list_cache, _lam_cache = {}, {}, {}


def done_lams(job):
    """set of components with a result (cached until the result file changes)."""
    try:
        mt = os.path.getmtime(job['out'])
    except FileNotFoundError:
        return set()
    c = _lam_cache.get(job['out'])
    if c is None or c[0] != mt:
        c = (mt, set(results(job['out'])))
        _lam_cache[job['out']] = c
    return c[1]


def left_in_degree(st, n, d):
    """components of degree d of format n without a result in any of its band jobs (extra jobs not counted)."""
    done = set()
    for j in st['jobs'].values():
        if j['n'] == n and j['d'] == d and not j.get('extra'):
            done |= done_lams(j)
    return len(comp_list(n, d)) - len(done)


_est_cache, _calib = {}, {}


def mat_parts(n, lam, g, old=False):
    """per direction: (MB of the g evaluated flattenings N1 x K, MB of the combination phi and the H and V
    eliminations).  Workers started since F32_SINCE: float32 throughout, 4 g N1 K and 4 (N1 K + N1^2 + K^2); before
    (old=True): flattenings float64 (float32 above 2^26 entries) and 8 (N1 K + N1^2 + K^2)."""
    out = []
    for t in range(3):
        a = lam[t]; b, c = [lam[u] for u in range(3) if u != t]
        n1 = dim_schur(a, n); n23 = dim_schur(b, n) * dim_schur(c, n)
        N1 = min(n1, g * n23) + 8; K = min(g * n1, n23) + 8
        el = g * N1 * K
        if old:
            out.append((el * (8 if el <= (1 << 26) else 4) / 2.0 ** 20, 8.0 * (N1 * K + N1 * N1 + K * K) / 2.0 ** 20))
        else:
            out.append((4.0 * el / 2.0 ** 20, 4.0 * (N1 * K + N1 * N1 + K * K) / 2.0 ** 20))
    return out


def eval_phase_mb(st, n, d):
    """memory of the evaluation phase beyond the flattenings (word minors, contraction blocks), calibrated on the
    recorded peaks of degree d of format n: max of peak RSS - flattenings over its network components whose peak the
    elimination phase does not explain (peak > flattenings + eliminations + 1 GB), + 512 MB margin; 4 GB while fewer
    than 5 records exist or none is evaluation-dominated.  Refreshed every 15 min."""
    c = _calib.get((n, d))
    if c is not None and time.time() - c[0] < 900:
        return c[1]
    vals, allv, nrec_elim = [], [], [0]
    for j in st['jobs'].values():
        if j['n'] != n or j['d'] != d or j.get('extra') or not os.path.exists(j['out']):
            continue
        for l in open(j['out']):
            try:
                r = json.loads(l)
            except ValueError:
                continue
            if any(x.get('method') in ('onerow', 'colwedge') or x.get('status') == 'infeasible' for x in r['dirs']):
                continue
            lam = tuple(tuple(x) for x in r['lam'])
            P = mat_parts(n, lam, r['g'], ('ts' not in r or calendar.timegm(time.strptime(r['ts'], '%Y-%m-%dT%H:%M:%SZ')) < F32_SINCE))
            allv.append(r['rss_peak_mb'] - max(fs for fs, _ in P))
            if r['rss_peak_mb'] > max(fs + m for fs, m in P) + 1024:      # peak not explained by the elimination
                vals.append(allv[-1])
            else:
                nrec_elim[0] += 1
    if vals and len(vals) + nrec_elim[0] >= 5:
        v = max(vals) + 512
    elif len(allv) >= 5:            # no evaluation-dominated peak: the evaluation phase stays below every peak - flattenings
        v = max(allv) + 512
    else:
        v = 4096.0
    _calib[(n, d)] = (time.time(), v)
    return v


def f32_model_on():
    """<SCAN>/f32model = 1: estimate workers started since F32_SINCE with the float32 matrix sizes (mat_parts); off
    (the default) keeps the float64 sizes for every worker until a large float32 peak has confirmed the new ones."""
    try:
        return open(os.path.join(SCAN, 'f32model')).read().split()[0] == '1'
    except (OSError, IndexError):
        return False


def est_peak_mb(st, n, d, lam, g, extra=False, job=None, old=False):
    """estimated peak RSS of a worker on component lam (MB): two phases -- evaluation (flattenings + word minors and
    contraction blocks, eval_phase_mb, which carries its own 512 MB margin) and elimination (flattenings + phi +
    eliminations, + 800 MB: 300 MB was 130 MB short on 8x8x8 ((3,2,1),(3,2,1),(3,1,1,1)): 6785 MB) -- of its largest
    direction.  Checked against the recorded components: no peak above its estimate (one-row
    components, closed form: 3.5 GB; extra jobs with a larger WCAP: + extra_mb)."""
    if is_onerow(lam):
        return 3584.0
    if is_colwedge(lam):                 # closed form (colwedge_family.py): rows stream into the echelon form (<= m x m
        dims = [dim_schur(tuple(l), n) for l in lam]   # float64) + chunk arrays (the first version stored the matrix
        m = max(min(x, dims[0] * dims[1] * dims[2] // x) + 8 for x in dims)   # three times: peaks 24 m^2 + 0.3 GB)
        return 10.0 * m * m / 2 ** 20 + 1536.0
    if job is not None:            # word-minor tensor above WCAP at the lowest needed rank rlo: rankscan.py either probes
        wcap = int(job.get('env', {}).get('WCAP', 1 << 26))   # the highest feasible rank (SATPROBE, if >= rlo - 4: a normal
        rlo = min(job['need'])                                 # evaluation, normal estimate) or skips the component at once
        if word_minor_size(lam, n, rlo) > wcap:
            rmax = max([r for r in range(1, rlo) if word_minor_size(lam, n, r) <= wcap] or [0])
            if rmax < max(2, rlo - 4):
                return 300.0                     # largest recorded one-row peak: 3.0 GB (9x9x9 d = 6)
    old = old or not f32_model_on()
    key = (n, lam, g, old)            # old: a worker started before F32_SINCE (float64 matrices)
    if key not in _est_cache:
        _est_cache[key] = mat_parts(n, lam, g, old)
    B = eval_phase_mb(st, n, d)
    # elimination phase: + 1.2 GB over the matrices (largest recorded excess 0.77 GB: 9x9x9 ((3,2,1),(3,2,1),(2,1^4)) 9218 MB);
    # evaluation phase: B (calibrated on the recorded peaks, + 512 MB) + EVALMARGIN (0 since 2026-10-18 07:43; it was 800
    # as well, so the evaluation estimates carried 1.3 GB over the largest recorded excess: 6x6x6 d = 8 peaks <= 1.4 GB
    # were estimated at 2.8-3.0 GB and kept cores idle next to the 9.4 GB 9x9x9 components; without it every one of the
    # 2661 recorded network peaks is still >= 0.2 GB below its estimate)
    return max(max(fs + B + EVALMARGIN, fs + m + 400 + 800) for fs, m in _est_cache[key]) + (extra_mb(n, lam, job) if extra else 0)


def extra_mb(n, lam, job):
    """what a rerun with a larger WCAP adds (MB): its largest word-minor tensor (int64, at the highest needed rank it can
    evaluate) + 1 GB.  Since 2026-10-19 11:29 (before: a flat 4 GB, which kept a core idle next to the 7.9 GB estimate of
    the 8x8x8 hook rerun); every recorded rerun peak is >= 0.4 GB below it (the flat 4 GB: >= 1.6 GB)."""
    if job is None:
        return 4096.0
    wcap = int(job.get('env', {}).get('WCAP', 1 << 26))
    rmax = max([x for x in range(1, max(job['need']) + 1) if word_minor_size(lam, n, x) <= wcap] or [0])
    return 8.0 * word_minor_size(lam, n, rmax) / 2 ** 20 + 1024


def next_component(job, exclude=()):
    """the component a new worker of this job takes: the first listed one with neither a claim nor a result
    (rankscan.py's order), skipping the indices in exclude (predicted for workers that have not claimed yet)."""
    idx = {lam: (li, g) for _, li, lam, g in comp_list(job['n'], job['d'])}
    done = done_lams(job)
    try:
        cl = {int(fn) for fn in os.listdir(job['claims']) if fn.isdigit()}
    except FileNotFoundError:
        cl = set()
    for l in open(job['list']):
        if not l.strip():
            continue
        lam = tuple(tuple(x) for x in eval(l))
        li, g = idx[lam]
        if lam in done or li in cl or li in exclude:
            continue
        return li, lam, g
    return None


def worker_component(job, pid):
    """index of the newest claim held by pid in this job (None before the worker has claimed)."""
    best = None
    try:
        for fn in os.listdir(job['claims']):
            path = os.path.join(job['claims'], fn)
            w, p = read_claim(path)
            if p == pid and w not in MARKS:
                mt = os.path.getmtime(path)
                if best is None or mt > best[0]:
                    best = (mt, int(fn))
    except FileNotFoundError:
        pass
    return None if best is None else best[1]


def refresh_extra_lists(st):
    """rerun jobs with 'r0' and 'dropped_not_yet_run' (components not tried by a normal job when the rerun list was made):
    a component whose normal record now exists is added to the rerun list only if that record leaves r0 unresolved
    (not at the rank bounds from some rank <= r0, and r0 not resolved); a done job with new components is reopened."""
    from scan_report import dir_sat
    changed = False
    for name, j in st['jobs'].items():
        if not j.get('extra') or 'r0' not in j or not j.get('dropped_not_yet_run'):
            continue
        n, d, r0 = j['n'], j['d'], j['r0']
        normal = {}
        for jj in st['jobs'].values():
            if jj['n'] == n and jj['d'] == d and not jj.get('extra') and os.path.exists(jj['out']):
                for l in open(jj['out']):
                    try:
                        r = json.loads(l)
                    except ValueError:
                        continue
                    normal[tuple(tuple(x) for x in r['lam'])] = r
        add, still = [], []
        for rep in j['dropped_not_yet_run']:
            lam = tuple(tuple(x) for x in eval(rep))
            r = normal.get(lam)
            if r is None:
                still.append(rep)
                continue
            sats = [dir_sat(n, r['lam'], x) for x in r['dirs']]
            sat = max(sats) if sats and all(v is not None for v in sats) else None
            if not ((sat is not None and sat <= r0) or r0 in set(r['need']) - set(r['unknown'])):
                add.append(lam)
        if len(still) != len(j['dropped_not_yet_run']):
            if add:
                with open(j['list'], 'a') as fh:
                    fh.write(''.join(repr(l) + '\n' for l in add))
                j['ncomp'] += len(add)
                _list_cache.pop(j['list'], None)
                if j['status'] == 'done':
                    j['status'] = 'running'
            log('rerun list %s: %d component(s) tried by normal jobs, %d added (r = %d unresolved), %d not tried yet'
                % (name, len(j['dropped_not_yet_run']) - len(still), len(add), r0, len(still)))
            j['dropped_not_yet_run'] = still
            changed = True
    return changed


def open_components(job):
    """number of listed components with neither a claim nor a result (a job is runnable iff > 0; counting claim
    files alone kept starting workers that found nothing to do when a finished component had lost its claim)."""
    key = job['list']
    if key not in _list_cache:
        idx = {lam: li for _, li, lam, _ in comp_list(job['n'], job['d'])}
        _list_cache[key] = {idx[tuple(tuple(x) for x in eval(l))] for l in open(job['list']) if l.strip()}
    lis = _list_cache[key]
    try:
        mt = os.path.getmtime(job['out'])
    except FileNotFoundError:
        mt = None
    c = _done_cache.get(job['out'])
    if c is None or c[0] != mt:
        idx = {lam: li for _, li, lam, _ in comp_list(job['n'], job['d'])}
        c = (mt, {idx[lam] for lam in results(job['out']) if lam in idx} if mt else set())
        _done_cache[job['out']] = c
    try:
        cl = {int(fn) for fn in os.listdir(job['claims']) if fn.isdigit()}
    except FileNotFoundError:
        cl = set()
    return len(lis - cl - c[1])


def pid_alive(pid):
    """running and not a zombie."""
    try:
        with open('/proc/%d/status' % pid) as fh:
            for l in fh:
                if l.startswith('State:'):
                    return 'Z' not in l.split()[1]
    except OSError:
        return False
    return True


def is_worker(pid):
    try:
        return b'rankscan.py' in open('/proc/%d/cmdline' % pid, 'rb').read()
    except OSError:
        return False


def set_deferred(job, on):
    """on: placeholder claims for all unclaimed components; off: remove them."""
    lst = [tuple(tuple(x) for x in eval(l)) for l in open(job['list']) if l.strip()]
    idx = {lam: li for _, li, lam, _ in comp_list(job['n'], job['d'])}
    k = 0
    if on:
        done = results(job['out'])
        for lam in lst:
            fn = os.path.join(job['claims'], str(idx[lam]))
            if lam not in done and not os.path.exists(fn):
                open(fn, 'w').write('deferred 0\n'); k += 1
    else:
        for fn in os.listdir(job['claims']):
            if read_claim(os.path.join(job['claims'], fn))[0] == 'deferred':
                os.remove(os.path.join(job['claims'], fn)); k += 1
    return k


def stale_claims(job, alive):
    """claims of dead workers whose component has no result."""
    dead = []
    for fn in os.listdir(job['claims']):
        w, pid = read_claim(os.path.join(job['claims'], fn))
        if w is not None and w not in MARKS and pid not in alive:
            dead.append((fn, pid))
    if not dead:
        return []
    done = results(job['out'])
    comps = {li: lam for _, li, lam, _ in comp_list(job['n'], job['d'])}
    return [(fn, comps[int(fn)], pid) for fn, pid in dead if int(fn) in comps and comps[int(fn)] not in done]


def rss_mb(pid):
    try:
        for l in open('/proc/%d/status' % pid):
            if l.startswith('VmRSS'):
                return int(l.split()[1]) / 1024.0
    except OSError:
        pass
    return 0.0


def meminfo():
    m = {}
    for l in open('/proc/meminfo'):
        k, v = l.split(':')
        m[k] = int(v.split()[0]) / 1024.0
    return m


def cgroup_mem():
    try:
        path = [l.split(':', 2)[2].strip() for l in open('/proc/self/cgroup') if ':memory:' in l][0]
        base = '/sys/fs/cgroup/memory' + path
        return (int(open(base + '/memory.usage_in_bytes').read()) / 2 ** 20,
                int(open(base + '/memory.max_usage_in_bytes').read()) / 2 ** 20)
    except (IndexError, OSError, ValueError):
        return (0.0, 0.0)


def report():
    subprocess.run([sys.executable, 'scan_report.py'], env=dict(os.environ, SCAN=SCAN, **WENV))


def main():
    os.makedirs(os.path.join(SCAN, 'logs'), exist_ok=True)
    st = load_state()
    for n in NS:
        st['n'].setdefault(str(n), {'rgen': generic_rank(n), 'stage': 1, 'd': 1, 'finished': False})
    for job in st['jobs'].values():
        job.setdefault('timeout', [])
    workers = {}          # pid -> (Popen or None (adopted), job name, worker id, t0)
    predicted = {}        # pid -> (component index, est. peak MB) until the worker's claim appears
    backfill = set()      # pids started while a larger component waited for memory
    last_start = collections.defaultdict(float)   # n -> time of its last worker start (round robin)
    bf_log, wait_t = set(), None
    try:                  # seed the round robin, the backfill set and the memory wait from the log (a restart must not reset them)
        import calendar, re
        for l in open(os.path.join(SCAN, 'runner.log')).readlines()[-3000:]:
            mm = re.match(r'(\d{4}-\d\d-\d\d \d\d:\d\d:\d\d) started worker \d+ on n(\d+)_\S+ \(pid (\d+)\)', l)
            if mm:
                last_start[int(mm.group(2))] = calendar.timegm(time.strptime(mm.group(1), '%Y-%m-%d %H:%M:%S'))
                if l.rstrip().endswith('(backfill)'):
                    bf_log.add(int(mm.group(3)))
                else:
                    wait_t = None
            mw = re.match(r'(\d{4}-\d\d-\d\d \d\d:\d\d:\d\d) memory: .* waiting', l)
            if mw and wait_t is None:
                wait_t = calendar.timegm(time.strptime(mw.group(1), '%Y-%m-%d %H:%M:%S'))
    except OSError:
        pass
    mem_wait = None
    skip_logged = {}      # job -> component logged as skipped for the reservation
    paused = set()
    mem_wait_strict = False
    strict_set = set()    # backfills running when the exception expired (only they may still keep the waiting one out)
    mem_wait_t0 = wait_t  # since when only backfilled components keep the waiting one out (bounds the backfill exception)
    # restart: adopt workers that are still running, drop claims of the dead ones
    for name, job in st['jobs'].items():
        if job['status'] != 'running':
            continue
        done = results(job['out'])
        comps = {li: lam for _, li, lam, _ in comp_list(job['n'], job['d'])}
        for fn in os.listdir(job['claims']):
            w, pid = read_claim(os.path.join(job['claims'], fn))
            if w is None or w in MARKS:
                continue
            if pid_alive(pid) and is_worker(pid):
                if pid not in workers:
                    workers[pid] = (None, name, int(w), os.path.getmtime(os.path.join(job['claims'], fn)))
                    log('restart: adopted running worker pid %d on %s' % (pid, name))
            elif comps.get(int(fn)) not in done:      # claims of finished components stay (they count as claimed)
                os.remove(os.path.join(job['claims'], fn))
                log('restart: removed stale claim %s/%s (pid %d)' % (name, fn, pid))
    backfill |= {pid for pid in workers if pid in bf_log}
    save_state(st)
    retry = {}
    wid = itertools.count(int(time.time()) % 100000 * 10)
    last_mon = last_rep = 0
    changed = True
    while True:
        now = time.time()
        # reap
        for pid, (pr, name, w, t0) in list(workers.items()):
            if pr is not None:
                rc = pr.poll()
            else:
                rc = None if pid_alive(pid) else 0
            if rc is not None:
                del workers[pid]
                backfill.discard(pid); predicted.pop(pid, None)
                if rc != 0:
                    log('worker %d (%s, pid %d) exited with %s after %.0fs' % (w, name, pid, rc, now - t0))
        alive = set(workers)
        # time limit (adjustable at run time: seconds in <SCAN>/tlimit), dead workers, job completion
        tlimit = TLIMIT
        try:
            tlimit = float(open(os.path.join(SCAN, 'tlimit')).read().split()[0])
        except (OSError, ValueError, IndexError):
            pass
        for name, job in st['jobs'].items():
            if job['status'] != 'running':
                continue
            # Only a worker's CURRENT component counts: its newest claim, and only if that component has no result
            # yet.  (Claim files of finished components stay, and the old check measured them: all nine 'timeouts'
            # before 2026-10-05 03:40 were components that had finished long before -- the worker was killed in the
            # middle of another component.)
            newest = {}
            for fn in os.listdir(job['claims']):
                path = os.path.join(job['claims'], fn)
                w, pid = read_claim(path)
                if w is None or w in MARKS or pid not in alive:
                    continue
                mt = os.path.getmtime(path)
                if pid not in newest or mt > newest[pid][0]:
                    newest[pid] = (mt, fn, path)
            if newest:
                done_now = done_lams(job)
                comps_idx = {li: lam for _, li, lam, _ in comp_list(job['n'], job['d'])}
            for pid, (mt, fn, path) in newest.items():
                age = now - mt
                if age > tlimit and comps_idx.get(int(fn)) not in done_now:
                    lam = comps_idx.get(int(fn))
                    open(path, 'w').write('timeout %d %.0f\n' % (pid, age))
                    job['timeout'].append([list(map(list, lam)), round(age)])
                    try:
                        os.kill(pid, signal.SIGTERM)
                    except OSError:
                        pass
                    log('TIMEOUT: %s %s after %.0fs (pid %d stopped; component recorded as not checked)' % (name, lam, age, pid))
                    changed = True
            for fn, lam, pid in stale_claims(job, alive):
                key = name + ':' + fn
                retry[key] = retry.get(key, 0) + 1
                os.remove(os.path.join(job['claims'], fn))
                if retry[key] >= 2:
                    job['failed'].append([list(map(list, lam)), pid])
                    open(os.path.join(job['claims'], fn), 'w').write('failed %d\n' % pid)
                    log('FAILED twice: %s %s (pid %d), marked failed' % (name, lam, pid))
                else:
                    log('worker pid %d died on %s %s: claim removed, will be retried once' % (pid, name, lam))
                changed = True
            nres = nlines(job['out'])
            if nres + len(job['failed']) + len(job['timeout']) >= job['ncomp']:
                nres = len(results(job['out']))      # distinct components (a redone component may appear twice)
            running = any(nm == name for _, nm, _, _ in workers.values())
            if nres + len(job['failed']) + len(job['timeout']) >= job['ncomp'] and not running:
                job['status'] = 'done'; job['t_end'] = now; changed = True
                _dm_cache.pop(job['n'], None)
                dm = dmin_map(st, job['n'])
                log('job %s done: %d results, %d failed, %d timeout, %.0fs; d_min now %s' % (name, nres, len(job['failed']),
                    len(job['timeout']), job['t_end'] - job['t_start'], dict(sorted(dm.items()))))
        # current job of every format; defer the other running jobs
        if changed:
            _dm_cache.clear()
        current = {advance(st, n) for n in NS} - {None}
        for name, job in st['jobs'].items():
            if job['status'] != 'running':
                continue
            if job.get('extra'):
                continue                             # hand-made reruns (own env, e.g. a larger WCAP): never deferred
            if name in current and job.get('deferred'):
                k = set_deferred(job, False); job['deferred'] = False
                log('job %s resumed (%d deferred components released)' % (name, k))
            elif name not in current and not job.get('deferred'):
                k = set_deferred(job, True); job['deferred'] = True
                log('job %s deferred (%d unclaimed components held back until n=%d returns to degree %d)' % (name, k, job['n'], job['d']))
            elif name not in current and changed:
                set_deferred(job, True)          # components freed by a dead worker go back to the deferred pile
        if changed:
            save_state(st)
            report(); last_rep = time.time()
            changed = False
        # schedule (the worker limit can be changed at run time: an integer in <SCAN>/ncores, e.g. to share the cores
        # with another agent; running components are never interrupted, the runner just starts fewer new workers)
        ncores = NCORES
        try:
            ncores = max(0, int(open(os.path.join(SCAN, 'ncores')).read().split()[0]))
        except (OSError, ValueError, IndexError):
            pass
        # paused formats (<SCAN>/pause: n values; since 2026-10-13 09:30, 10x10x10 at the user's request -- smaller
        # formats first): no new workers; running ones finish, their components stay in the job
        try:
            paused_now = {int(x) for x in open(os.path.join(SCAN, 'pause')).read().replace(',', ' ').split()}
        except (OSError, ValueError):
            paused_now = set()
        if paused_now != paused:
            log('paused formats: %s' % (sorted(paused_now) or 'none'))
            paused = paused_now
        runnable = [nm for nm, j in st['jobs'].items()
                    if j['status'] == 'running' and not j.get('deferred') and open_components(j) > 0
                    and j['n'] not in paused]
        # fair share (since 2026-10-06 18:45): a free slot goes to the format with the fewest running workers, ties to
        # the format with the fewest unchecked components left in its current degree (finishing a degree settles the
        # lowest separating degree); extra jobs (stage 0) first.  The old order (band, n) let one format's long
        # components hold every slot while other formats waited for days with a few components left in a degree.
        budget = MEMBUDGET
        try:
            budget = float(open(os.path.join(SCAN, 'membudget')).read().split()[0])
        except (OSError, ValueError, IndexError):
            pass

        extramax = 1
        try:
            extramax = int(open(os.path.join(SCAN, 'extramax')).read().split()[0])
        except (OSError, ValueError, IndexError):
            pass

        bfwait = BFWAIT
        try:
            bfwait = float(open(os.path.join(SCAN, 'bfwait')).read().split()[0])
        except (OSError, ValueError, IndexError):
            pass

        def running_est(pid):
            """estimated peak of a running worker's component (predicted until its claim appears)."""
            jb = st['jobs'][workers[pid][1]]
            li = worker_component(jb, pid)
            if li is None:
                return predicted.get(pid, (None, 0.0))[1]
            predicted.pop(pid, None)
            lm, gg = {i: (l_, g_) for _, i, l_, g_ in comp_list(jb['n'], jb['d'])}[li]
            return est_peak_mb(st, jb['n'], jb['d'], lm, gg, bool(jb.get('extra')), jb, workers[pid][3] < F32_SINCE)
        while len(workers) < ncores:
            per_n = collections.Counter(st['jobs'][nm]['n'] for _, nm, _, _ in workers.values())
            cands = []
            for name in runnable:
                job = st['jobs'][name]
                nw = sum(1 for _, nm, _, _ in workers.values() if nm == name)
                if nw >= open_components(job) or nw >= job.get('maxworkers', NCORES):
                    continue
                if job.get('extra') and sum(1 for _, nm, _, _ in workers.values() if st['jobs'][nm].get('extra')) >= extramax:
                    continue                         # extra jobs: at most <SCAN>/extramax workers at a time (default 1)
                left = left_in_degree(st, job['n'], job['d'])
                # fewest running workers first; then degrees with <= 10 components left (finishing a degree settles a
                # lowest separating degree); then round robin (the format that started a worker longest ago)
                cands.append(((job['stage'] > 0, per_n[job['n']], left > 10, last_start[job['n']], left, job['n'], job['d']), name))
            if not cands:
                break
            cands.sort()
            # memory admission: the estimated peaks of the running components plus that of the next component of the
            # job must fit the budget.  If the first job in line does not fit, it waits (nothing is skipped) and later
            # jobs may backfill, but only as long as the backfilled components together leave room for the waiting one
            # (so it fits once the other running components finish: no starvation).
            ests = {pid: running_est(pid) for pid in workers}
            used = sum(ests.values())
            bf_used = sum(v for pid, v in ests.items() if pid in backfill)
            reserve, pick, reserve_extra, blocked_nb = None, None, False, False
            for _, name in cands:
                job = st['jobs'][name]
                excl = {li for pid, (li, _) in predicted.items() if pid in workers and workers[pid][1] == name}
                nc = next_component(job, excl)
                need_mb = est_peak_mb(st, job['n'], job['d'], nc[1], nc[2], bool(job.get('extra')), job) if nc else 0.0
                if reserve is None:
                    if not workers or used + need_mb <= budget:
                        pick = (name, nc, need_mb, False)
                        break
                    # cannot start before a long-running (> LONGRUN) non-backfilled component finishes, whatever else
                    # runs: it holds no reservation, the next job in line does (since 2026-10-20 09:19: the 9.4 GB 9x9x9
                    # component, blocked by the > 1 day 8x8x8 hook rerun, kept the 4.8 GB 7x7x7 ones from ever fitting)
                    long_nb = sum(v for pid, v in ests.items() if pid not in backfill and now - workers[pid][3] > LONGRUN)
                    if long_nb + need_mb > budget:
                        if skip_logged.get(name) != nc[0]:
                            skip_logged[name] = nc[0]
                            log('memory: %s %s (~%.1f GB) cannot start before a long-running component finishes: '
                                'the next job in line holds the reservation' % (name, nc[1], need_mb / 1024))
                        continue
                    reserve = need_mb
                    reserve_extra = bool(job.get('extra'))
                    blocked_nb = used - bf_used + need_mb > budget
                    if blocked_nb:
                        # blocked by components that were not backfilled: backfills cannot delay it yet, keep cores busy
                        mem_wait_t0, mem_wait_strict, grace = None, False, True
                    else:
                        # only backfilled components keep it out: the exception ends BFWAIT s from now
                        if mem_wait_t0 is None:
                            mem_wait_t0 = time.time()
                        grace = time.time() - mem_wait_t0 < bfwait
                        if not grace and not mem_wait_strict:
                            mem_wait_strict = True
                            strict_set = {pid for pid in workers if pid in backfill}     # the backfills keeping it out now
                            log('memory: %s has been kept out by backfilled components for %.0f min: from now on only '
                                'backfills that fit beside it once those finish' % (name, (time.time() - mem_wait_t0) / 60))
                    if mem_wait != (name, nc and nc[0]):
                        mem_wait = (name, nc and nc[0])
                        log('memory: %s %s needs ~%.1f GB, running components ~%.1f GB of %.1f GB: waiting (backfill up to %.1f GB)'
                            % (name, nc and nc[1], need_mb / 1024, used / 1024, budget / 1024, max(0.0, budget - need_mb) / 1024))
                    continue
                # backfill: fits now, and leaves room for the waiting component once the others finish -- or is cheap
                # (cost band <= 3: minutes) or small (<= 4 GB), so it delays the waiting one by at most its own run time
                # (no exceptions while the waiting component belongs to an extra job: such a rerun needs most of the budget
                #  and would otherwise wait for ever behind a stream of small components; and none after it has waited
                #  BFWAIT s, since 2026-10-12: a 7.4 GB component waited behind an endless stream of small ones -- a freed
                #  slot was refilled at once, so the running estimates never dropped below budget - 7.4 GB.  The clock runs
                #  only while the non-backfilled components alone would leave room for it (since 15:52; before, a
                #  waiting component blocked by a long non-backfilled one left cores idle for hours to no effect))
                # once only backfilled components keep it out and the exception has expired, nothing more backfills:
                # the reservation rule alone (room once the non-backfilled ones finish) would let a stream of small
                # components keep it out for as long as a long non-backfilled component runs (since 19:25).  Since
                # 2026-10-18 12:46 a backfill is still admitted then if the waiting component fits beside it (and beside
                # the non-backfilled ones and the backfills admitted this way) as soon as the backfills that kept it out
                # when the exception expired have finished: it starts no later than without that backfill.  (A core sat
                # idle 1.5 h behind a 3.4 h 8x8x8 backfill although a 2.3 GB 6x6x6 component fit beside the waiting 4 GB one.)
                late_bf = sum(v for pid, v in ests.items() if pid in backfill and pid not in strict_set)
                fits_beside = (used - bf_used) + late_bf + need_mb + reserve <= budget
                # ... and while every backfill that still keeps it out has run > LONGRUN (4 h), cheap/small components
                # may backfill again: they delay it by at most their own run time once the long one finishes (since
                # 2026-10-18 19:19: a core idled behind a 10 h 8x8x8 hook component that the waiting 9x9x9 one needs gone)
                blockers = [pid for pid in strict_set if pid in workers]
                long_block = bool(blockers) and all(now - workers[pid][3] > LONGRUN for pid in blockers)
                # (while non-backfilled components block it, any size may backfill -- since 2026-10-20 07:47: the 4.8 GB
                #  7x7x7 components were starved behind the 9.4 GB 9x9x9 one, which could not start before the 8x8x8
                #  hook rerun ends in > 1 day anyway; the 30 min clock then bounds the delay once they are gone)
                if used + need_mb <= budget and ((grace and (bf_used + need_mb + reserve <= budget or
                                                             (not reserve_extra and (blocked_nb or job['stage'] <= 3 or
                                                                                     need_mb <= 4096))))
                                                 or (not grace and (fits_beside or (long_block and not reserve_extra and
                                                                                    (job['stage'] <= 3 or need_mb <= 4096))))):
                    pick = (name, nc, need_mb, True)
                    break
            if reserve is None:
                mem_wait_t0, mem_wait_strict = None, False
            if pick is None:
                break
            name, nc, need_mb, is_bf = pick
            if not is_bf:
                mem_wait, mem_wait_t0, mem_wait_strict = None, None, False
            job = st['jobs'][name]
            w = next(wid)
            env = dict(os.environ, **WENV)
            env.update({'NEED': ','.join(map(str, job['need'])), 'LIST': job['list'], 'OUT': job['out'],
                        'CLAIMDIR': job['claims'], 'RESUME': job['out'], 'WORKER': str(w), 'MAXCOMP': '1'})
            env.update(job.get('env', {}))           # per-job settings (extra jobs)
            lf = open(os.path.join(SCAN, 'logs', '%s.log' % name), 'a')
            pr = subprocess.Popen([sys.executable, '-u', 'rankscan.py', str(job['n']), str(job['d'])], env=env,
                                  stdout=lf, stderr=subprocess.STDOUT, start_new_session=True)
            workers[pr.pid] = (pr, name, w, time.time())
            last_start[job['n']] = time.time()
            if nc:
                predicted[pr.pid] = (nc[0], need_mb)
            if is_bf:
                backfill.add(pr.pid)
            log('started worker %d on %s (pid %d)%s%s' % (w, name, pr.pid, ', est. peak %.1f GB' % (need_mb / 1024) if nc else '',
                                                         ' (backfill)' if is_bf else ''))
        save_state(st)
        if all(st['n'][str(n)]['finished'] for n in NS) and not workers:
            log('all formats finished')
            report()
            break
        now = time.time()
        if now - last_mon >= MONITOR:
            m = meminfo(); cg = cgroup_mem()
            ws = ' '.join('%s:%d:%.0fMB:%.0fs' % (nm, pid, rss_mb(pid), now - t0) for pid, (_, nm, _, t0) in sorted(workers.items()))
            with open(os.path.join(SCAN, 'monitor.log'), 'a') as fh:
                fh.write('%s avail=%.0fMB cgroup=%.0fMB cgroup_peak=%.0fMB load=%s workers=%d %s\n' % (
                    time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), m.get('MemAvailable', 0), cg[0], cg[1],
                    open('/proc/loadavg').read().split()[0], len(workers), ws))
            last_mon = now
        if now - last_rep >= REPORT:
            try:
                if refresh_extra_lists(st):
                    save_state(st)
            except Exception as e:                       # never let the bookkeeping stop the runner
                log('refresh_extra_lists failed: %r' % (e,))
            report(); last_rep = now
        time.sleep(3)


if __name__ == '__main__':
    main()
