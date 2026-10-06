"""python3 scan_runner.py            (start with: setsid nohup python3 -u scan_runner.py >> scan/live/runner.log 2>&1 &)

Orchestrates rankscan.py over the formats n x n x n (n in NS) and degrees d = 1..DMAX, see SCAN.md.

Job (n, d, stage) covers the components of degree d whose cost proxy lies in (CAPS[stage-1], CAPS[stage]] and
resolves the ranks NEED = {r < r_gen : no separator of r vs r+1 is known in a degree < d, r not skipped}.
Per format the jobs are run in the order (d, stage): degree d is completed in every cost band before degree d + 1
is started (that is what the lowest separating degree needs); degrees above d_min(target rank) are not run (target
= r_gen - 1 unless skipped in state.json).  Across formats, a free worker slot goes to the format with the fewest
running workers, ties to the one with the fewest unchecked components left in its current degree (fair share; before
2026-10-06 18:30: the order (stage, n)).  A worker is started only if the estimated peak memory of the component it
will take plus that of the running components fits MEMBUDGET MB (<SCAN>/membudget overrides); otherwise no worker is
started until enough memory is free (the next component waits, it is not skipped).  A component running longer than TLIMIT seconds is stopped and recorded as 'timeout' (not checked,
listed in the report).  Running jobs that are not the current job of their format (after a change of the ordering)
are 'deferred': their unclaimed components get a placeholder claim so that no worker takes them, until the format
reaches that job again.  On a restart, workers that are still running are adopted (not killed).
A resource line (memory, per-worker RSS, load) goes to <SCAN>/monitor.log every MONITOR s, and scan_report.py writes
<SCAN>/STATUS.md after every job and every REPORT s.  State: <SCAN>/state.json (SCAN = scan/live, untracked;
scan_autosave.sh copies everything into scan/ and commits)."""
import os, sys, json, time, subprocess, itertools, signal, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rankscan import generic_rank, components, cost_proxy, is_onerow
from hwv import dim_schur

NS = [int(x) for x in os.environ.get('NS', '3,4,5,6,7,8,9,10').split(',')]
DMAX = int(os.environ.get('DMAX', '10'))
NCORES = int(os.environ.get('NCORES', '4'))
CAPS = [0] + [float(x) for x in os.environ.get('CAPS', '3e5,3e6,3e7,3e8,3e9').split(',')]
TLIMIT = float(os.environ.get('TLIMIT', '7200'))
MEMBUDGET = float(os.environ.get('MEMBUDGET', '15000'))     # MB for the workers (container: 16 GB, no swap)
MONITOR = int(os.environ.get('MONITOR', '300'))
REPORT = int(os.environ.get('REPORT', '900'))
SCAN = os.environ.get('SCAN', 'scan/live')
STATE = os.path.join(SCAN, 'state.json')
WENV = {'OPENBLAS_NUM_THREADS': '1', 'OMP_NUM_THREADS': '1', 'PYTHONDONTWRITEBYTECODE': '1'}
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


def mat_parts(n, lam, g):
    """per direction: (MB of the g evaluated flattenings N1 x K (float32 above 2^26 entries), MB of the combination
    phi and the H and V eliminations: 8 (N1 K + N1^2 + K^2))."""
    out = []
    for t in range(3):
        a = lam[t]; b, c = [lam[u] for u in range(3) if u != t]
        n1 = dim_schur(a, n); n23 = dim_schur(b, n) * dim_schur(c, n)
        N1 = min(n1, g * n23) + 8; K = min(g * n1, n23) + 8
        el = g * N1 * K
        out.append((el * (8 if el <= (1 << 26) else 4) / 2.0 ** 20, 8.0 * (N1 * K + N1 * N1 + K * K) / 2.0 ** 20))
    return out


def eval_phase_mb(st, n, d):
    """memory of the evaluation phase beyond the flattenings (word minors, contraction blocks), calibrated on the
    recorded peaks of degree d of format n: max over its network components of peak RSS - flattenings (an upper
    bound, since it also absorbs elimination-dominated peaks), + 512 MB margin; 4 GB until 5 records exist (the largest
    excess over all 2363 records of 2026-10-06 was 3.8 GB).  Refreshed every 15 min."""
    c = _calib.get((n, d))
    if c is not None and time.time() - c[0] < 900:
        return c[1]
    vals = []
    for j in st['jobs'].values():
        if j['n'] != n or j['d'] != d or j.get('extra') or not os.path.exists(j['out']):
            continue
        for l in open(j['out']):
            try:
                r = json.loads(l)
            except ValueError:
                continue
            if any(x.get('method') == 'onerow' for x in r['dirs']):
                continue
            lam = tuple(tuple(x) for x in r['lam'])
            vals.append(r['rss_peak_mb'] - max(fs for fs, _ in mat_parts(n, lam, r['g'])))
    v = max(vals) + 512 if len(vals) >= 5 else 4096.0
    _calib[(n, d)] = (time.time(), v)
    return v


def est_peak_mb(st, n, d, lam, g, extra=False):
    """estimated peak RSS of a worker on component lam (MB): two phases -- evaluation (flattenings + word minors and
    contraction blocks, eval_phase_mb) and elimination (flattenings + phi + eliminations) -- of its largest
    direction, + 800 MB (300 MB was 130 MB short on 8x8x8 ((3,2,1),(3,2,1),(3,1,1,1)): 6785 MB).  Checked against the recorded components: no peak above its estimate (one-row
    components, closed form: 3.5 GB; extra jobs with WCAP 2^28: + 4 GB)."""
    if is_onerow(lam):
        return 3584.0                     # largest recorded one-row peak: 3.0 GB (9x9x9 d = 6)
    key = (n, lam, g)
    if key not in _est_cache:
        _est_cache[key] = mat_parts(n, lam, g)
    B = eval_phase_mb(st, n, d)
    return max(fs + max(B, m) for fs, m in _est_cache[key]) + 800 + (4096 if extra else 0)


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
    mem_wait = None
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
        runnable = [nm for nm, j in st['jobs'].items()
                    if j['status'] == 'running' and not j.get('deferred') and open_components(j) > 0]
        # fair share (since 2026-10-06 18:45): a free slot goes to the format with the fewest running workers, ties to
        # the format with the fewest unchecked components left in its current degree (finishing a degree settles the
        # lowest separating degree); extra jobs (stage 0) first.  The old order (band, n) let one format's long
        # components hold every slot while other formats waited for days with a few components left in a degree.
        while len(workers) < ncores:
            per_n = collections.Counter(st['jobs'][nm]['n'] for _, nm, _, _ in workers.values())
            best = None
            for name in runnable:
                job = st['jobs'][name]
                nw = sum(1 for _, nm, _, _ in workers.values() if nm == name)
                if nw >= open_components(job) or nw >= job.get('maxworkers', NCORES):
                    continue
                if job.get('extra') and sum(1 for _, nm, _, _ in workers.values() if st['jobs'][nm].get('extra')) >= 1:
                    continue                         # extra jobs use much memory: one worker at a time over all of them
                key = (job['stage'] > 0, per_n[job['n']], left_in_degree(st, job['n'], job['d']), job['n'], job['d'])
                if best is None or key < best[0]:
                    best = (key, name)
            if best is None:
                break
            name = best[1]
            job = st['jobs'][name]
            # memory admission: estimated peaks of the running components (predicted ones for workers that have not
            # claimed yet) plus the next component of this job must fit the budget; else wait (nothing is skipped)
            budget = MEMBUDGET
            try:
                budget = float(open(os.path.join(SCAN, 'membudget')).read().split()[0])
            except (OSError, ValueError, IndexError):
                pass
            used = 0.0
            for pid, (_, nm, _, _) in workers.items():
                jb = st['jobs'][nm]
                li = worker_component(jb, pid)
                if li is not None:
                    predicted.pop(pid, None)
                    lam_g = {i: (lm, gg) for _, i, lm, gg in comp_list(jb['n'], jb['d'])}[li]
                    used += est_peak_mb(st, jb['n'], jb['d'], lam_g[0], lam_g[1], bool(jb.get('extra')))
                elif pid in predicted:
                    used += predicted[pid][1]
            excl = {li for pid, (li, _) in predicted.items() if pid in workers and workers[pid][1] == name}
            nc = next_component(job, excl)
            need_mb = est_peak_mb(st, job['n'], job['d'], nc[1], nc[2], bool(job.get('extra'))) if nc else 0.0
            if workers and used + need_mb > budget:
                if mem_wait != (name, nc and nc[0]):
                    mem_wait = (name, nc and nc[0])
                    log('memory: %s %s needs ~%.1f GB, running components ~%.1f GB of %.1f GB: waiting for a worker to finish'
                        % (name, nc and nc[1], need_mb / 1024, used / 1024, budget / 1024))
                break
            mem_wait = None
            w = next(wid)
            env = dict(os.environ, **WENV)
            env.update({'NEED': ','.join(map(str, job['need'])), 'LIST': job['list'], 'OUT': job['out'],
                        'CLAIMDIR': job['claims'], 'RESUME': job['out'], 'WORKER': str(w), 'MAXCOMP': '1'})
            env.update(job.get('env', {}))           # per-job settings (extra jobs)
            lf = open(os.path.join(SCAN, 'logs', '%s.log' % name), 'a')
            pr = subprocess.Popen([sys.executable, '-u', 'rankscan.py', str(job['n']), str(job['d'])], env=env,
                                  stdout=lf, stderr=subprocess.STDOUT, start_new_session=True)
            workers[pr.pid] = (pr, name, w, time.time())
            if nc:
                predicted[pr.pid] = (nc[0], need_mb)
            log('started worker %d on %s (pid %d)%s' % (w, name, pr.pid, ', est. peak %.1f GB' % (need_mb / 1024) if nc else ''))
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
            report(); last_rep = now
        time.sleep(3)


if __name__ == '__main__':
    main()
