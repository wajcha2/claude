"""python3 scan_runner.py            (start with: setsid nohup python3 -u scan_runner.py >> scan/live/runner.log 2>&1 &)

Orchestrates rankscan.py over the formats n x n x n (n in NS) and degrees d = 1..DMAX, see SCAN.md.

Job (n, d, stage) covers the components of degree d whose cost proxy lies in (CAPS[stage-1], CAPS[stage]] and
resolves the ranks NEED = {r < r_gen : no separator of r vs r+1 is known in a degree < d, r not skipped}.
Per format the jobs are run in the order (d, stage): degree d is completed in every cost band before degree d + 1
is started (that is what the lowest separating degree needs); degrees above d_min(target rank) are not run (target
= r_gen - 1 unless skipped in state.json).  Across formats, workers go to the runnable jobs in the order
(stage, n): cheap bands first, small formats first.  A component running longer than TLIMIT seconds is stopped and recorded as 'timeout' (not checked,
listed in the report).  Running jobs that are not the current job of their format (after a change of the ordering)
are 'deferred': their unclaimed components get a placeholder claim so that no worker takes them, until the format
reaches that job again.  On a restart, workers that are still running are adopted (not killed).
A resource line (memory, per-worker RSS, load) goes to <SCAN>/monitor.log every MONITOR s, and scan_report.py writes
<SCAN>/STATUS.md after every job and every REPORT s.  State: <SCAN>/state.json (SCAN = scan/live, untracked;
scan_autosave.sh copies everything into scan/ and commits)."""
import os, sys, json, time, subprocess, itertools, signal
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rankscan import generic_rank, components, cost_proxy

NS = [int(x) for x in os.environ.get('NS', '3,4,5,6,7,8,9,10').split(',')]
DMAX = int(os.environ.get('DMAX', '10'))
NCORES = int(os.environ.get('NCORES', '4'))
CAPS = [0] + [float(x) for x in os.environ.get('CAPS', '3e5,3e6,3e7,3e8,3e9').split(',')]
TLIMIT = float(os.environ.get('TLIMIT', '7200'))
MONITOR = int(os.environ.get('MONITOR', '300'))
REPORT = int(os.environ.get('REPORT', '900'))
SCAN = os.environ.get('SCAN', 'scan/live')
STATE = os.path.join(SCAN, 'state.json')
WENV = {'OPENBLAS_NUM_THREADS': '1', 'OMP_NUM_THREADS': '1', 'PYTHONDONTWRITEBYTECODE': '1'}
MARKS = ('failed', 'deferred', 'timeout')       # claim files that are not held by a worker


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
    # restart: adopt workers that are still running, drop claims of the dead ones
    for name, job in st['jobs'].items():
        if job['status'] != 'running':
            continue
        for fn in os.listdir(job['claims']):
            w, pid = read_claim(os.path.join(job['claims'], fn))
            if w is None or w in MARKS:
                continue
            if pid_alive(pid) and is_worker(pid):
                if pid not in workers:
                    workers[pid] = (None, name, int(w), os.path.getmtime(os.path.join(job['claims'], fn)))
                    log('restart: adopted running worker pid %d on %s' % (pid, name))
            else:
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
        # time limit, dead workers, job completion
        for name, job in st['jobs'].items():
            if job['status'] != 'running':
                continue
            for fn in os.listdir(job['claims']):
                path = os.path.join(job['claims'], fn)
                w, pid = read_claim(path)
                if w is None or w in MARKS or pid not in alive:
                    continue
                age = now - os.path.getmtime(path)
                if age > TLIMIT:
                    lam = {li: lam for _, li, lam, _ in comp_list(job['n'], job['d'])}.get(int(fn))
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
        # schedule
        runnable = sorted((j['stage'], j['n'], j['d'], nm) for nm, j in st['jobs'].items()
                          if j['status'] == 'running' and claimed(j) < j['ncomp'])
        for _, _, _, name in runnable:
            if len(workers) >= NCORES:
                break
            job = st['jobs'][name]
            nw = sum(1 for _, nm, _, _ in workers.values() if nm == name)
            if nw >= job['ncomp'] - claimed(job):
                continue
            w = next(wid)
            env = dict(os.environ, **WENV)
            env.update({'NEED': ','.join(map(str, job['need'])), 'LIST': job['list'], 'OUT': job['out'],
                        'CLAIMDIR': job['claims'], 'RESUME': job['out'], 'WORKER': str(w)})
            lf = open(os.path.join(SCAN, 'logs', '%s.log' % name), 'a')
            pr = subprocess.Popen([sys.executable, '-u', 'rankscan.py', str(job['n']), str(job['d'])], env=env,
                                  stdout=lf, stderr=subprocess.STDOUT, start_new_session=True)
            workers[pr.pid] = (pr, name, w, time.time())
            log('started worker %d on %s (pid %d)' % (w, name, pr.pid))
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
