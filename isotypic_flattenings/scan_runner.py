"""python3 scan_runner.py            (start with: setsid nohup python3 -u scan_runner.py >> scan/live/runner.log 2>&1 &)

Orchestrates rankscan.py over the formats n x n x n (n in NS) and degrees d = 1..DMAX, see SCAN.md.

For each n the degrees are run in increasing order; job (n, d, stage) covers the components of degree d whose cost
proxy lies in (CAPS[stage-1], CAPS[stage]] and resolves the ranks NEED = {r < r_gen : no separator of r vs r+1 is
known in a degree < d}.  After a job, d_min(r) (lowest degree with a separator) is recomputed from all results;
stage s of n stops after degree d once r_gen - 1 is separated in degree <= d, or at DMAX.  Stage s + 1 then goes
through the degrees again (up to the current d_min(r_gen - 1)) with the next cost band, so that cheap components of
all n come first.  Jobs are scheduled on NCORES worker processes, priority (stage, d, n); a job's workers claim its
components dynamically.  A resource line (memory, per-worker RSS, load) goes to <SCAN>/monitor.log every MONITOR s,
and scan_report.py writes <SCAN>/STATUS.md after every job and every REPORT s.  The state is in <SCAN>/state.json
(SCAN = scan/live, untracked; scan_autosave.sh copies everything into scan/ and commits); a
restart continues from the result files (stale claims of dead workers are removed)."""
import os, sys, json, time, subprocess, itertools, signal
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rankscan import generic_rank, components, cost_proxy

NS = [int(x) for x in os.environ.get('NS', '3,4,5,6,7,8,9,10').split(',')]
DMAX = int(os.environ.get('DMAX', '10'))
NCORES = int(os.environ.get('NCORES', '4'))
CAPS = [0] + [float(x) for x in os.environ.get('CAPS', '3e5,3e6,3e7,3e8,3e9').split(',')]
MONITOR = int(os.environ.get('MONITOR', '300'))
REPORT = int(os.environ.get('REPORT', '900'))
SCAN = os.environ.get('SCAN', 'scan/live')        # live files (untracked); scan_autosave.sh snapshots them into scan/
STATE = os.path.join(SCAN, 'state.json')
WENV = {'OPENBLAS_NUM_THREADS': '1', 'OMP_NUM_THREADS': '1', 'PYTHONDONTWRITEBYTECODE': '1'}


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
    """r -> lowest degree with a separator, over all finished and running jobs of n (cached until a job changes)."""
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


def make_job(st, n, d, stage):
    """create job (n, d, stage); returns its name, or None if it has nothing to do."""
    ns = st['n'][str(n)]
    rgen = ns['rgen']
    dm = dmin_map(st, n)
    need = [r for r in range(1, rgen) if dm.get(r, 99) >= d]
    name = 'n%d_d%d_s%d' % (n, d, stage)
    if not need:
        return None
    lo, hi = CAPS[stage - 1], CAPS[stage]
    comps = sorted(c for c in comp_list(n, d) if lo < c[0] <= hi)
    total = len(comp_list(n, d))
    if not comps:
        return None
    os.makedirs(os.path.join(SCAN, 'jobs'), exist_ok=True)
    lst = os.path.join(SCAN, 'jobs', name + '.txt')
    with open(lst, 'w') as fh:
        for c in comps:
            fh.write(repr(c[2]) + '\n')
    st['jobs'][name] = {'n': n, 'd': d, 'stage': stage, 'need': need, 'list': lst, 'ncomp': len(comps),
                        'ncomp_degree': total, 'cap': [lo, hi], 'out': os.path.join(SCAN, 'res', name + '.jsonl'),
                        'claims': os.path.join(SCAN, 'claims', name), 'status': 'running',
                        't_start': time.time(), 'failed': []}
    os.makedirs(os.path.join(SCAN, 'res'), exist_ok=True)
    os.makedirs(st['jobs'][name]['claims'], exist_ok=True)
    log('job %s created: %d components (cost %.0e..%.0e of %d in degree %d), need=%s' % (name, len(comps), lo, hi, total, d, need))
    return name


def advance(st, n):
    """create the next job of n (possibly skipping empty ones); marks n finished when nothing is left."""
    ns = st['n'][str(n)]
    while not ns['finished']:
        rgen = ns['rgen']
        dm = dmin_map(st, n)
        dtop = min(DMAX, dm.get(rgen - 1, 99))         # degrees beyond d_min(r_gen - 1) are not needed
        if ns['d'] > dtop:
            if ns['stage'] + 1 >= len(CAPS):
                ns['finished'] = True; log('n=%d finished (all stages)' % n); break
            ns['stage'] += 1; ns['d'] = 1
            log('n=%d: stage %d (cost band %.0e..%.0e), degrees up to %d' % (n, ns['stage'], CAPS[ns['stage'] - 1], CAPS[ns['stage']], dtop))
            continue
        name = 'n%d_d%d_s%d' % (n, ns['d'], ns['stage'])
        if name in st['jobs']:
            if st['jobs'][name]['status'] == 'running':
                return name
            ns['d'] += 1; continue
        name = make_job(st, n, ns['d'], ns['stage'])
        if name is None:
            ns['d'] += 1; continue
        return name
    return None


def claimed(job):
    try:
        return len(os.listdir(job['claims']))
    except FileNotFoundError:
        return 0


def pid_alive(pid):
    try:
        os.kill(pid, 0)
        return True
    except OSError:
        return False


def clean_stale_claims(job, alive_pids):
    """remove claims of dead workers whose component has no result (it will be redone, or marked failed)."""
    dead = []
    for fn in os.listdir(job['claims']):
        try:
            w, pid = open(os.path.join(job['claims'], fn)).read().split()[:2]
            pid = int(pid)
        except (ValueError, OSError):
            continue
        if w != 'failed' and pid not in alive_pids:
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


def main():
    os.makedirs(os.path.join(SCAN, 'logs'), exist_ok=True)
    st = load_state()
    for n in NS:
        st['n'].setdefault(str(n), {'rgen': generic_rank(n), 'stage': 1, 'd': 1, 'finished': False})
    # restart: drop claims of components without a result (their workers are gone)
    retry = {}
    for name, job in st['jobs'].items():
        if job['status'] == 'running':
            for fn, lam, pid in clean_stale_claims(job, set()):
                os.remove(os.path.join(job['claims'], fn))
                log('restart: removed stale claim %s %s (pid %d)' % (name, lam, pid))
    save_state(st)
    workers = {}          # pid -> (Popen, job name, worker id, t0)
    wid = itertools.count(int(time.time()) % 100000 * 10)
    last_mon = last_rep = 0
    while True:
        # reap
        for pid, (pr, name, w, t0) in list(workers.items()):
            rc = pr.poll()
            if rc is not None:
                del workers[pid]
                if rc != 0:
                    log('worker %d (%s, pid %d) exited with %s after %.0fs' % (w, name, pid, rc, time.time() - t0))
        alive = set(workers)
        # job completion / failures
        changed = False
        for name, job in st['jobs'].items():
            if job['status'] != 'running':
                continue
            for fn, lam, pid in clean_stale_claims(job, alive):
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
            running = any(nm == name for _, nm, _, _ in workers.values())
            if nres + len(job['failed']) >= job['ncomp'] and not running:
                job['status'] = 'done'; job['t_end'] = time.time(); changed = True
                _dm_cache.pop(job['n'], None)
                dm = dmin_map(st, job['n'])
                log('job %s done: %d results, %d failed, %.0fs; d_min now %s' % (name, nres, len(job['failed']),
                    job['t_end'] - job['t_start'], dict(sorted(dm.items()))))
        if changed:
            _dm_cache.clear()
            for n in NS:
                advance(st, n)
            save_state(st)
            subprocess.run([sys.executable, 'scan_report.py'], env=dict(os.environ, SCAN=SCAN, **WENV))
            last_rep = time.time()
        # schedule
        for n in NS:
            advance(st, n)
        runnable = sorted((j['stage'], j['d'], j['n'], nm) for nm, j in st['jobs'].items()
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
            subprocess.run([sys.executable, 'scan_report.py'], env=dict(os.environ, SCAN=SCAN, **WENV))
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
            subprocess.run([sys.executable, 'scan_report.py'], env=dict(os.environ, SCAN=SCAN, **WENV))
            last_rep = now
        time.sleep(3)


if __name__ == '__main__':
    main()
