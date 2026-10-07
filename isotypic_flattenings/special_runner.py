"""python3 special_runner.py JOBFILE       (background: setsid nohup python3 -u special_runner.py special/jobs.txt >> special/runner.log 2>&1 &)

Runs specialscan.py jobs, one process per component, at most NCORES at a time (read every 10 s from
special/live/ncores, default 4), in the order of JOBFILE.  JOBFILE lines: `[KEY=VALUE ...] n d R methods...` (all components with
g >= 2 of degree d, cheapest first by rankscan.cost_proxy) or `n d R methods... :: lam` (one component).
Output of a job: special/live/res/n<n>_d<d>_s<slot>.jsonl and special/live/logs/n<n>_d<d>_s<slot>.log (slot = pool
slot, so that no two running processes append to one file; special/live is not tracked: special/sync.sh copies it
to special/res, special/logs and commits).  Resume: a component is skipped when every distinct direction has a
record with the same ranks and methods in some special/live/res/n<n>_d<d>*.jsonl.  A job running longer than
TLIMIT seconds (special/live/tlimit, default 10800) is killed and listed in special/runner.log as 'timeout'.
EXCLUSIVE=1 jobs run alone (the queue is drained when one comes first).  Memory guard: at most special/live/maxbig (default 2) jobs with some direction of max(N1, K) > 6000 or
g N1 K > 5e7 run at once (the queue skips ahead to small jobs), and a job starts only while MemAvailable >=
special/live/minfree MB (default 5000) or nothing runs."""
import os, sys, time, json, glob, subprocess, signal
import rankscan
from rankscan import distinct_dirs, cost_proxy

LIVE = 'special/live'


def read_int(path, default):
    try:
        return int(open(path).read().strip())
    except (OSError, ValueError):
        return default


def parse_R(s):
    return list(range(int(s.split('-')[0]), int(s.split('-')[1]) + 1)) if '-' in s else [int(x) for x in s.split(',')]


def done_set(n, d):
    out = set()
    for f in glob.glob('special/live/res/n%d_d%d*.jsonl' % (n, d)):
        for l in open(f):
            try:
                r = json.loads(l)
            except ValueError:
                continue
            out.add((tuple(tuple(x) for x in r['lam']), r['t'], tuple(r['r']), tuple(r['methods'])))
    return out


def mem_available_mb():
    try:
        for l in open('/proc/meminfo'):
            if l.startswith('MemAvailable'):
                return int(l.split()[1]) // 1024
    except OSError:
        pass
    return 10 ** 9


def is_big(n, lam):
    """a job that can need several GB: some direction with max(N1, K) > 6000 or g N1 K > 5e7 (rankscan sampling)."""
    from hwv import dim_schur
    from isoflat import kronecker
    g = kronecker(*lam)
    dims = [dim_schur(l, n) for l in lam]
    for t in distinct_dirs(lam):
        n1 = dims[t]; n23 = dims[(t + 1) % 3] * dims[(t + 2) % 3]
        N1, K = min(n1, g * n23) + 8, min(g * n1, n23) + 8
        if max(N1, K) > 6000 or g * N1 * K > 5e7:
            return True
    return False


def external_jobs(own_pids):
    """jobs of specialscan.py processes not started by this runner (e.g. left by a restarted runner)."""
    out = set()
    for d in os.listdir('/proc'):
        if not d.isdigit() or int(d) in own_pids:
            continue
        try:
            a = open('/proc/%s/cmdline' % d, 'rb').read().decode().split('\0')
        except OSError:
            continue
        if len(a) > 6 and a[1] == '-u' and a[2] == 'specialscan.py':
            try:
                out.add((int(a[3]), int(a[4]), a[6], tuple(x for x in a[7:] if x), tuple(tuple(x) for x in eval(a[5]))))
            except Exception:
                pass
    return out


def expand(jobfile):
    """jobs in priority order.  A job named by a '::' line takes that line's position and environment; general lines
    skip it."""
    entries = []
    for line in open(jobfile):
        line = line.split('#')[0].strip()
        if not line:
            continue
        if '::' in line:
            head, lam = line.split('::')
            lams = [tuple(tuple(x) for x in eval(lam.strip()))]
        else:
            head, lams = line, None
        f = head.split()
        env = {}
        while f and '=' in f[0]:                 # leading KEY=VALUE tokens: environment of these jobs
            k, v = f.pop(0).split('=', 1)
            env[k] = v
        entries.append((env, int(f[0]), int(f[1]), f[2], tuple(f[3:]), lams))
    specific = {(n, d, Rs, m, lams[0]) for env, n, d, Rs, m, lams in entries if lams is not None}
    jobs, seen = [], set()
    for env, n, d, Rs, methods, lams in entries:
        general = lams is None
        if general:
            comps = [(lam, g) for _, lam, g in rankscan.components(n, d) if g >= 2]
            comps.sort(key=lambda c: cost_proxy(n, c[0], c[1]))
            lams = [lam for lam, _ in comps]
        for lam in lams:
            job = (n, d, Rs, methods, lam)
            if job in seen or (general and job in specific):
                continue
            seen.add(job)
            jobs.append(job)
            if env:
                JOBENV[job] = env
    return jobs


JOBENV = {}


def main():
    jobfile = sys.argv[1]
    os.makedirs(LIVE, exist_ok=True)
    os.makedirs('special/live/res', exist_ok=True)
    os.makedirs('special/live/logs', exist_ok=True)
    running = {}            # slot -> (proc, job, t0)
    # slots (output file suffixes) of this runner; above the ones of jobs left by a previous runner
    slot0 = 4 if external_jobs(set()) else 0
    pending = None
    print('# runner start %s' % time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), flush=True)
    while True:
        # re-read the job file every round (jobs can be appended while running)
        jobs = expand(jobfile)
        cache = {}
        todo = []
        ext = external_jobs({proc.pid for proc, _, _ in running.values()})
        active = set(j for _, j, _ in running.values()) | ext
        for job in jobs:
            n, d, Rs, methods, lam = job
            if job in active:
                continue
            if (n, d) not in cache:
                cache[(n, d)] = done_set(n, d)
            R = tuple(parse_R(Rs))
            if all((lam, t, R, methods) in cache[(n, d)] for t in distinct_dirs(lam)):
                continue
            if (n, d, Rs, methods, lam) in getattr(main, 'failed', set()):
                continue
            todo.append(job)
        ncores = read_int(os.path.join(LIVE, 'ncores'), 4)
        tlimit = read_int(os.path.join(LIVE, 'tlimit'), 10800)
        # reap
        for slot, (proc, job, t0) in list(running.items()):
            if proc.poll() is not None:
                print('%s done  slot %d rc %s %.0fs  %s' % (time.strftime('%H:%M:%S'), slot, proc.returncode, time.time() - t0, job), flush=True)
                if proc.returncode != 0:
                    main.failed = getattr(main, 'failed', set()) | {job}
                del running[slot]
            elif time.time() - t0 > tlimit:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
                print('%s TIMEOUT slot %d %.0fs  %s' % (time.strftime('%H:%M:%S'), slot, time.time() - t0, job), flush=True)
                main.failed = getattr(main, 'failed', set()) | {job}
                del running[slot]
        # launch
        todo = [j for j in todo if j not in set(jj for _, jj, _ in running.values())]
        nbig = sum(1 for j in [jj for _, jj, _ in running.values()] + list(ext) if is_big(j[0], j[4]))   # after reaping
        while todo and len(running) + len(ext) < ncores:
            # memory guard: at most MAXBIG jobs that can need several GB, and >= MINFREE MB available
            if running and mem_available_mb() < read_int(os.path.join(LIVE, 'minfree'), 5000):
                break
            # EXCLUSIVE jobs (huge memory) run alone: nothing starts while one runs; when one is the first runnable
            # job, the others are drained first
            if any(JOBENV.get(j, {}).get('EXCLUSIVE') for j in [jj for _, jj, _ in running.values()] + list(ext)):
                break
            k = next((i for i, j in enumerate(todo) if JOBENV.get(j, {}).get('EXCLUSIVE') or not is_big(j[0], j[4])
                      or nbig < read_int(os.path.join(LIVE, 'maxbig'), 2)), None)
            if k is None:
                break
            if JOBENV.get(todo[k], {}).get('EXCLUSIVE') and (running or ext):
                break
            job = todo.pop(k)
            nbig += is_big(job[0], job[4])
            slot = min(set(range(slot0, slot0 + 16)) - set(running))
            n, d, Rs, methods, lam = job
            env = dict(os.environ, **JOBENV.get(job, {}))
            env = dict(env, OPENBLAS_NUM_THREADS='1', OMP_NUM_THREADS='1',
                       OUT='special/live/res/n%d_d%d_s%d.jsonl' % (n, d, slot), DONEGLOB='special/live/res')
            logf = open('special/live/logs/n%d_d%d_s%d.log' % (n, d, slot), 'a')
            proc = subprocess.Popen(['python3', '-u', 'specialscan.py', str(n), str(d), repr(lam), Rs] + list(methods),
                                    stdout=logf, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL, env=env,
                                    start_new_session=True)
            running[slot] = (proc, job, time.time())
            print('%s start slot %d  %s' % (time.strftime('%H:%M:%S'), slot, job), flush=True)
        if not running and not todo and not ext:
            print('# runner: nothing left %s' % time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), flush=True)
            break
        time.sleep(10)


if __name__ == '__main__':
    main()
