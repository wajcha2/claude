"""d9_jobs.py (copy of combined/comb_jobs.py: logs in combined_d9/logs/jobs, cache combined_d9/live/cache) -- run a list of comb_search.py jobs on N workers, resumable after container restarts.

usage: python3 comb_jobs.py JOBFILE [NWORKERS]        (detach with setsid nohup; rerun the same command after a restart)
JOBFILE: one job per line, 'name | comb_search arguments' ('#' comments), in priority order; it is re-read every
cycle, so jobs can be added or reordered while the runner works.  Job `name` writes logs/jobs/<name>_partK.log
(K = 1, 2, ... one part per launch); a relaunch passes --resume over all earlier parts.  A job is done when one of its
parts has the final summary line (' total ').  A job whose comb_search process is already running (started by an
earlier runner: found in /proc by its command line) counts as running and takes a slot, so restarting the runner never
duplicates work.  Status: logs/jobs/runner.status.

Memory budget (2026-11-02, after an OOM loop: the cgroup limit is 14.3 GB and one 4x5x5 dir-1 lattice of size 19588
needs > 6.3 GB): `name @GB | args` gives a job's expected peak memory (default 2 GB).  A job is launched only when
sum over running jobs of max(hint, current RSS) + its hint <= BUDGET_GB (argv[3], default 13.5).  A job blocked by
memory lets later jobs start only when their hint is <= 2 GB.  With nothing running, the first waiting job starts.  A job of this runner killed by SIGKILL (the OOM killer)
gets hint max(hint, 1.25 x its peak RSS), kept in logs/jobs/memhints.json.

usage: python3 d9_jobs.py JOBFILE [NWORKERS [BUDGET_GB]]"""
import os, sys, re, time, subprocess, glob, json
HERE = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'combined')   # comb_search.py lives there
MINE = os.path.dirname(os.path.abspath(__file__))
JOBDIR = os.path.join(MINE, 'logs', 'jobs')
CACHE = os.path.join(MINE, 'live', 'cache')
jobfile, nworkers = sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 4
budget = float(sys.argv[3]) if len(sys.argv) > 3 else 13.5
HINTS = os.path.join(JOBDIR, 'memhints.json')
SMALL = 2.0
os.makedirs(JOBDIR, exist_ok=True)

def read_jobs():
    jobs = []
    for l in open(jobfile):
        l = l.split('#')[0].strip()
        if l:
            name, a = [x.strip() for x in l.split('|', 1)]
            m = re.match(r'(\S+)\s*(?:@([\d.]+))?$', name)
            name, hint = m.group(1), float(m.group(2) or 2.0)
            jobs.append((name, ' '.join(a.split())))
            hints[name] = max(hint, learned.get(name, 0.0))
    return jobs

def rss_gb(pid):
    try:
        for l in open('/proc/%d/status' % pid):
            if l.startswith('VmRSS:'):
                return int(l.split()[1]) / 2**20
    except OSError:
        pass
    return 0.0

def parts(name):
    return sorted(glob.glob(os.path.join(JOBDIR, '%s_part*.log' % name)), key=lambda f: int(re.search(r'_part(\d+)\.log$', f).group(1)))

def done(name):
    return any(' total ' in l and l.startswith('n=') for f in parts(name) for l in open(f))

def external(jobs, own_pids):
    """jobs whose comb_search process runs outside this runner (matched by 'comb_search.py <args>' in /proc)."""
    out = {}
    for d in glob.glob('/proc/[0-9]*'):
        if int(d[6:]) in own_pids:
            continue
        try:
            cmd = open(d + '/cmdline', 'rb').read().replace(b'\0', b' ').decode(errors='replace')
        except OSError:
            continue
        if 'comb_search.py' not in cmd:
            continue
        for name, a in jobs:
            if ('comb_search.py ' + a + ' ') in cmd + ' ':
                out[name] = int(d[6:])
    return out

running = {}
hints, peak = {}, {}
try:
    learned = json.load(open(HINTS))
except (OSError, ValueError):
    learned = {}
env = dict(os.environ, OPENBLAS_NUM_THREADS='1', PYTHONDONTWRITEBYTECODE='1')
while True:
    jobs = read_jobs()
    for name in [n for n, pr in running.items() if pr.poll() is not None]:
        if running[name].returncode == -9 and not done(name):        # OOM killer: remember the memory it reached
            learned[name] = round(max(hints.get(name, 2.0), 1.25 * peak.get(name, 0.0)), 2)
            json.dump(learned, open(HINTS, 'w'), indent=1)
            hints[name] = max(hints.get(name, 2.0), learned[name])
        del running[name]
        peak.pop(name, None)
    ext = external(jobs, {pr.pid for pr in running.values()})
    pids = dict(ext, **{n: pr.pid for n, pr in running.items()})
    for n, pid in pids.items():
        peak[n] = max(peak.get(n, 0.0), rss_gb(pid))
    busy = set(running) | set(ext)
    reserved = sum(max(hints.get(n, 2.0), rss_gb(pid)) for n, pid in pids.items())
    blocked = []
    for name, a in jobs:
        if len(busy) >= nworkers:
            break
        if name in busy or done(name):
            continue
        if busy and (reserved + hints[name] > budget or (blocked and hints[name] > SMALL)):   # alone, any job may run
            blocked.append(name)
            continue
        reserved += hints[name]
        ps = parts(name)
        k = 1 + max([int(re.search(r'_part(\d+)\.log$', f).group(1)) for f in ps] or [0])
        resume = ':'.join(ps)
        cmd = [sys.executable, '-u', os.path.join(HERE, 'comb_search.py')] + a.split() + ['--cache', CACHE] + (['--resume', resume] if resume else [])
        out = open(os.path.join(JOBDIR, '%s_part%d.log' % (name, k)), 'w')
        running[name] = subprocess.Popen(cmd, stdout=out, stderr=subprocess.STDOUT, cwd=HERE, env=env)
        busy.add(name)
    left = [n for n, _ in jobs if n not in busy and not done(n)]
    with open(os.path.join(JOBDIR, 'runner.status'), 'w') as f:
        f.write('%s running: %s (external: %s); waiting: %d %s; done: %s; memory: reserved %.1f of %.1f GB, blocked by memory: %s\n'
                % (time.strftime('%Y-%m-%d %H:%M:%S'), sorted(running), sorted(ext), len(left), left, [n for n, _ in jobs if done(n)],
                   reserved, budget, blocked))
    if not busy and not left:
        break
    time.sleep(30)
