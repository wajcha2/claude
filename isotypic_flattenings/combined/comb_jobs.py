"""comb_jobs.py -- run a list of comb_search.py jobs on N workers, resumable after container restarts.

usage: python3 comb_jobs.py JOBFILE [NWORKERS]        (detach with setsid nohup; rerun the same command after a restart)
JOBFILE: one job per line, 'name | comb_search arguments' ('#' comments), in priority order; it is re-read every
cycle, so jobs can be added or reordered while the runner works.  Job `name` writes logs/jobs/<name>_partK.log
(K = 1, 2, ... one part per launch); a relaunch passes --resume over all earlier parts.  A job is done when one of its
parts has the final summary line (' total ').  A job whose comb_search process is already running (started by an
earlier runner: found in /proc by its command line) counts as running and takes a slot, so restarting the runner never
duplicates work.  Status: logs/jobs/runner.status.  Every 10 minutes prune_cache.py JOBFILE --do frees the disk
cache of finished targets (log: logs/jobs/prune.log)."""
import os, sys, re, time, subprocess, glob
HERE = os.path.dirname(os.path.abspath(__file__))
JOBDIR = os.path.join(HERE, 'logs', 'jobs')
jobfile, nworkers = sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 4
os.makedirs(JOBDIR, exist_ok=True)

def read_jobs():
    jobs = []
    for l in open(jobfile):
        l = l.split('#')[0].strip()
        if l:
            name, a = [x.strip() for x in l.split('|', 1)]
            jobs.append((name, ' '.join(a.split())))
    return jobs

def parts(name):
    return sorted(glob.glob(os.path.join(JOBDIR, '%s_part*.log' % name)), key=lambda f: int(re.search(r'_part(\d+)\.log$', f).group(1)))

def done(name):
    return any(' total ' in l and l.startswith('n=') for f in parts(name) for l in open(f))

def external(jobs, own_pids):
    """jobs whose comb_search process runs outside this runner (matched by 'comb_search.py <args>' in /proc)."""
    out = set()
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
                out.add(name)
    return out

running = {}
env = dict(os.environ, OPENBLAS_NUM_THREADS='1', PYTHONDONTWRITEBYTECODE='1')
cycle = 0
while True:
    if cycle % 20 == 0:
        # every 10 minutes: delete cached flattenings that no job will read again (prune_cache.py; the cache of the
        # d = 7, 8 pattern jobs reached 30 GB and filled the disk on 2026-10-23)
        with open(os.path.join(JOBDIR, 'prune.log'), 'a') as pl:
            pl.write(time.strftime('%Y-%m-%d %H:%M:%S\n')); pl.flush()
            subprocess.call([sys.executable, os.path.join(HERE, 'prune_cache.py'), jobfile, '--do'], stdout=pl, stderr=subprocess.STDOUT, cwd=HERE)
    cycle += 1
    jobs = read_jobs()
    for name in [n for n, pr in running.items() if pr.poll() is not None]:
        del running[name]
    ext = external(jobs, {pr.pid for pr in running.values()})
    busy = set(running) | ext
    for name, a in jobs:
        if len(busy) >= nworkers:
            break
        if name in busy or done(name):
            continue
        ps = parts(name)
        k = 1 + max([int(re.search(r'_part(\d+)\.log$', f).group(1)) for f in ps] or [0])
        resume = ':'.join(ps)
        cmd = [sys.executable, '-u', os.path.join(HERE, 'comb_search.py')] + a.split() + (['--resume', resume] if resume else [])
        out = open(os.path.join(JOBDIR, '%s_part%d.log' % (name, k)), 'w')
        running[name] = subprocess.Popen(cmd, stdout=out, stderr=subprocess.STDOUT, cwd=HERE, env=env)
        busy.add(name)
    left = [n for n, _ in jobs if n not in busy and not done(n)]
    with open(os.path.join(JOBDIR, 'runner.status'), 'w') as f:
        f.write('%s running: %s (external: %s); waiting: %d %s; done: %s\n' % (time.strftime('%Y-%m-%d %H:%M:%S'), sorted(running),
                sorted(ext), len(left), left, [n for n, _ in jobs if done(n)]))
    if not busy and not left:
        break
    time.sleep(30)
