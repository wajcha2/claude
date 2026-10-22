"""comb_jobs.py -- run a list of comb_search.py jobs on N workers, resumable after container restarts.

usage: python3 comb_jobs.py JOBFILE [NWORKERS]        (detach with nohup; rerun the same command after a restart)
JOBFILE: one job per line, 'name | comb_search arguments' ('#' comments).  Job `name` writes logs/jobs/<name>_partK.log
(K = 1, 2, ... one part per launch); a relaunch passes --resume over all earlier parts.  A job is done when one of its
parts has the final summary line (' total ').  Status: logs/jobs/runner.status."""
import os, sys, re, time, subprocess, glob
HERE = os.path.dirname(os.path.abspath(__file__))
JOBDIR = os.path.join(HERE, 'logs', 'jobs')
jobfile, nworkers = sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 4
os.makedirs(JOBDIR, exist_ok=True)
jobs = []
for l in open(jobfile):
    l = l.split('#')[0].strip()
    if l:
        name, a = [x.strip() for x in l.split('|', 1)]
        jobs.append((name, a))

def parts(name):
    return sorted(glob.glob(os.path.join(JOBDIR, '%s_part*.log' % name)), key=lambda f: int(re.search(r'_part(\d+)\.log$', f).group(1)))

def done(name):
    return any(' total ' in l and l.startswith('n=') for f in parts(name) for l in open(f))

running = {}
env = dict(os.environ, OPENBLAS_NUM_THREADS='1', PYTHONDONTWRITEBYTECODE='1')
while True:
    for name in [n for n, pr in running.items() if pr.poll() is not None]:
        del running[name]
    todo = [(n, a) for n, a in jobs if n not in running and not done(n)]
    for name, a in todo:
        if len(running) >= nworkers:
            break
        ps = parts(name)
        k = 1 + max([int(re.search(r'_part(\d+)\.log$', f).group(1)) for f in ps] or [0])
        resume = ':'.join(ps)
        cmd = [sys.executable, '-u', os.path.join(HERE, 'comb_search.py')] + a.split() + (['--resume', resume] if resume else [])
        out = open(os.path.join(JOBDIR, '%s_part%d.log' % (name, k)), 'w')
        running[name] = subprocess.Popen(cmd, stdout=out, stderr=subprocess.STDOUT, cwd=HERE, env=env)
    with open(os.path.join(JOBDIR, 'runner.status'), 'w') as f:
        f.write('%s running: %s; waiting: %d; done: %s\n' % (time.strftime('%Y-%m-%d %H:%M:%S'), sorted(running),
                len([1 for n, _ in jobs if n not in running and not done(n)]), [n for n, _ in jobs if done(n)]))
    if not running and not [1 for n, _ in jobs if not done(n)]:
        break
    time.sleep(30)
