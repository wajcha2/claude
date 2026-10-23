"""kp_jobs.py -- run a list of kp_search.py jobs (copy of combined/comb_jobs.py) on N workers, resumable after container restarts.

usage: python3 comb_jobs.py JOBFILE [NWORKERS]        (detach with nohup; rerun the same command after a restart)
JOBFILE: one job per line, 'name | kp_search arguments' ('#' comments).  Job `name` writes logs/jobs/<name>_partK.log
(K = 1, 2, ... one part per launch); a relaunch passes --resume over all earlier parts.  The job file is re-read
every loop (jobs can be added); a new runner adopts workers an earlier runner left running (same arguments).  A job is done when one of its
parts has the final summary line (' total ').  Status: logs/jobs/runner.status."""
import os, sys, re, time, subprocess, glob
HERE = os.path.dirname(os.path.abspath(__file__))
JOBDIR = os.path.join(HERE, 'logs', 'jobs')
jobfile, nworkers = sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 4
os.makedirs(JOBDIR, exist_ok=True)
def read_jobs():
    """the job file is re-read at every loop, so jobs can be added while the runner runs."""
    out = []
    for l in open(jobfile):
        l = l.split('#')[0].strip()
        if l:
            name, a = [x.strip() for x in l.split('|', 1)]
            out.append((name, a))
    return out
jobs = read_jobs()

def command(a):
    words = a.split()
    script = words.pop(0) if words[0].endswith('.py') else 'kp_search.py'     # 'kp_single.py ...' jobs too
    return script, words

def adopt():
    """workers left running by an earlier runner (same script and arguments, any --resume): {name: pid}."""
    found = {}
    for d in os.listdir('/proc'):
        if not d.isdigit():
            continue
        try:
            argv = open('/proc/%s/cmdline' % d, 'rb').read().decode().split('\0')[:-1]
        except OSError:
            continue
        if len(argv) < 3 or not any(x.endswith(('kp_search.py', 'kp_single.py')) for x in argv):
            continue
        i = next(k for k, x in enumerate(argv) if x.endswith(('kp_search.py', 'kp_single.py')))
        script, words = os.path.basename(argv[i]), argv[i + 1:]
        if '--resume' in words:
            k = words.index('--resume'); words = words[:k] + words[k + 2:]
        for name, a in jobs:
            if command(a) == (script, words):
                found[name] = int(d)
    return found

class Adopted:
    def __init__(self, pid):
        self.pid = pid
    def poll(self):
        try:
            st = open('/proc/%d/stat' % self.pid).read().split(')')[-1].split()[0]
            return None if st != 'Z' else 0
        except OSError:
            return 0

def parts(name):
    return sorted(glob.glob(os.path.join(JOBDIR, '%s_part*.log' % name)), key=lambda f: int(re.search(r'_part(\d+)\.log$', f).group(1)))

def done(name):
    return any(' total ' in l and l.startswith('n=') for f in parts(name) for l in open(f))

running = {name: Adopted(pid) for name, pid in adopt().items()}
if running:
    print('adopted running workers: %s' % sorted(running)); sys.stdout.flush()
env = dict(os.environ, OPENBLAS_NUM_THREADS='1', PYTHONDONTWRITEBYTECODE='1')
while True:
    try:
        jobs = read_jobs()
    except OSError:
        pass
    for name in [n for n, pr in running.items() if pr.poll() is not None]:
        del running[name]
    todo = [(n, a) for n, a in jobs if n not in running and not done(n)]
    for name, a in todo:
        if len(running) >= nworkers:
            break
        ps = parts(name)
        k = 1 + max([int(re.search(r'_part(\d+)\.log$', f).group(1)) for f in ps] or [0])
        resume = ':'.join(ps)
        script, words = command(a)
        cmd = [sys.executable, '-u', os.path.join(HERE, script)] + words + (['--resume', resume] if resume else [])
        out = open(os.path.join(JOBDIR, '%s_part%d.log' % (name, k)), 'w')
        running[name] = subprocess.Popen(cmd, stdout=out, stderr=subprocess.STDOUT, cwd=HERE, env=env)
    with open(os.path.join(JOBDIR, 'runner.status'), 'w') as f:
        f.write('%s running: %s; waiting: %d; done: %s\n' % (time.strftime('%Y-%m-%d %H:%M:%S'), sorted(running),
                len([1 for n, _ in jobs if n not in running and not done(n)]), [n for n, _ in jobs if done(n)]))
    if not running and not [1 for n, _ in jobs if not done(n)]:
        break
    time.sleep(30)
