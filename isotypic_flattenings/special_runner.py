"""python3 special_runner.py JOBFILE       (background: setsid nohup python3 -u special_runner.py special/jobs.txt >> special/runner.log 2>&1 &)

Runs specialscan.py jobs, one process per component, at most NCORES at a time (read every 10 s from
special/live/ncores, default 4), in the order of JOBFILE.  JOBFILE lines: `n d R methods...` (all components with
g >= 2 of degree d, cheapest first by rankscan.cost_proxy) or `n d R methods... :: lam` (one component).
Output of a job: special/live/res/n<n>_d<d>_s<slot>.jsonl and special/live/logs/n<n>_d<d>_s<slot>.log (slot = pool
slot, so that no two running processes append to one file; special/live is not tracked: special/sync.sh copies it
to special/res, special/logs and commits).  Resume: a component is skipped when every distinct direction has a
record with the same ranks and methods in some special/live/res/n<n>_d<d>*.jsonl.  A job running longer than
TLIMIT seconds (special/live/tlimit, default 10800) is killed and listed in special/runner.log as 'timeout'."""
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


def expand(jobfile):
    jobs = []
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
        n, d, Rs, methods = int(f[0]), int(f[1]), f[2], f[3:]
        if lams is None:
            comps = [(lam, g) for _, lam, g in rankscan.components(n, d) if g >= 2]
            comps.sort(key=lambda c: cost_proxy(n, c[0], c[1]))
            lams = [lam for lam, _ in comps]
        for lam in lams:
            jobs.append((n, d, Rs, tuple(methods), lam))
    return jobs


def main():
    jobfile = sys.argv[1]
    os.makedirs(LIVE, exist_ok=True)
    os.makedirs('special/live/res', exist_ok=True)
    os.makedirs('special/live/logs', exist_ok=True)
    running = {}            # slot -> (proc, job, t0)
    pending = None
    print('# runner start %s' % time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), flush=True)
    while True:
        # re-read the job file every round (jobs can be appended while running)
        jobs = expand(jobfile)
        cache = {}
        todo = []
        active = set(j for _, j, _ in running.values())
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
        while todo and len(running) < ncores:
            job = todo.pop(0)
            slot = min(set(range(16)) - set(running))
            n, d, Rs, methods, lam = job
            env = dict(os.environ, OPENBLAS_NUM_THREADS='1', OMP_NUM_THREADS='1',
                       OUT='special/live/res/n%d_d%d_s%d.jsonl' % (n, d, slot), DONEGLOB='special/live/res')
            logf = open('special/live/logs/n%d_d%d_s%d.log' % (n, d, slot), 'a')
            proc = subprocess.Popen(['python3', '-u', 'specialscan.py', str(n), str(d), repr(lam), Rs] + list(methods),
                                    stdout=logf, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL, env=env,
                                    start_new_session=True)
            running[slot] = (proc, job, time.time())
            print('%s start slot %d  %s' % (time.strftime('%H:%M:%S'), slot, job), flush=True)
        if not running and not todo:
            print('# runner: nothing left %s' % time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), flush=True)
            break
        time.sleep(10)


if __name__ == '__main__':
    main()
