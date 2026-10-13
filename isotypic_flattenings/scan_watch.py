"""prints one line per event worth attention: new max separated rank of some n, a component separating a rank
(n, r) not separated before or at a lower degree than known (as soon as its record is written, not only when the job
is done -- since 2026-10-13: the 6x6x6 r = 10 separation of 2026-10-12 14:53 sat in a running job unreported),
worker deaths/failures, stage changes, finished formats, runner not running.  Polls every 60 s; state in
scan/live/.watch_state.json."""
import json, os, re, time, subprocess, glob
os.chdir(os.path.dirname(os.path.abspath(__file__)))
SF = 'scan/live/.watch_state.json'
s = json.load(open(SF)) if os.path.exists(SF) else {'pos': 0, 'max': {}}


def fmt(lam):
    return '(' + ','.join(''.join(map(str, p)) for p in lam) + ')'


def new_seps(first):
    """separating records appended since the last poll; on the first run only the lowest known degrees are seeded."""
    offs, low = s.setdefault('offs', {}), s.setdefault('low', {})
    for fn in sorted(glob.glob('scan/live/res/*.jsonl')):
        try:
            with open(fn) as f:
                f.seek(offs.get(fn, 0))
                data = f.read()
        except OSError:
            continue
        done = data.rfind('\n') + 1                     # a half-written last line is read next time
        offs[fn] = offs.get(fn, 0) + len(data[:done].encode())
        for l in data[:done].splitlines():
            try:
                d = json.loads(l)
            except ValueError:
                continue
            for r in (d.get('sep') or {}):
                key = '%d:%s' % (d['n'], r)
                if key not in low or d['d'] < low[key]:
                    low[key] = d['d']
                    if not first:
                        print('n=%d: r=%s vs %d separated at d=%d by %s g=%s %s (%s)'
                              % (d['n'], r, int(r) + 1, d['d'], fmt(d['lam']), d.get('g'), d['sep'][r],
                                 os.path.basename(fn)[:-6]), flush=True)


new_seps('offs' not in s)
while True:
    try:
        lines = open('scan/live/runner.log').read().splitlines()
    except OSError:
        lines = []
    for l in lines[s['pos']:]:
        m = re.search(r'job n(\d+)_d(\d+)_s(\d+) done: .*d_min now (\{.*\})', l)
        if m:
            n, d = m.group(1), int(m.group(2))
            dm = {int(k): v for k, v in eval(m.group(4)).items()}
            mx = max(dm) if dm else 0
            if mx > s['max'].get(n, 0):
                s['max'][n] = mx
                print('n=%s: max separated rank now %d (vs %d) at d=%d (job %s)' % (n, mx, mx + 1, dm[mx], l.split()[3]), flush=True)
        elif re.search(r'FAILED|TIMEOUT|Traceback|finished|deferred|resumed', l):
            print(l, flush=True)
    s['pos'] = len(lines)
    new_seps(False)
    json.dump(s, open(SF, 'w'))
    if subprocess.run(['pgrep', '-f', 'scan_runner.py'], capture_output=True).returncode != 0:
        print('RUNNER NOT RUNNING', flush=True)
    time.sleep(60)
