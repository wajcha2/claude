"""prints one line per event worth attention: new max separated rank of some n, worker deaths/failures, stage
changes, finished formats, runner not running.  Polls every 60 s; state in scan/.watch_state.json."""
import json, os, re, time, subprocess
os.chdir(os.path.dirname(os.path.abspath(__file__)))
SF = 'scan/.watch_state.json'
s = json.load(open(SF)) if os.path.exists(SF) else {'pos': 0, 'max': {}}
while True:
    try:
        lines = open('scan/runner.log').read().splitlines()
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
        elif re.search(r'FAILED|exited with|Traceback|finished|: stage', l):
            print(l, flush=True)
    s['pos'] = len(lines)
    json.dump(s, open(SF, 'w'))
    if subprocess.run(['pgrep', '-f', 'scan_runner.py'], capture_output=True).returncode != 0:
        print('RUNNER NOT RUNNING', flush=True)
    time.sleep(60)
