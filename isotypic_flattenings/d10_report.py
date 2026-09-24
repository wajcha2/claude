"""Generate agents/d10.md (status of the d=10 sweep) from the hwv4_d10_*.log files.  python3 d10_report.py > agents/d10.md"""
import glob, re, os, subprocess, itertools, time, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hwv import dim_schur
from isoflat import partitions, kronecker
n, d = 4, 10
PASSES = [(1, 'max150', 0, 150), (2, 'max300', 150, 300), (3, 'max0', 300, 0)]
comps = [(lam, kronecker(*lam)) for lam in itertools.combinations_with_replacement(partitions(d, n), 3)]
comps = [(lam, g) for lam, g in comps if g > 0]
comps.sort(key=lambda x: (max(dim_schur(l, n) for l in x[0]), x[1]))
def pass_of(lam):
    md = max(dim_schur(l, n) for l in lam)
    return 1 if md <= 150 else (2 if md <= 300 else 3)
done = {}   # lam -> (pass, g, dims, summary, secs, sep, logfile)
finished_logs, all_logs = set(), sorted(glob.glob('hwv4_d10_*.log'))
for lf in all_logs:
    for line in open(lf):
        m = re.match(r'lam=(\(.*?\)\)) g=(\d+) dims=(\(.*?\))\s+(.*?)\s+\(([\d.]+)s\)(.*)$', line.strip())
        if m:
            lam = eval(m.group(1)); sep = 'SEPARATES' in m.group(6)
            done.setdefault(lam, (pass_of(lam), int(m.group(2)), m.group(3), m.group(4), float(m.group(5)), sep, lf))
        if line.startswith('n=4 d=10'): finished_logs.add(lf)
ps = subprocess.run(['ps', '-eo', 'pid,etime,rss,args'], capture_output=True, text=True).stdout
procs = [l for l in ps.splitlines() if 'sweep_hwv.py 4 10' in l and 'grep' not in l]
out = []
out.append('# d10 agent status (C^4 (x) C^4 (x) C^4, rank 6 vs 7, degree d = 10)')
out.append('Updated %s. Branch for this agent\'s work: shared `claude/wonderful-fermat-1v76ux` (also mirrored on `claude/tender-hopper-mcnmta`).' % time.strftime('%Y-%m-%d %H:%M UTC', time.gmtime()))
out.append('Sweep started 2026-09-24 19:09 UTC on 4 cores (memory cgroup 13.4 GiB), 3 processes, `noV`, `CHUNK=32`, seed 5, p = 524287.')
out.append('**STOPPED 2026-09-24 19:42 UTC at the user\'s request** (a d=9 separator was reported; the d10 agent moved to C^4 (x) C^5 (x) C^5, rank 8 vs 9,')
out.append('see `agents/d10_455.md`). Restart: `D10_RESUME=1 bash d10_checkin.sh` (RESUME over all hwv4_d10 logs).')
out.append('')
out.append('## Running now')
out.extend(['    ' + l for l in procs] or ['    (no sweep process running)'])
out.append('')
out.append('## Passes')
out.append('| pass | filter | components | finished | slices finished | hits |')
out.append('|---|---|---|---|---|---|')
for pno, pfx, lo, hi in PASSES:
    members = [lam for lam, g in comps if pass_of(lam) == pno]
    fin = [lam for lam in members if lam in done]
    sl = [k for k in range(3) if any(lf in finished_logs for lf in all_logs if re.match(r'hwv4_d10_%s_s%d(_r\d+)?\.log' % (pfx, k), lf))]
    hits = [lam for lam in fin if done[lam][5]]
    out.append('| %d | %s | %d | %d | %s | %d |' % (pno, 'MAXDIM=150' if pno == 1 else ('MINDIM=150 MAXDIM=300' if pno == 2 else 'MINDIM=300 (unbounded)'), len(members), len(fin), ','.join(map(str, sl)) or '-', len(hits)))
tot = sum(v[4] for v in done.values())
out.append('')
out.append('Components finished: %d / %d.  Sum of per-component times: %.1f h (3 processes in parallel).' % (len(done), len(comps), tot / 3600))
hits = [(lam, v) for lam, v in done.items() if v[5]]
out.append('')
out.append('## Hits (`*** SEPARATES`)')
if hits:
    for lam, v in hits: out.append('* lam=%s g=%d dims=%s  %s  (log %s)' % (lam, v[1], v[2], v[3], v[6]))
else:
    out.append('None so far: every checked flattening has the same rank on the random rank-6 and rank-7 tensors.')
out.append('')
out.append('## Method notes')
out.append('* `[method]` commit (2026-09-24): `hwv.py` chooses the pairwise contraction order with opt_einsum\'s dynamic programming, minimising the largest')
out.append('  intermediate (`pip install opt_einsum`; `PATHOPT=greedy` restores the old order), and halves the row (Y) or column (Z) batch recursively when the')
out.append('  predicted largest intermediate exceeds `MEMCAP` int64 elements (default 4e7 = 0.32 GB). Motivation: a shape-only simulation of the old greedy order')
out.append('  at d = 10 predicted intermediates of 10-60 GB on many random fillings (batch of HWVs x up to 7^7 word indices); a dims-6 component already reached')
out.append('  2.7 GB RSS. Results are bit-identical (18 random cases incl. forced splits, d=4 sweep, C^3 d=5 test). Measured per-filling times, same inputs,')
out.append('  old -> new: 21.7s -> 1.8s, 16.4s -> 2.1s, 10.8s -> 0.13s, 8.3s -> 5.2s, 3.4s -> 2.1s, 0.2s -> 0.2s (never slower by more than ~0.3 s).')
out.append('  RSS of the sweep processes now stays in the 0.1-0.7 GB range. Applies to every degree; for d <= 8 the gain is smaller (fewer boxes).')
out.append('')
out.append('## Restart (fresh container, from the pushed logs alone)')
out.append('```')
out.append('git clone -b claude/tender-hopper-mcnmta https://github.com/wajcha2/claude && cd claude   # sweep dir = own branch (any branch with the code works)')
out.append('git worktree add /home/user/claude-shared claude/wonderful-fermat-1v76ux            # worktree used only for pull --rebase / push to the shared branch')
out.append('cd isotypic_flattenings && cp /home/user/claude-shared/isotypic_flattenings/hwv4_d10_*.log .   # authoritative logs = shared branch')
out.append('pip install numpy sympy opt_einsum')
out.append('bash d10_checkin.sh          # restarts every unfinished slice of the current pass with RESUME=<all hwv4_d10 logs>, or starts the next pass')
out.append('# manually, for pass P in 1,2,3 = (MINDIM,MAXDIM) in (0,150),(150,300),(300,0), log prefix max150/max300/max0, slice k in 0,1,2, fresh suffix _r<N>:')
out.append('ALL=$(ls hwv4_d10_*.log | tr "\\n" ":"); RESUME=$ALL MINDIM=<lo> MAXDIM=<hi> CHUNK=32 OMP_NUM_THREADS=1 setsid nohup \\')
out.append('  python3 sweep_hwv.py 4 10 6,7 5 <k> 3 noV > hwv4_d10_<prefix>_s<k>_r<N>.log 2>&1 < /dev/null &')
out.append('```')
out.append('A slice is finished when its log ends with `n=4 d=10 ... FOUND: [...]`. Hourly check-in routine trig_01Kq52M65tDvcZNxEXAWNoxm (session d10).')
out.append('')
for pno, pfx, lo, hi in PASSES:
    fin = [(lam, done[lam]) for lam, g in comps if pass_of(lam) == pno and lam in done]
    if not fin: continue
    out.append('## Pass %d: components checked (%d)' % (pno, len(fin)))
    out.append('Columns: gK = generic functional, direction K; HK = stacked flattening (U = whole multiplicity space), direction K. Ranks are rank-6/rank-7.')
    out.append('')
    out.append('| lam | g | dims | ranks | s |')
    out.append('|---|---|---|---|---|')
    for lam, v in fin:
        out.append('| %s | %d | %s | %s | %.0f |%s' % (lam, v[1], v[2], v[3], v[4], ' **SEPARATES**' if v[5] else ''))
    out.append('')
nc = [(lam, g) for lam, g in comps if lam not in done]
out.append('## Not checked yet (%d), by pass' % len(nc))
for pno, pfx, lo, hi in PASSES:
    rest = [(lam, g) for lam, g in nc if pass_of(lam) == pno]
    out.append('* pass %d (%s): %d components%s' % (pno, 'max dim <= 150' if pno == 1 else ('150 < max dim <= 300' if pno == 2 else 'max dim > 300'), len(rest), '' if pno < 3 and len(rest) > 40 else ''))
print('\n'.join(out))
