"""Generate agents/d10.md (status of the d10 agent: C^4 (x) C^5 (x) C^5 sweep, rank 8 vs 9) from hwv455_*.log.
python3 t455_report.py > agents/d10.md"""
import glob, re, os, subprocess, itertools, time, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t455_common import components, dims_of, ns
RANKS = (8, 9)
jobs = []
for line in open('t455_jobs.txt'):
    if line.strip() and not line.startswith('#'):
        d, M = line.split(); jobs.append((int(d), M))
degrees = sorted({d for d, _ in jobs})
done = {}   # (d, lam) -> dict
logs = sorted(glob.glob('hwv455_*.log'))
finished_logs = {lf for lf in logs if os.path.getsize(lf) and open(lf).read().rstrip('\n').split('\n')[-1].startswith('n=4,5,5 d=') and 'FOUND:' in open(lf).read().rstrip('\n').split('\n')[-1]}
for lf in logs:
    d = int(re.search(r'hwv455_d(\d+)', lf).group(1))
    for line in open(lf):
        m = re.match(r'lam=(\(.*?\)\)) g=(\d+) dims=(\(.*?\))\s+(.*?)\s+span=([\d,]+) cost=([\d.e+]+) \(([\d.]+)s\)(.*)$', line.strip())
        if m:
            lam = eval(m.group(1))
            done.setdefault((d, lam), dict(g=int(m.group(2)), dims=m.group(3), ranks=m.group(4), span=m.group(5), secs=float(m.group(7)), sep='SEPARATES' in m.group(8), log=lf))
ps = subprocess.run(['ps', '-eo', 'pid,etime,rss,args'], capture_output=True, text=True).stdout
procs = [l for l in ps.splitlines() if 'sweep_fast.py 4,5,5' in l and 'grep' not in l]
out = []
out.append('# d10 agent status: C^4 (x) C^5 (x) C^5, rank 8 vs rank 9 (isotypic flattenings, all degrees in the job queue)')
out.append('Updated %s. Work is pushed to the shared branch `claude/wonderful-fermat-1v76ux` (mirror `claude/tender-hopper-mcnmta`).' % time.strftime('%Y-%m-%d %H:%M UTC', time.gmtime()))
out.append('Setting: T in C^4 (x) C^5 (x) C^5 (generic rank 9, sigma_8 of codimension 3). "Separates" = smaller flattening rank on a random rank-8')
out.append('tensor than on a random rank-9 tensor. Tool: `sweep_fast.py 4,5,5 d 8,9 5 <k> 3 noV` (d9 agent\'s Cauchy-Binet / float64-BLAS evaluator,')
out.append('generalised to different factor dimensions; exact mod p = 524287; components = (l1; {l2,l3}) unordered in the two C^5 factors, all with')
out.append('Kronecker coefficient g > 0; three flattening directions; gN = generic functional, HN = full multiplicity space stacked). 3 workers, seed 5.')
out.append('')
out.append('## Running now')
out.extend(['    ' + l for l in procs] or ['    (no sweep process running)'])
out.append('')
out.append('## Jobs (t455_jobs.txt) and progress per degree')
out.append('| degree | components (g>0) | checked | hits | sum of times (h) | slowest (s) |')
out.append('|---|---|---|---|---|---|')
tot = 0.0
for d in degrees:
    comps = components(d)
    fin = [lam for lam, g in comps if (d, lam) in done]
    secs = [done[(d, lam)]['secs'] for lam in fin]; tot += sum(secs)
    hits = [lam for lam in fin if done[(d, lam)]['sep']]
    out.append('| %d | %d | %d | %d | %.2f | %.0f |' % (d, len(comps), len(fin), len(hits), sum(secs) / 3600, max(secs) if secs else 0))
out.append('')
out.append('Sum of per-component times so far: %.2f h (3 workers in parallel). Jobs: %s.' % (tot / 3600, ', '.join('d=%d%s' % (d, '' if M == 'inf' else ' MAXDIM=%s' % M) for d, M in jobs)))
try:
    eta = subprocess.run([sys.executable, os.path.join(os.path.dirname(os.path.abspath(__file__)), 't455_eta.py')], capture_output=True, text=True, timeout=600).stdout.strip().splitlines()
    out.append(''); out.append('Predicted remaining wall time (power-law fit of seconds vs the cost proxy g*sum(dim_i+4)^2; rough):'); out.extend('* ' + l for l in eta)
except Exception as e:
    out.append('(ETA unavailable: %s)' % e)
hits = [(k, v) for k, v in done.items() if v['sep']]
out.append('')
out.append('## Hits (`*** SEPARATES`)')
if hits:
    for (d, lam), v in sorted(hits): out.append('* d=%d lam=%s g=%d dims=%s  %s  (log %s)' % (d, lam, v['g'], v['dims'], v['ranks'], v['log']))
else:
    out.append('None so far: every checked flattening has the same rank on the random rank-8 and rank-9 tensors.')
out.append('')
out.append('## Method notes / [method] commits by this agent')
out.append('* 2026-09-24 `[method]` hwv.py: optimal contraction path (opt_einsum DP minimising the largest intermediate) + MEMCAP batch splitting for the')
out.append('  int64 evaluator (adopted by d7d8 as b3feecb). Superseded for sweeps by the d9 agent\'s hwv_fast/sweep_fast (be0ecaf), which this agent adopted.')
out.append('* 2026-09-24 `[method]` mixed factor dimensions: `random_gs` (hwv.py), `prepare` (hwv_fast.py: minors up to each factor\'s own dimension,')
out.append('  only for the column lengths that occur), `sweep_fast.py`/`test_fast.py` take `n1,n2,n3`. Equal-dimension runs are unchanged (d=4 ranks identical')
out.append('  to hwv4_d4.log via both `4` and `4,4,4`; C^3 d=5 control finds exactly the 3 known separators). Mixed-dimension checks: fast == reference')
out.append('  `hwv.flattening_matrix` entrywise on 16 (4,5,5) cases with 5-row partitions and r=9; ranks in (4,5,5) equal the ranks computed in (5,5,5) on the')
out.append('  same tensor embedded with a zero coordinate (test_embed, d=5, r=9). Reference int64 code is 3-45x slower per flattening at r=9 (test_fast).')
out.append('* 2026-09-25 00:45 UTC adopted the d7d8 agent\'s `[method]` ROWCAP (d463955): rows/columns sampled only up to the rank bounds (N1 = min(n1, g*n23)+8,')
out.append('  K = min(n1, n23)+8). Ranks identical to this sweep\'s logs on all 360 components of degrees 4-6 (noV). Degree-8 workers restarted with it (RESUME).')
out.append('* 2026-09-27 12:40 UTC adopted the d13 agent\'s `[method]` 49e2a11 (sweep_fast.py: the ONLY filter is applied before the Kronecker coefficients are')
out.append('  computed; results, indices and claim files unchanged). Not needed by the running pass (no ONLY), taken for future verification runs on single components.')
out.append('* 2026-09-27 18:40 UTC adopted the d13 agent\'s `[method]` 27b3cfe (sweep_fast.py: when a flattening exceeds MEMCAP, block splitting tries both')
out.append('  halving orders and takes the cheaper one; exact block-wise assembly, results unchanged). Running workers keep the old code; restarted ones use it.')
out.append('* 2026-09-27 23:40 UTC adopted `[method]` 0dbe107 (isoflat.py: memoized Murnaghan-Nakayama characters, faster Kronecker enumeration at worker start;')
out.append('  the Kronecker coefficients of all 2467 components of degrees 6-8 agree with the values computed before the change).')
out.append('* 2026-09-28 17:40 UTC adopted `[method]` 760f863 (sweep_fast.py: the DynamicProgramming path fallback is tried only for networks with at most')
out.append('  DPMAX=24 tensors, an out-of-memory guard for d=13/14 networks; degree-9 networks are far below the cap, so this sweep is unaffected).')
out.append('* 2026-10-04 00:25 UTC `[method]` sweep_fast.compute_F: the partial edge blocks of a split flattening (N1 or K not divisible by the block size)')
out.append('  now reuse the full block\'s memory-checked path pb; before, every edge block got a fresh best_path(ops, out, 32) RandomGreedy path that was never')
out.append('  checked against MEMCAP (and networks of more than DPMAX tensors have no DP fallback). On the 8-row edge block of ((5,2,1,1),(6,3),(5,1,1,1,1))')
out.append('  (2408 x 2408 points) such a path carried a word-index-only intermediate (up to 9^9 elements): 13.2 GB anon-rss, cgroup OOM kill of worker 2')
out.append('  (2026-10-04 00:14 UTC; the 6th worker death of this sweep). Exact block-wise assembly, results unchanged: 20 split evaluations with edge blocks')
out.append('  (37 x 37 points, block sizes 1-10, five components of d = 5, 6, 7) equal the unsplit matrices entry by entry, and degrees 4 and 5 rerun with')
out.append('  MEMCAP = 4096 / 32768 (743 + 1816 split evaluations, 270 of them with edge blocks) reproduce every rank and span of hwv455_d4/d5. All workers')
out.append('  restarted on the fixed code at 00:24 UTC.')
out.append('* 2026-10-04 07:40 UTC considered the d9 agent\'s `[method]` 75110fe (flatlib.py, plane_candidates.py, afree_d8.py, plane_d8*.py, section_probe_d8.py,')
out.append('  bilinear_fit_d8.py: canonical 1-dim U = phi_M2 for the C^4 d=8 separator, A-freed reduction, cokernel degree probes): new analysis scripts only,')
out.append('  sweep_fast/hwv_fast/hwv/isoflat unchanged, so nothing to adopt for this sweep; the tools are relevant for analysing a hit, should one occur.')
out.append('  Same for d9\'s `[method]` 852b043 and c6ced66 (08:35 UTC; verify_phiM2.py, m2_symmetry.py, plane_test_d8.py, plane_stack_d8.py, ks_degen_d8.py,')
out.append('  line_point_M2.py: independent checks of K_M2 and of the d=8 separating plane) and bdd4fe3 (11:35 UTC; plane_basis_d8.py: rank profiles of')
out.append('  single fillings and of a basis of the separating plane) and 3b113b3 (13:35 UTC; formal_p0.py: exact formal-variable test of the d=8 P0')
out.append('  flattening): analysis scripts only, sweep code identical.')
out.append('* 2026-10-04 17:45 UTC adopted the d13 agent\'s `[method]` e01ddd5 (sweep_fast.py: MAXFLOPS cap per flattening by the path flop estimate; capped')
out.append('  components are logged as `lam=... NOT CHECKED (MAXFLOPS ...)`; default MAXFLOPS=inf). Builds on this agent\'s edge-block fix; with the default the')
out.append('  behaviour is unchanged (d=4 rerun identical to hwv455_d4 on all 28 components). Not used by the running d=9 pass (workers keep the old code until')
out.append('  a relaunch); a candidate for the expensive tail of d=10, where the report would then have to count NOT CHECKED lines separately.')
out.append('* 2026-10-05 11:50 UTC adopted the d13 agent\'s `[method]` 05630e7 and 1341c0c (isoflat.modrank: row elimination in chunks of <= 2^23 elements and')
out.append('  in-place reduction of the working copy; 3-4x less peak memory on the 9000+ x 9000 H stacks of the C^5 d=14 sweep, which had OOM-killed a worker there).')
out.append('  Same arithmetic: 48 planted-rank test matrices (1 x 1 to 2416 x 2424, wide, tall, zero, unreduced negative entries) give identical ranks with the')
out.append('  input untouched, and the d=4 sweep rerun is identical to hwv455_d4 on all 28 components. The running d=9 workers keep the old code until a relaunch.')
out.append('* 2026-10-05 14:50 UTC adopted the d13 agent\'s `[method]` e80bf0d (sweep_fast.direction: the flattenings are computed and consumed one rank at a time,')
out.append('  the compression H @ R of the g-fold stack is accumulated per filling in float64 with R drawn once; same random stream, exact arithmetic, so the')
out.append('  same ranks; peak memory per worker much lower on the d=14 C^5 stacks). Checked here: d=4 (28) and d=5 (82 components, 4 with g >= 2) reruns identical')
out.append('  to hwv455_d4/d5. The running d=9 workers keep the old code until a relaunch (their memory is far below the limit).')
out.append('* 2026-10-06 01:50 UTC adopted the d13 agent\'s `[method]` b13543e (isoflat.modrank: blocked right-looking Gaussian elimination in exact float64,')
out.append('  panels of 256 columns, BLAS trailing updates; every sum < 2^46, so exact). Independent check: 85 randomized matrices (up to 2633 x 2641, planted')
out.append('  ranks 0 to full, adversarial structure) give the same ranks as the old routine with the input untouched; d=4 and d=5 sweeps identical. 2416 x 2424')
out.append('  full rank 164 s -> 12 s, 2633 x 2641 full rank 226 s -> 14 s. Runner and d=9 workers relaunched on it at 01:55 UTC (all adopted methods now live).')
out.append('')
out.append('## Restart (fresh container, from the pushed logs alone)')
out.append('```')
out.append('git clone -b claude/tender-hopper-mcnmta https://github.com/wajcha2/claude && cd claude      # sweep dir (own branch; any branch with the code works)')
out.append('git worktree add /home/user/claude-shared claude/wonderful-fermat-1v76ux                   # used only to pull --rebase / push the shared branch')
out.append('cd isotypic_flattenings && cp /home/user/claude-shared/isotypic_flattenings/hwv455_*.log . 2>/dev/null   # authoritative logs = shared branch')
out.append('pip install numpy sympy opt_einsum')
out.append('bash t455_checkin.sh      # restarts the workers of the first unfinished job in t455_jobs.txt with RESUME=<all hwv455_d<d> logs>, or starts the next job')
out.append('# by hand: RESUME=$(ls hwv455_d<d>*.log | tr "\\n" ":") MAXDIM=<inf|N> CLAIMDIR=claims455_d<d>[_max<N>] OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \\')
out.append('#   setsid nohup python3 sweep_fast.py 4,5,5 <d> 8,9 5 <k> 3 noV >> hwv455_d<d>[_max<N>]_w<k>.log 2>&1 < /dev/null &     (k = 0,1,2; remove the dead worker\'s claim files first)')
out.append('```')
out.append('A worker is finished when the last line of its log is `n=4,5,5 d=... FOUND: [...]`. Hourly check-in routine trig_01Kq52M65tDvcZNxEXAWNoxm (this session).')
out.append('Container behaviour (observed 2026-09-24 20:34 UTC): the session container is stopped when the session is idle between turns and re-provisioned')
out.append('when the routine fires (disk restored, all processes gone). Detached processes therefore only run while the session is busy; the agent keeps a')
out.append('harness-tracked Monitor task armed (30 min windows, re-armed at each expiry) and the check-in restarts the runner after any restore.')
out.append('')
for d in degrees:
    comps = components(d)
    fin = [(lam, done[(d, lam)]) for lam, g in comps if (d, lam) in done]
    if not fin: continue
    out.append('## Degree %d: components checked (%d of %d)' % (d, len(fin), len(comps)))
    out.append('gN/HN = generic functional / full-multiplicity-space stack in direction N (1 = source S^{l1}(C^4)^*, 2 = S^{l2}(C^5)^*, 3 = S^{l3}(C^5)^*); ranks rank-8/rank-9.')
    out.append('')
    out.append('| lam | g | dims | ranks | span | s |')
    out.append('|---|---|---|---|---|---|')
    for lam, v in fin:
        out.append('| %s | %d | %s | %s | %s | %.0f |%s' % (lam, v['g'], v['dims'], v['ranks'], v['span'], v['secs'], ' **SEPARATES**' if v['sep'] else ''))
    out.append('')
    nc = [(lam, g) for lam, g in comps if (d, lam) not in done]
    if nc:
        out.append('Not checked yet at degree %d: %d components%s' % (d, len(nc), (': ' + ', '.join('%s (g=%d, dims %s)' % (lam, g, dims_of(lam)) for lam, g in nc)) if len(nc) <= 60 else ' (largest Weyl dimension %d..%d)' % (min(max(dims_of(l)) for l, _ in nc), max(max(dims_of(l)) for l, _ in nc))))
        out.append('')
out.append('## Previous task of this agent: C^4 (x) C^4 (x) C^4, d = 10, rank 6 vs 7 (stopped 2026-09-24 19:42 UTC)')
n10 = len({l.split(' g=')[0] for lf in glob.glob('hwv4_d10_*.log') for l in open(lf) if l.startswith('lam=')})
out.append('Stopped by the user after the d9 agent found two degree-9 separators. %d of the 279 pass-1 components (largest Weyl dimension <= 150) were' % n10)
out.append('checked with no separator (logs `hwv4_d10_*.log`, per-component ranks in the git history of agents/d10.md before this task). Restart: `D10_RESUME=1 bash d10_checkin.sh`.')
print('\n'.join(out))
