"""python3 d13_report.py > agents/d13.md : status file of the d13 agent (C^5 rank 9 vs 10, degrees 13 and 14)."""
import os, re, subprocess, time, glob
SESSION = "https://claude.ai/code/session_01Xqa6zjM98kkSHbEmfYGvTt"
now = time.strftime('%Y-%m-%d %H:%M UTC', time.gmtime())
out = []
P = out.append
P("# d13 agent status: C^5 (x) C^5 (x) C^5, rank 9 vs rank 10, isotypic flattenings in degrees 13 and 14")
P("Updated %s. Session %s. Pushes to the shared branch `claude/wonderful-fermat-1v76ux`." % (now, SESSION))
P("Task: PROMPT_C5_d13.md. Components = the 'promising' lists prom5_d13.txt / prom5_d14.txt (made by make_prom5.py: g > 0,")
P("l1 with <= 2 rows, l2, l3 with >= 4 rows, dim S^{l1} >= dim S^{l2} dim S^{l3} / 2; make_prom5.py reproduces prom5_d11/d12.txt exactly).")
P("Tool: `MEMCAP=67108864 ONLY=prom5_d<d>.txt CLAIMDIR=claims5_p<d> sweep_fast.py 5 <d> 9,10 5 <k> 4 noV` (ROWCAP on, seed 5, p = 524287),")
P("one worker per core (since 2026-09-28 04:13 UTC: 3 on d=13, 1 on d=14, interleaved because the remaining d=13 components take > 6 h each), cheapest components first, logs untracked in live/ and snapshotted into hwv5_d<d>_prom_done.log at every check-in.")
P("Sanity checks passed before the start: `sweep_fast.py 4 4 6,7` full ranks / FOUND: [], and the d=8 C^4 hit reproduces H1:304/309.")
P("")
P("## Running now")
ps = subprocess.run("ps -eo pid,etime,rss,pcpu,args | awk '$5==\"python3\" && $7==\"sweep_fast.py\"'", shell=True, capture_output=True, text=True).stdout.strip()
P("```\n%s\n```" % (ps or "(no worker running)"))
P("")
P("## Progress")
P("| degree | components in list | checked | hits | sum of times (h) | slowest (s) |")
P("|---|---|---|---|---|---|")
tables = {}
for d in (13, 14):
    lst = 'prom5_d%d.txt' % d; log = 'hwv5_d%d_prom_done.log' % d
    tot = sum(1 for l in open(lst) if l.strip()) if os.path.exists(lst) else 0
    lines = [l.rstrip('\n') for l in open(log) if l.startswith('lam=')] if os.path.exists(log) else []
    times = [float(m.group(1)) for l in lines for m in [re.search(r'\(([\d.]+)s\)', l)] if m]
    hits = [l for l in lines if 'SEPARATES' in l]
    P("| %d | %d | %d | %d | %.2f | %.0f |" % (d, tot, len(lines), len(hits), sum(times) / 3600, max(times) if times else 0))
    tables[d] = (lines, hits, tot)
P("")
P("## Hits (`*** SEPARATES`)")
allhits = [h for d in tables for h in tables[d][1]]
if allhits:
    for h in allhits: P("* " + h)
else:
    P("None so far: every checked flattening has the same rank on the random rank-9 and the random rank-10 tensor.")
P("")
P("## Method notes / [method] commits by this agent")
P("* 2026-09-27 `[method]` sweep_fast.py: with ONLY set, the Kronecker coefficient is skipped for unlisted components (the full")
P("  enumeration of 32509 triples at n=5, d=13 took 2 h per worker start; now 1 min).  Indices, random streams, results unchanged.")
P("* 2026-09-27 `[method]` sweep_fast.py compute_F: when the path exceeds MEMCAP, both halving orders (target pairs first / source")
P("  points first) are tried and the one with fewer total flops is used.  The old Z-first order cut ((9,4),(3,3,3,3,1),(3,3,3,3,1))")
P("  (683 x 233 points) into 26562 blocks of 6 x 1 at 4.2e13 flops per flattening (> 4 h for one of six flattenings, i.e. days per")
P("  component); Y-first gives 1 x 233 blocks at 5.7e12 flops.  Results identical (C^4 d=4 with forced splitting, C^4 d=8 hit).")
P("  Workers restarted 18:27 UTC with MEMCAP=2^26 (so that 1 x K blocks fit); the 4 components in progress were recomputed.")
P("")
P("## Restart (fresh container, from the pushed files alone)")
P("```")
P("pip install numpy sympy opt_einsum; cd isotypic_flattenings; bash d13_checkin.sh      # restarts dead workers with RESUME=hwv5_d<d>_prom_done.log, snapshots, commits, pushes")
P("# by hand (d=13: k = 0,1,2; d=14: k = 3, with 14 in place of 13 below): MEMCAP=67108864 ONLY=prom5_d13.txt CLAIMDIR=claims5_p13 RESUME=hwv5_d13_prom_done.log OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \\")
P("#   setsid nohup python3 -u sweep_fast.py 5 13 9,10 5 $k 4 noV >> live/d13_w$k.log 2>&1 < /dev/null &      (remove the dead worker's claim files first)")
P("```")
P("Check-in routine every 2 h in this session (create_trigger); a harness Monitor task (30 min, re-armed) keeps the container alive between check-ins.")
P("")
for d in (13, 14):
    lines, hits, tot = tables[d]
    P("## Degree %d: components checked (%d of %d), format of sweep_fast.py (gN generic functional, HN full-M stack; a/b = rank on rank 9 / rank 10)" % (d, len(lines), tot))
    P("```")
    for l in sorted(lines, key=lambda l: float(re.search(r'\(([\d.]+)s\)', l).group(1)) if re.search(r'\(([\d.]+)s\)', l) else 0):
        P(l)
    P("```")
    # components not yet checked
    if os.path.exists('prom5_d%d.txt' % d):
        done = {l.split(' g=')[0][4:].strip() for l in lines}
        left = [l.strip() for l in open('prom5_d%d.txt' % d) if l.strip() and l.strip() not in done]
        P("Not yet checked (%d): %s" % (len(left), '; '.join(left) if len(left) <= 60 else '; '.join(left[:60]) + '; ...'))
    P("")
print('\n'.join(out))
