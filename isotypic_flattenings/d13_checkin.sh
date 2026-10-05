#!/bin/bash
# One check-in of the C^5 rank 9 vs 10 sweep at d = 13 / 14 (d13 agent): process status, OOM check, snapshot of the
# untracked live/ logs into the tracked hwv5_d<d>_prom_done.log, restart of dead workers (RESUME), agents/d13.md,
# commit + push (git pull --rebase --autostash first).  Usage: bash d13_checkin.sh [nworkers]   (default 4)
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1
NW=${1:-4}
mkdir -p live; touch hwv5_d13_prom_done.log hwv5_d14_prom_done.log
cnt() { local c; c=$(grep '^lam=' "$1" 2>/dev/null | grep -vc 'NOT CHECKED'); echo ${c:-0}; }   # checked components (MAXFLOPS skips excluded)
skp() { local c; c=$(grep -c 'NOT CHECKED (MAXFLOPS' "$1" 2>/dev/null); echo ${c:-0}; }
echo "== $(date -u +'%Y-%m-%d %H:%M:%S UTC') =="
echo "-- processes --"; ps -eo pid,etime,rss,pcpu,args | awk '$5=="python3" && $7=="sweep_fast.py"' || echo "(none)"
echo "-- oom --"; (dmesg 2>/dev/null | grep -i oom | tail -2) || true
grep -h "oom_kill" /sys/fs/cgroup/memory.events 2>/dev/null || true
# MAXFLOPS stages (file maxflops_stage, tracked): a component one of whose flattenings needs more flops than the stage's cap
# (path estimate, printed as '# blocks: ... flops') is left as 'lam=... NOT CHECKED (MAXFLOPS <cap>)' in the logs/done-log
# and the worker moves on.  Measured 1.1e9 flop/s for the 1 x K block loops, so 1e13 ~ 2.5 h per flattening.  Stage 1e13
# since 2026-10-04 17:30 UTC (all four workers had sat in flattenings of 4e13 .. 3e14 flops, 10 .. 75 h each).  When both
# lists are exhausted under MC and the current cap, the stage advances to the next value of STAGES (3e13 asked for on
# 2026-10-05): the skip lines of the lower caps are dropped from the snapshot (so RESUME recomputes those components,
# cheapest first by the cost proxy), all claims are released and the workers are relaunched with the new cap.
STAGES="1e13 3e13"
MAXFLOPS=${MAXFLOPS:-$(cat maxflops_stage 2>/dev/null || echo 1e13)}
next_stage() { local prev=""; for s in $STAGES; do [ -n "$prev" ] && [ "$prev" = "$1" ] && { echo $s; return; }; prev=$s; done; }
stage_filter() {  # stdin -> stdout without the 'NOT CHECKED (MAXFLOPS <cap>)' lines whose cap is below the current stage
  python3 -c '
import sys, re
cap = float(sys.argv[1])
for l in sys.stdin:
    m = re.search(r"NOT CHECKED \(MAXFLOPS ([0-9.e+-]+)\)", l)
    if m and float(m.group(1)) < cap: continue
    sys.stdout.write(l)' "$MAXFLOPS"
}
# snapshot: every finished component line of the live logs goes into the tracked done-log (union, sorted, unique; skip lines
# of lower MAXFLOPS stages dropped)
snapshot() {
  for d in 13 14; do
    cat hwv5_d${d}_prom_done.log live/d${d}_w*.log 2>/dev/null | grep '^lam=' | stage_filter | sort -u > hwv5_d${d}_prom_done.tmp
    mv hwv5_d${d}_prom_done.tmp hwv5_d${d}_prom_done.log
  done
}
snapshot
echo "-- hits / problems --"; grep -H "SEPARATES" hwv5_d13_prom_done.log hwv5_d14_prom_done.log live/d1[34]_w*.log 2>/dev/null || echo "no SEPARATES"
grep -H -i "error\|Traceback\|Killed\|MemoryError" live/d1[34]_w*.log 2>/dev/null | head -5 || true
# Cost policy (since 2026-09-28 08:45 UTC): components of both degrees are processed cheapest first by the sweep's cost proxy
# g * sum_t N1_t K_t (rows x columns of the sampled flattening matrices), in stages MC = 1e7, 3e7, 1e8 (env MC13 / MC14, passed
# to sweep_fast as MAXCOST).  Measured: about 6e-3 s per cost unit for the big components, so 1e7 ~ 17 h, 3e7 ~ 50 h per
# component.  prom5_d<d>_cost.txt caches "repr(lam) g cost dims" for every listed component.
# Worker slots: W13 / W14 list the slots (0..NW-1) for d=13 / d=14; a degree with nothing left under its MC hands its
# slots to the other degree.
MC13=${MC13:-1e8}; MC14=${MC14:-1e8}     # stage 3 since 2026-09-28 23:20 UTC (3e7 stage: the 2.3e7 d=13 component took 2 h, not 60 h, once the DP path fallback was capped)
W13=${W13:-"0 1"}; W14=${W14:-"2 3"}
left() {  # degree maxcost -> number of listed components with cost <= maxcost not yet in the done-log
  python3 - <<PY
import os, re
mc = float("$2"); n = 0
done = {l.split(' g=')[0][4:].strip() for l in open('hwv5_d$1_prom_done.log')} if os.path.exists('hwv5_d$1_prom_done.log') else set()
for l in open('prom5_d$1_cost.txt'):
    m = re.match(r'^(\(.*\)) (\d+) (\d+) (\(.*\))$', l.strip())
    if m and float(m.group(3)) <= mc and m.group(1) not in done: n += 1
print(n)
PY
}
L13=$(left 13 $MC13); L14=$(left 14 $MC14)
if [ "$L13" = 0 ] && [ "$L14" = 0 ]; then
  NEW=$(next_stage $MAXFLOPS)
  if [ -n "$NEW" ]; then
    echo "*** MAXFLOPS stage advance $MAXFLOPS -> $NEW ($(date -u +%FT%TZ)): both lists exhausted under MC/$MAXFLOPS; the components skipped under $MAXFLOPS are redone"
    echo $NEW > maxflops_stage; MAXFLOPS=$NEW
    for f in claims5_p13/* claims5_p14/*; do [ -f "$f" ] && rm -f "$f"; done   # nothing is in progress (L13 = L14 = 0): every claim is done or skipped
    snapshot; L13=$(left 13 $MC13); L14=$(left 14 $MC14)
  fi
fi
[ "$L13" = 0 ] && { W14="$W14 $W13"; W13=""; }
[ "$L14" = 0 ] && { W13="$W13 $W14"; W14=""; }
echo "-- left under MAXCOST: d=13 $L13 (MC $MC13), d=14 $L14 (MC $MC14); MAXFLOPS stage $MAXFLOPS; slots d=13: [$W13], d=14: [$W14] --"
launch_deg() {  # degree maxcost worker-slots...
  DEG=$1; MC=$2; shift 2
  mkdir -p claims5_p$DEG
  for k in "$@"; do
    if ps -eo args | grep -v grep | grep -q "sweep_fast.py 5 1[34] 9,10 5 $k $NW noV"; then continue; fi   # slot busy (either degree)
    # drop the dead worker's claim files (components it claimed but did not finish)
    for f in claims5_p$DEG/*; do [ -f "$f" ] && [ "$(cat $f)" = "$k" ] && rm -f "$f"; done
    MEMCAP=67108864 MAXCOST=$MC MAXFLOPS=$MAXFLOPS ONLY=prom5_d$DEG.txt CLAIMDIR=claims5_p$DEG RESUME=hwv5_d${DEG}_prom_done.log \
      setsid nohup python3 -u sweep_fast.py 5 $DEG 9,10 5 $k $NW noV >> live/d${DEG}_w$k.log 2>&1 < /dev/null &
    echo "*** launched d=$DEG worker $k MAXCOST=$MC MAXFLOPS=$MAXFLOPS ($(date -u +%FT%TZ))"
  done
}
# a worker of degree D in slot k that is alive but was started without / with a different MAXCOST keeps running (its
# current component is finished, then it claims the next one under ITS bound); stale big claims are dropped by hand.
[ -n "$W13" ] && launch_deg 13 $MC13 $W13
[ -n "$W14" ] && launch_deg 14 $MC14 $W14
echo "-- progress --"
for d in 13 14; do [ -f prom5_d$d.txt ] && echo "d=$d: $(cnt hwv5_d${d}_prom_done.log) / $(grep -c . prom5_d$d.txt) components done, $(skp hwv5_d${d}_prom_done.log) skipped by MAXFLOPS"; done
python3 d13_report.py > agents/d13.md 2>/dev/null || echo "report failed"
cd .. && for f in hwv5_d13_prom_done.log hwv5_d14_prom_done.log maxflops_stage agents/d13.md agents/to-d7d8.md prom5_d13.txt prom5_d14.txt d13_checkin.sh d13_report.py make_prom5.py; do [ -f isotypic_flattenings/$f ] && git add isotypic_flattenings/$f; done
if ! git diff --cached --quiet; then
  git commit -q -m "d13 agent: C^5 rank 9 vs 10 d=13/14 status + logs $(date -u +%FT%H:%MZ) (d13 $(cnt isotypic_flattenings/hwv5_d13_prom_done.log), d14 $(cnt isotypic_flattenings/hwv5_d14_prom_done.log) components)

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Xqa6zjM98kkSHbEmfYGvTt"
  for i in 1 2 3 4; do git pull -q --rebase --autostash origin claude/wonderful-fermat-1v76ux && git push -q -u origin claude/wonderful-fermat-1v76ux && { echo "pushed"; break; }; sleep $((2**i)); done
else echo "nothing to commit"; fi
