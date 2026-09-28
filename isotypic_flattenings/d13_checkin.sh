#!/bin/bash
# One check-in of the C^5 rank 9 vs 10 sweep at d = 13 / 14 (d13 agent): process status, OOM check, snapshot of the
# untracked live/ logs into the tracked hwv5_d<d>_prom_done.log, restart of dead workers (RESUME), agents/d13.md,
# commit + push (git pull --rebase --autostash first).  Usage: bash d13_checkin.sh [nworkers]   (default 4)
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1
NW=${1:-4}
mkdir -p live; touch hwv5_d13_prom_done.log hwv5_d14_prom_done.log
cnt() { local c; c=$(grep -c '^lam=' "$1" 2>/dev/null); echo ${c:-0}; }
echo "== $(date -u +'%Y-%m-%d %H:%M:%S UTC') =="
echo "-- processes --"; ps -eo pid,etime,rss,pcpu,args | awk '$5=="python3" && $7=="sweep_fast.py"' || echo "(none)"
echo "-- oom --"; (dmesg 2>/dev/null | grep -i oom | tail -2) || true
grep -h "oom_kill" /sys/fs/cgroup/memory.events 2>/dev/null || true
# snapshot: every finished component line of the live logs goes into the tracked done-log (union, sorted, unique)
for d in 13 14; do
  if ls live/d${d}_w*.log >/dev/null 2>&1; then
    cat hwv5_d${d}_prom_done.log live/d${d}_w*.log 2>/dev/null | grep '^lam=' | sort -u > hwv5_d${d}_prom_done.tmp
    mv hwv5_d${d}_prom_done.tmp hwv5_d${d}_prom_done.log
  fi
done
echo "-- hits / problems --"; grep -H "SEPARATES" hwv5_d13_prom_done.log hwv5_d14_prom_done.log live/d1[34]_w*.log 2>/dev/null || echo "no SEPARATES"
grep -H -i "error\|Traceback\|Killed\|MemoryError" live/d1[34]_w*.log 2>/dev/null | head -5 || true
# worker assignment: W13 / W14 list the worker slots (0..NW-1) that run d=13 / d=14 (interleaving since 2026-09-28 04:20 UTC:
# 3 workers on d=13, 1 on d=14, because the remaining d=13 components take > 6 h each).  A degree whose list is
# exhausted gets no launches; its slots are then handed to the other degree.
W13=${W13:-"0 1 2"}; W14=${W14:-"3"}
left() {  # components of degree $1 not yet in the done-log
  python3 - <<PY
import os
tot={l.strip() for l in open('prom5_d$1.txt') if l.strip()}
done={l.split(' g=')[0][4:].strip() for l in open('hwv5_d$1_prom_done.log')} if os.path.exists('hwv5_d$1_prom_done.log') else set()
print(len(tot-done))
PY
}
L13=$(left 13); L14=$(left 14)
[ "$L13" = 0 ] && { W14="$W14 $W13"; W13=""; }
[ "$L14" = 0 ] && { W13="$W13 $W14"; W14=""; }
echo "-- left: d=13 $L13, d=14 $L14; slots d=13: [$W13], d=14: [$W14] --"
launch_deg() {  # degree, worker slots
  DEG=$1; shift
  mkdir -p claims5_p$DEG
  for k in "$@"; do
    if ps -eo args | grep -v grep | grep -q "sweep_fast.py 5 $DEG 9,10 5 $k $NW noV"; then continue; fi
    # a worker that printed its FOUND line is finished for good (nothing left to claim): do not restart it
    if [ -f live/d${DEG}_w$k.log ] && tail -1 live/d${DEG}_w$k.log | grep -q "FOUND:" && [ "$(left $DEG)" = 0 ]; then continue; fi
    # drop the dead worker's claim files (components it claimed but did not finish)
    for f in claims5_p$DEG/*; do [ -f "$f" ] && [ "$(cat $f)" = "$k" ] && rm -f "$f"; done
    MEMCAP=67108864 ONLY=prom5_d$DEG.txt CLAIMDIR=claims5_p$DEG RESUME=hwv5_d${DEG}_prom_done.log \
      setsid nohup python3 -u sweep_fast.py 5 $DEG 9,10 5 $k $NW noV >> live/d${DEG}_w$k.log 2>&1 < /dev/null &
    echo "*** launched d=$DEG worker $k ($(date -u +%FT%TZ))"
  done
}
[ -n "$W13" ] && launch_deg 13 $W13
[ -n "$W14" ] && launch_deg 14 $W14
echo "-- progress --"
for d in 13 14; do [ -f prom5_d$d.txt ] && echo "d=$d: $(cnt hwv5_d${d}_prom_done.log) / $(grep -c . prom5_d$d.txt) components done"; done
python3 d13_report.py > agents/d13.md 2>/dev/null || echo "report failed"
cd .. && for f in hwv5_d13_prom_done.log hwv5_d14_prom_done.log agents/d13.md agents/to-d7d8.md prom5_d13.txt prom5_d14.txt d13_checkin.sh d13_report.py make_prom5.py; do [ -f isotypic_flattenings/$f ] && git add isotypic_flattenings/$f; done
if ! git diff --cached --quiet; then
  git commit -q -m "d13 agent: C^5 rank 9 vs 10 d=13/14 status + logs $(date -u +%FT%H:%MZ) (d13 $(cnt isotypic_flattenings/hwv5_d13_prom_done.log), d14 $(cnt isotypic_flattenings/hwv5_d14_prom_done.log) components)

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Xqa6zjM98kkSHbEmfYGvTt"
  for i in 1 2 3 4; do git pull -q --rebase --autostash origin claude/wonderful-fermat-1v76ux && git push -q -u origin claude/wonderful-fermat-1v76ux && { echo "pushed"; break; }; sleep $((2**i)); done
else echo "nothing to commit"; fi
