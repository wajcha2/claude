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
# which degree is active: d=13 until every listed component is done, then d=14 (interleaving is done by hand: DEG env)
active() {  # prints the degree the workers should run
  for d in 13 14; do
    [ -f prom5_d$d.txt ] || continue
    tot=$(grep -c . prom5_d$d.txt); done=$(cnt hwv5_d${d}_prom_done.log)
    [ "$done" -lt "$tot" ] && { echo $d; return; }
  done
  echo none
}
DEG=${DEG:-$(active)}
echo "-- active degree: $DEG --"
if [ "$DEG" != none ]; then
  mkdir -p claims5_p$DEG
  for k in $(seq 0 $((NW-1))); do
    if ps -eo args | grep -v grep | grep -q "sweep_fast.py 5 $DEG 9,10 5 $k $NW noV"; then continue; fi
    # a worker that printed its FOUND line is finished for good (nothing left to claim): do not restart it
    if [ -f live/d${DEG}_w$k.log ] && tail -1 live/d${DEG}_w$k.log | grep -q "FOUND:"; then
      # but if new components remain unclaimed (e.g. a claim of a dead worker was removed), restart anyway
      left=$(python3 - <<PY
import os
tot={l.strip() for l in open('prom5_d$DEG.txt') if l.strip()}
done={l.split(' g=')[0][4:].strip() for l in open('hwv5_d${DEG}_prom_done.log')} if os.path.exists('hwv5_d${DEG}_prom_done.log') else set()
print(len(tot-done))
PY
)
      [ "$left" = 0 ] && continue
    fi
    # drop the dead worker's claim files (components it claimed but did not finish)
    for f in claims5_p$DEG/*; do [ -f "$f" ] && [ "$(cat $f)" = "$k" ] && rm -f "$f"; done
    MEMCAP=67108864 ONLY=prom5_d$DEG.txt CLAIMDIR=claims5_p$DEG RESUME=hwv5_d${DEG}_prom_done.log \
      setsid nohup python3 -u sweep_fast.py 5 $DEG 9,10 5 $k $NW noV >> live/d${DEG}_w$k.log 2>&1 < /dev/null &
    echo "*** launched d=$DEG worker $k ($(date -u +%FT%TZ))"
  done
fi
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
