#!/bin/bash
# Every 5 min: if fewer than NWANT (default 3 since 2026-10-19: one d=14 worker + 2 V workers) sweep workers are alive (a worker exits when nothing is left under its MAXCOST), run the
# check-in, which relaunches the free slots under the current stage (and snapshots/pushes).  Started with setsid nohup.
# Exits after two consecutive check-ins that launched nothing (queue empty: the 2-hourly routine check-in takes over).
cd "$(dirname "$0")"
idle=0
while true; do
  sleep 300
  n=$(ps -eo args | awk '$1=="python3" && $3=="sweep_fast.py"' | wc -l)
  want=${NWANT:-$([ "$(cat vstack_deg 2>/dev/null)" = 9 ] && echo 2 || echo 3)}   # d=14 paused while V d=9 runs
  if [ "$n" -lt "$want" ]; then
    echo "keepalive: $n workers alive at $(date -u +%FT%TZ), running the check-in"
    out=$(bash d13_checkin.sh 4 2>&1)
    echo "$out" | grep -E "left under|launched|pushed|nothing"
    if echo "$out" | grep -q launched; then idle=0; else idle=$((idle+1)); fi
    if [ "$idle" -ge 2 ]; then echo "keepalive: nothing to launch twice, exiting at $(date -u +%FT%TZ)"; exit 0; fi
  fi
done
