#!/bin/bash
# Every 5 min: if fewer than 4 sweep workers are alive (a worker exits when nothing is left under its MAXCOST), run the
# check-in, which relaunches the free slots under the current stage (and snapshots/pushes).  Started with setsid nohup.
cd "$(dirname "$0")"
while true; do
  sleep 300
  n=$(ps -eo args | awk '$1=="python3" && $3=="sweep_fast.py"' | wc -l)
  if [ "$n" -lt 4 ]; then
    echo "keepalive: $n workers alive at $(date -u +%FT%TZ), running the check-in"
    bash d13_checkin.sh 4 2>&1 | grep -E "left under|launched|pushed|nothing"
  fi
done
