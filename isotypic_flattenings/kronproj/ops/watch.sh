#!/bin/bash
# Monitor script (30 min): prints a line on a new SEPARATES line, a new kpB lattice line, a finished job,
# a dead runner, a relaunch loop or high memory; silent otherwise
cd /home/user/claude/isotypic_flattenings/kronproj
JOB=${JOB:-k555_d7_big2}   # the kpB job whose new lattice lines are reported
seen=$(cat logs/jobs/*.log 2>/dev/null | grep -c 'SEPARATES')
done0=$(grep -o "done: .*" logs/jobs/runner.status 2>/dev/null)
np0=$(ls logs/jobs/*_part*.log 2>/dev/null | wc -l)
kb0=$(cat logs/jobs/${JOB}_part*.log 2>/dev/null | grep -E '^kpB mn=' | grep 'tested=' | sort -u | wc -l)
while true; do
  n=$(cat logs/jobs/*.log 2>/dev/null | grep -c 'SEPARATES')
  if [ "$n" != "$seen" ]; then echo "$(date +%H:%M) NEW SEPARATES lines: $n (was $seen)"; grep -h 'SEPARATES' logs/jobs/*.log | tail -3 | cut -c1-300; seen=$n; fi
  d=$(grep -o "done: .*" logs/jobs/runner.status 2>/dev/null)
  if [ -n "$d" ] && [ "$d" != "$done0" ]; then echo "$(date +%H:%M) jobs $d"; done0=$d; fi
  ps -eo args | awk '$1 ~ /python3$/ && /kp_jobs.py/' | grep -q . || { echo "$(date +%H:%M) RUNNER NOT RUNNING"; sleep 600; }
  kb=$(cat logs/jobs/${JOB}_part*.log 2>/dev/null | grep -E '^kpB mn=' | grep 'tested=' | sort -u | wc -l)
  if [ "$kb" -gt "$kb0" ]; then echo "$(date +%H:%M) new $JOB kpB lattice line(s): $kb tested (was $kb0)"; grep -h -E '^kpB mn=' $(ls -t logs/jobs/${JOB}_part*.log | head -1) | tail -1 | cut -c1-160; kb0=$kb; fi
  np=$(ls logs/jobs/*_part*.log 2>/dev/null | wc -l)
  if [ $((np - np0)) -ge 2 ]; then echo "$(date +%H:%M) RELAUNCH LOOP? $((np - np0)) new part logs in a minute: $(ls -t logs/jobs/*_part*.log | head -2 | xargs -n1 basename)"; tail -3 $(ls -t logs/jobs/*_part*.log | head -1) | cut -c1-200; fi
  np0=$np
  mu=$(free -m | awk '/Mem:/{print $3}'); if [ "$mu" -gt 12500 ]; then echo "$(date +%H:%M) MEMORY HIGH used_MB=$mu: $(ps -eo rss,args --sort=-rss | awk '$2 ~ /python3$/ {printf "%d MB %s | ", $1/1024, $4}' | cut -c1-200)"; sleep 240; fi
  sleep 60
done
