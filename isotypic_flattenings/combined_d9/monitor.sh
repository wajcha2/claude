#!/bin/bash
# monitor.sh -- event stream for the Claude Code Monitor tool (one line per event): new SEPARATES / Traceback / Error /
# Killed / final ' total ' / famA lines in logs/jobs/*.log, OOM kills from dmesg, memory above 13.5 GB used, runner not
# running, low disk.  The last-seen log lines and OOM count are kept in logs/jobs/.monitor_seen and .monitor_nk, so events
# that happen between two monitor windows are still reported by the next one (2026-11-23).
cd "$(dirname "$0")/logs/jobs" || exit 1
PAT='SEPARATES|Traceback|Error|Killed| total |^famA'
scan() { grep -H -E "$PAT" *.log 2>/dev/null | cut -c1-300 | sort; }
if [ -f .monitor_seen ]; then prev=$(cat .monitor_seen); else prev=$(scan); echo "$prev" > .monitor_seen; fi
k=$(dmesg 2>/dev/null | grep -c "Killed process")
nk=$(cat .monitor_nk 2>/dev/null || echo "$k"); [ "$nk" -gt "$k" ] && nk=$k     # dmesg restarts with the container
hw=0
while true; do
  cur=$(scan)
  comm -13 <(echo "$prev") <(echo "$cur") | grep -v '^$' | cut -c1-250
  prev="$cur"; echo "$cur" > .monitor_seen
  k=$(dmesg 2>/dev/null | grep -c "Killed process")
  if [ "$k" -gt "$nk" ]; then dmesg | grep "Killed process" | tail -n $((k-nk)) | cut -c1-160 | sed 's/^/OOM KILL: /'; fi
  nk=$k; echo "$nk" > .monitor_nk
  u=$(grep used_MB mem.log | tail -n 1 | sed 's/.*used_MB=\([0-9]*\).*/\1/')
  if [ "${u:-0}" -gt 13500 ] && [ $hw -eq 0 ]; then echo "MEMORY HIGH: used_MB=$u"; hw=1; fi
  [ "${u:-0}" -lt 12000 ] && hw=0
  pgrep -f '^python3 -u d9_jobs.py' >/dev/null || { echo "RUNNER NOT RUNNING"; sleep 900; }
  av=$(df -BG --output=avail / | tail -1 | tr -dc 0-9); [ "$av" -lt 5 ] && { echo "DISK LOW: ${av}G free"; sleep 600; }
  sleep 60
done
