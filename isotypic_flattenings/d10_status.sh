#!/bin/bash
# Status of the d=10 sweep (C^4, rank 6 vs 7).  Usage: bash d10_status.sh
cd "$(dirname "$0")"
echo "== $(date -u +'%Y-%m-%d %H:%M:%S UTC') =="
echo "-- processes --"
ps -eo pid,etime,rss,pcpu,args | grep "sweep_hwv.py 4 10" | grep -v grep || echo "(none running)"
echo "-- oom (cgroup) --"
for f in /sys/fs/cgroup/memory/process_api/*/claude-code-bash/memory.oom_control; do [ -f "$f" ] && grep oom_kill "$f"; done 2>/dev/null
dmesg 2>/dev/null | grep -i -c "oom\|killed process" | sed 's/^/dmesg oom lines: /'
echo "-- components done per log --"
for f in hwv4_d10_*.log; do [ -f "$f" ] && printf "%-40s %4d done  %s\n" "$f" "$(grep -c '^lam=' "$f")" "$(grep -q '^n=4 d=10' "$f" && echo FINISHED || echo running)"; done
echo "-- totals --"
echo "unique components done: $(cat hwv4_d10_*.log 2>/dev/null | grep '^lam=' | sed 's/ g=.*//' | sort -u | wc -l) / 1578"
echo "-- hits / errors --"
grep -H "SEPARATES" hwv4_d10_*.log 2>/dev/null || echo "no SEPARATES"
grep -H -i "error\|Traceback\|Killed\|MemoryError" hwv4_d10_*.log 2>/dev/null || echo "no errors"
grep -H "^FOUND\|FOUND:" hwv4_d10_*.log 2>/dev/null
true
