#!/bin/bash
# memlog.sh: every 60 s append used memory, the RSS (MB) of each comb_search worker and the free disk to logs/jobs/mem.log;
# every 10 min delete the cached flattenings of finished targets of the dir-1 / 5x5x5 jobs (cache_gc.py)
cd "$(dirname "$0")"
i=0
while true; do
  used=$(free -m | awk '/Mem:/ {print $3}')
  rss=$(for pid in $(pgrep -f 'combined/comb_search.py'); do awk '/VmRSS/ {printf "%d,", $2/1024}' /proc/$pid/status 2>/dev/null; done)
  disk=$(df -BG --output=avail / | tail -1 | tr -d " ")
  echo "$(date +%H:%M:%S) used_MB=$used rss_MB=$rss disk_avail=$disk" >> logs/jobs/mem.log
  i=$((i + 1))
  if [ $((i % 10)) -eq 0 ]; then echo "$(date +%H:%M:%S) $(python3 cache_gc.py)" >> logs/jobs/mem.log; fi
  sleep 60
done
