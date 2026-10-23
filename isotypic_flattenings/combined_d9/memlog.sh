#!/bin/bash
# memlog.sh: every 60 s append used memory, the RSS (MB) of each comb_search worker and the free disk to logs/jobs/mem.log
cd "$(dirname "$0")"
while true; do
  used=$(free -m | awk '/Mem:/ {print $3}')
  rss=$(for pid in $(pgrep -f 'combined/comb_search.py'); do awk '/VmRSS/ {printf "%d,", $2/1024}' /proc/$pid/status 2>/dev/null; done)
  disk=$(df -BG --output=avail / | tail -1 | tr -d " ")
  echo "$(date +%H:%M:%S) used_MB=$used rss_MB=$rss disk_avail=$disk" >> logs/jobs/mem.log
  sleep 60
done
