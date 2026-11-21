#!/bin/bash
# one line a minute: time, used memory, RSS (MB) of every python3 process
cd /home/user/claude/isotypic_flattenings/kronproj
while true; do
  echo "$(date +%H:%M:%S) used_MB=$(free -m | awk '/Mem:/{print $3}') rss_MB=$(ps -eo rss,args | awk '$2 ~ /python3$/ {printf "%d,", $1/1024}')" >> logs/jobs/mem.log
  sleep 60
done
