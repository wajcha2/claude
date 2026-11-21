#!/bin/bash
# start the memory logger (process name memlog_loop) unless it is already running; run it in a Bash call of its own
cd /home/user/claude/isotypic_flattenings/kronproj
ps -eo args | awk '$1=="memlog_loop"{f=1} END{exit !f}' && exit 0
nohup bash -c 'exec -a memlog_loop bash ops/memlog_loop.sh' >/dev/null 2>&1 &
