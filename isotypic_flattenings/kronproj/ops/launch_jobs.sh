#!/bin/bash
# (re)start the kronproj job runner (resumable); safe to rerun after a container restart.
# After a FRESH container (logs/jobs missing), restore the last snapshot first: cp logs/jobs_snapshot/* logs/jobs/
cd /home/user/claude/isotypic_flattenings/kronproj
ps -eo args | awk '$1 ~ /python3$/ && /kp_jobs.py/' | grep -q . && { echo runner already running; exit 0; }
python3 -c 'import numpy, sympy, opt_einsum' 2>/dev/null || pip install -q numpy sympy opt_einsum
mkdir -p logs/jobs
[ -n "$(ls logs/jobs/*_part*.log 2>/dev/null)" ] || { echo "logs/jobs empty -- restoring logs/jobs_snapshot"; cp logs/jobs_snapshot/* logs/jobs/; }
nohup python3 -u kp_jobs.py jobs.txt 4 > logs/jobs/runner.out 2>&1 &
echo runner started
