#!/bin/bash
# 4x4x4 rank 6 vs 7: d = 5, 6 (one worker), d = 7 (workers 0-2); methods line flag pflag
cd "$(dirname "$0")/.."
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
(python3 -u specialscan.py 4 5 all 6 line flag pflag >> special/logs/n4_d5.log 2>&1; python3 -u specialscan.py 4 6 all 6 line flag pflag >> special/logs/n4_d6.log 2>&1) < /dev/null &
for w in 0 1 2; do
  WORKER=$w NWORKERS=3 OUT=special/res/n4_d7_w$w.jsonl python3 -u specialscan.py 4 7 all 6 line flag pflag >> special/logs/n4_d7_w$w.log 2>&1 < /dev/null &
done
wait
