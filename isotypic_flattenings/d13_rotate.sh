#!/bin/bash
# Wait until a legacy worker (started without MAXCOST) finishes its current component (its live log gains a 'lam=' line),
# then stop it, release its unfinished claims and run the check-in, which relaunches the slot under the cost policy.
# Usage: bash d13_rotate.sh <pid> <degree> <slot>
cd "$(dirname "$0")"
PID=$1; DEG=$2; K=$3; LOG=live/d${DEG}_w$K.log
n0=$(grep -c '^lam=' $LOG)
while kill -0 $PID 2>/dev/null; do
  sleep 30
  n=$(grep -c '^lam=' $LOG)
  if [ "$n" -gt "$n0" ]; then
    kill $PID; sleep 2
    echo "rotate: stopped legacy d=$DEG worker $K (pid $PID) after component $n at $(date -u +%FT%TZ)"
    PYTHONDONTWRITEBYTECODE=1 python3 - <<PY
import itertools, os, glob
from isoflat import partitions
onlyset = {tuple(tuple(x) for x in eval(l)) for l in open('prom5_d$DEG.txt') if l.strip()}
done = {l.split(' g=')[0][4:].strip() for l in open('hwv5_d${DEG}_prom_done.log') if l.startswith('lam=')}
done |= {l.split(' g=')[0][4:].strip() for l in open('$LOG') if l.startswith('lam=')}
idx = {li: lam for li, lam in enumerate(itertools.combinations_with_replacement(partitions($DEG, 5), 3)) if lam in onlyset}
for f in sorted(glob.glob('claims5_p$DEG/*')):
    lam = idx[int(os.path.basename(f))]
    if repr(lam) not in done and open(f).read().strip() == '$K':
        os.remove(f); print('rotate: released claim', lam)
PY
    bash d13_checkin.sh 4 2>&1 | grep -E "left under|launched|pushed"
    exit 0
  fi
done
echo "rotate: pid $PID exited on its own at $(date -u +%FT%TZ)"
