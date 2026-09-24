#!/bin/bash
# One check-in of the d=10 sweep: status, restart dead slices / start next pass, regenerate agents/d10.md,
# commit+push logs and status to the shared branch (worktree) and to this session's own branch.
MAIN=$(cd "$(dirname "$0")" && pwd)                       # where the sweep runs and writes its logs (own branch)
SHARED=${SHARED:-/home/user/claude-shared/isotypic_flattenings}   # git worktree on the shared branch claude/wonderful-fermat-1v76ux
cd $MAIN
alive() { ps -eo args | grep -v grep | grep -q "sweep_hwv.py 4 10 6,7 5 $1 3 noV"; }
finished() { grep -lq "^n=4 d=10" hwv4_d10_$1_s$2.log hwv4_d10_$1_s$2_r*.log 2>/dev/null; }
launch() {  # pass slice
  case $1 in 1) MIN=0; MAX=150; PFX=max150;; 2) MIN=150; MAX=300; PFX=max300;; 3) MIN=300; MAX=0; PFX=max0;; esac
  N=$(ls hwv4_d10_${PFX}_s$2*.log 2>/dev/null | wc -l); SUF=""; [ "$N" -gt 0 ] && SUF="_r$N"
  if [ "$N" -ge 6 ]; then echo "!!! pass $1 slice $2 restarted $N times already; NOT restarting automatically"; return; fi
  ALL=$(ls hwv4_d10_*.log 2>/dev/null | tr '\n' ':')
  RESUME=$ALL MINDIM=$MIN MAXDIM=$MAX CHUNK=32 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 setsid nohup \
    python3 sweep_hwv.py 4 10 6,7 5 $2 3 noV > hwv4_d10_${PFX}_s$2$SUF.log 2>&1 < /dev/null &
  echo "*** launched pass $1 slice $2 -> hwv4_d10_${PFX}_s$2$SUF.log  ($(date -u +%FT%TZ))"
}
bash d10_status.sh
echo "-- pass state --"
for P in 1 2 3; do
  case $P in 1) PFX=max150;; 2) PFX=max300;; 3) PFX=max0;; esac
  ALLFIN=1
  for k in 0 1 2; do finished $PFX $k || ALLFIN=0; done
  if [ $ALLFIN = 1 ]; then echo "pass $P: complete"; continue; fi
  for k in 0 1 2; do
    if finished $PFX $k; then echo "pass $P slice $k: finished"
    elif alive $k; then echo "pass $P slice $k: running"
    else echo "pass $P slice $k: DEAD or not started -> launching"; launch $P $k; fi
  done
  break     # only the lowest unfinished pass is active
done
if [ "$ALLFIN" = 1 ]; then echo "*** ALL PASSES COMPLETE ***"; fi
python3 d10_report.py > agents/d10.md
# shared branch (worktree): pull --rebase, copy own files, commit, push
if [ ! -d $SHARED/.. ] || ! (cd $SHARED && git rev-parse --abbrev-ref HEAD 2>/dev/null | grep -q wonderful-fermat); then
  echo "!!! shared worktree $SHARED missing: cd /home/user/claude && git worktree add /home/user/claude-shared claude/wonderful-fermat-1v76ux"; exit 1; fi
cd $SHARED && git pull -q --rebase origin claude/wonderful-fermat-1v76ux 2>&1 | tail -2
mkdir -p agents && cp $MAIN/hwv4_d10_*.log . && cp $MAIN/agents/d10.md agents/d10.md && cp $MAIN/d10_status.sh $MAIN/d10_report.py $MAIN/d10_checkin.sh .
[ -f $MAIN/agents/from-d10.md ] && cp $MAIN/agents/from-d10.md agents/from-d10.md
git add hwv4_d10_*.log agents/d10.md agents/from-d10.md d10_status.sh d10_report.py d10_checkin.sh 2>/dev/null
git commit -q -m "d10: status + logs $(date -u +%FT%H:%MZ) ($(grep -c '^lam=' hwv4_d10_*.log | awk -F: '{s+=$2} END {print s}') component lines)" 2>/dev/null && echo "shared: committed" || echo "shared: nothing new"
git push -q origin claude/wonderful-fermat-1v76ux 2>&1 | tail -1 && echo "shared: pushed $(git rev-parse --short HEAD)"
echo "-- new [method] commits by others on shared (last 10) --"; git log --oneline -10 --grep='^\[method\]' | grep -v "d10" || true
echo "-- messages to d10 --"; [ -f agents/to-d10.md ] && tail -30 agents/to-d10.md || echo "(none)"
# own branch mirror
cd $MAIN && git add hwv4_d10_*.log agents/d10.md agents/from-d10.md d10_status.sh d10_report.py d10_checkin.sh 2>/dev/null
git commit -q -m "d10: status + logs $(date -u +%FT%H:%MZ)" 2>/dev/null && git push -q origin claude/tender-hopper-mcnmta 2>&1 | tail -1 && echo "own branch: pushed" || echo "own branch: nothing new"
