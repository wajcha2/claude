#!/bin/bash
# One check-in of the C^4 (x) C^5 (x) C^5 sweep (rank 8 vs 9): status, restart dead workers / start the next job of
# t455_jobs.txt, regenerate agents/d10.md, commit+push logs and status to the shared branch (worktree) and own branch.
MAIN=$(cd "$(dirname "$0")" && pwd)
SHARED=${SHARED:-/home/user/claude-shared/isotypic_flattenings}
NW=3                                   # workers (cores minus one)
cd $MAIN
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1
tag() { [ "$2" = inf ] && echo "d$1" || echo "d$1_max$2"; }
alive() { ps -eo args | grep -v grep | grep -q "sweep_fast.py 4,5,5 $1 8,9 5 $2 $NW noV"; }
finished() { [ -f hwv455_$1_w$2.log ] && tail -1 hwv455_$1_w$2.log | grep -q "^n=4,5,5 d=.* FOUND:"; }
launch() {  # d maxdim worker
  T=$(tag $1 $2); CD=claims455_$T; mkdir -p $CD
  for f in $CD/*; do [ -f "$f" ] && [ "$(cat $f)" = "$3" ] && rm -f "$f"; done      # drop the dead worker's claims
  ALL=$(ls hwv455_d$1*.log 2>/dev/null | tr '\n' ':')
  RESUME=$ALL MAXDIM=$2 CLAIMDIR=$CD setsid nohup python3 sweep_fast.py 4,5,5 $1 8,9 5 $3 $NW noV >> hwv455_${T}_w$3.log 2>&1 < /dev/null &
  echo "*** launched $T worker $3 -> hwv455_${T}_w$3.log ($(date -u +%FT%TZ))"
}
echo "== $(date -u +'%Y-%m-%d %H:%M:%S UTC') =="
echo "-- processes --"; ps -eo pid,etime,rss,pcpu,args | grep "[s]weep_fast.py 4,5,5" || echo "(none)"
echo "-- oom --"; grep oom_kill /sys/fs/cgroup/memory/process_api/*/claude-code-bash/memory.oom_control 2>/dev/null | tail -1
echo "-- hits / problems --"; grep -H "SEPARATES" hwv455_*.log 2>/dev/null || echo "no SEPARATES"
grep -H -i "error\|Traceback\|Killed\|MemoryError" hwv455_*.log 2>/dev/null | head -5 || true
grep -H "span=" hwv455_*.log 2>/dev/null | awk '{for(i=1;i<=NF;i++) if($i ~ /^span=/) s=$i; g=$0; sub(/.* g=/,"",g); sub(/ .*/,"",g); n=split(substr(s,6),a,","); for(j=1;j<=n;j++) if(a[j]!=g) {print "span<g: " $0; break}}' | head -5
echo "-- runner --"
if ps -eo args | grep -v grep | grep -q "bash t455_runner.sh"; then echo "runner alive"; else
  if tail -1 t455_runner.log 2>/dev/null | grep -q "all jobs of t455_jobs.txt complete"; then echo "*** ALL JOBS IN t455_jobs.txt COMPLETE ***"
  else echo "runner not running -> starting it"; setsid nohup bash t455_runner.sh >> t455_runner.log 2>&1 < /dev/null & sleep 3; fi; fi
tail -4 t455_runner.log 2>/dev/null
echo "-- jobs --"
while read d M; do
  [ -z "$d" ] && continue; case $d in \#*) continue;; esac
  T=$(tag $d $M); st=""
  for k in $(seq 0 $((NW-1))); do finished $T $k && st="$st F" || { alive $d $k && st="$st R($(grep -c '^lam=' hwv455_${T}_w$k.log 2>/dev/null))" || st="$st -"; }; done
  echo "$T:$st   ($(cat hwv455_${T}_w*.log 2>/dev/null | grep -c '^lam=') lines)"
done < t455_jobs.txt
python3 t455_report.py > agents/d10.md
if ! (cd $SHARED 2>/dev/null && git rev-parse --abbrev-ref HEAD 2>/dev/null | grep -q wonderful-fermat); then
  echo "!!! shared worktree $SHARED missing: cd /home/user/claude && git worktree add /home/user/claude-shared claude/wonderful-fermat-1v76ux"; exit 1; fi
cd $SHARED && git pull -q --rebase origin claude/wonderful-fermat-1v76ux 2>&1 | tail -2
mkdir -p agents && cp $MAIN/hwv455_*.log . 2>/dev/null; cp $MAIN/agents/d10.md agents/d10.md; cp $MAIN/agents/from-d10.md agents/from-d10.md 2>/dev/null
cp $MAIN/t455_checkin.sh $MAIN/t455_runner.sh $MAIN/t455_report.py $MAIN/t455_jobs.txt .; cp $MAIN/t455_runner.log . 2>/dev/null
git add hwv455_*.log t455_runner.log agents/d10.md agents/from-d10.md t455_checkin.sh t455_runner.sh t455_report.py t455_jobs.txt 2>/dev/null
git commit -q -m "d10 agent: C^4x5x5 status + logs $(date -u +%FT%H:%MZ) ($(cat hwv455_*.log 2>/dev/null | grep -c '^lam=') component lines)" 2>/dev/null && echo "shared: committed" || echo "shared: nothing new"
git push -q origin claude/wonderful-fermat-1v76ux 2>&1 | tail -1 && echo "shared: pushed $(git rev-parse --short HEAD)"
LAST=$(cat $MAIN/.d10_last_shared 2>/dev/null || echo c17b6d7); echo "-- shared commits since last check-in ($LAST): [method] ones marked --"
git log --format='%h %s' $LAST..HEAD | grep -v '^[0-9a-f]* d10' | sed 's/^\([0-9a-f]* \[method\]\)/*** \1/' || true; git rev-parse --short HEAD > $MAIN/.d10_last_shared
echo "-- messages to d10 (tail) --"; [ -f agents/to-d10.md ] && tail -12 agents/to-d10.md || echo "(none)"
cd $MAIN && git add hwv455_*.log t455_runner.log agents/d10.md agents/from-d10.md t455_checkin.sh t455_runner.sh t455_report.py t455_jobs.txt 2>/dev/null
git commit -q -m "d10 agent: C^4x5x5 status + logs $(date -u +%FT%H:%MZ)" 2>/dev/null && git push -q origin claude/tender-hopper-mcnmta 2>&1 | tail -1 && echo "own branch: pushed" || echo "own branch: nothing new"
