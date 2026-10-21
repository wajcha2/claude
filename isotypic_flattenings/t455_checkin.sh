#!/bin/bash
# One check-in of the C^4 (x) C^5 (x) C^5 sweep (rank 8 vs 9): status, restart dead workers / start the next job of
# t455_jobs.txt, regenerate agents/d10.md, commit+push logs and status to the shared branch (worktree) and own branch.
MAIN=$(cd "$(dirname "$0")" && pwd)
SHARED=${SHARED:-/home/user/claude-shared/isotypic_flattenings}
NW=3                                   # workers (cores minus one)
cd $MAIN
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1
. $MAIN/t455_helpers.sh             # tag/logf/alive/finished/launch/joblogs (job names: ONLY list or V = V-stack pass)
echo "== $(date -u +'%Y-%m-%d %H:%M:%S UTC') =="
echo "-- processes --"; ps -eo pid,etime,rss,pcpu,args | grep "[s]weep_fast.py 4,5,5" || echo "(none)"
echo "-- oom --"; grep oom_kill /sys/fs/cgroup/memory/process_api/*/claude-code-bash/memory.oom_control 2>/dev/null | tail -1
echo "-- hits / problems --"; grep -H "SEPARATES" hwv455_*.log hwv455V_*.log 2>/dev/null || echo "no SEPARATES"
grep -H -i "error\|Traceback\|Killed\|MemoryError" hwv455_*.log 2>/dev/null | head -5 || true
python3 t455_spancheck.py 2>&1 | head -10
echo "-- runner --"
if ps -eo args | grep -v grep | grep -q "bash t455_runner.sh"; then echo "runner alive"; else
  if tail -1 t455_runner.log 2>/dev/null | grep -q "all jobs of t455_jobs.txt complete"; then echo "*** ALL JOBS IN t455_jobs.txt COMPLETE ***"
  else echo "runner not running -> starting it"; setsid nohup bash t455_runner.sh >> t455_runner.log 2>&1 < /dev/null & sleep 3; fi; fi
tail -4 t455_runner.log 2>/dev/null
echo "-- V-stack runner (spare core) --"
if ps -eo args | grep -v grep | grep -q "bash t455V_runner.sh"; then echo "V runner alive"; tail -1 t455V_runner.log 2>/dev/null
elif tail -1 t455V_runner.log 2>/dev/null | grep -q "all V degrees done"; then echo "V runner: all V degrees done"
elif [ -f t455V_runner.sh ]; then echo "V runner not running -> starting it"; setsid nohup bash t455V_runner.sh >> t455V_runner.log 2>&1 < /dev/null & sleep 2; fi
for f in hwv455V_d*.log; do [ -f "$f" ] && echo "$f: $(grep -c '^lam=' $f) lines$(tail -1 $f | grep -q FOUND && echo ', finished')"; done
echo "-- jobs --"
while read d M O; do
  [ -z "$d" ] && continue; case $d in \#*) continue;; esac
  T=$(tag $d $M $O); st=""; NW=$(jobnw $d $M "$O")
  for k in $(seq 0 $((NW-1))); do
    L=$(logf $d $M "$O" $k)
    if finished $d $M "$O" $k; then st="$st F"; elif [ -f $L ] && alive $d $M "$O" $k; then st="$st R($(grep -c '^lam=' $L || true))"; else st="$st -"; fi
  done
  echo "$T:$st   ($(cat $(joblogs $d $M "$O") /dev/null 2>/dev/null | grep -c '^lam=') lines)"
done < t455_jobs.txt
NW=3
python3 t455_report.py > agents/d10.md
# push with retries (2, 4, 8, 16 s back-off) and the real exit status (a pipe into tail hid failures before)
push_retry() { local i; for i in 1 2 3 4 5; do git push -q origin "$1" 2>&1 | tail -1; [ ${PIPESTATUS[0]} -eq 0 ] && return 0; [ $i -lt 5 ] && { sleep $((2**i)); git pull -q --rebase --autostash origin "$1" 2>&1 | tail -1; }; done; return 1; }
# commit attribution footer: read from the git-excluded file .d10_commit_footer next to this script (recreate it from the session's attribution
# lines after a fresh clone); no footer if it is missing
FOOT=(); [ -s $MAIN/.d10_commit_footer ] && FOOT=(-m "$(cat $MAIN/.d10_commit_footer)")
if ! (cd $SHARED 2>/dev/null && git rev-parse --abbrev-ref HEAD 2>/dev/null | grep -q wonderful-fermat); then
  echo "!!! shared worktree $SHARED missing: cd /home/user/claude && git worktree add /home/user/claude-shared claude/wonderful-fermat-1v76ux"; exit 1; fi
cd $SHARED && git pull -q --rebase origin claude/wonderful-fermat-1v76ux 2>&1 | tail -2
mkdir -p agents && cp $MAIN/hwv455_*.log . 2>/dev/null; cp $MAIN/agents/d10.md agents/d10.md; cp $MAIN/agents/from-d10.md agents/from-d10.md 2>/dev/null
cp $MAIN/t455_checkin.sh $MAIN/t455_runner.sh $MAIN/t455_helpers.sh $MAIN/t455_report.py $MAIN/t455_eta.py $MAIN/t455_spancheck.py $MAIN/t455_common.py $MAIN/t455_jobs.txt .; cp $MAIN/t455_runner.log $MAIN/t455V_runner.log $MAIN/t455V_runner.sh $MAIN/hwv455V_*.log $MAIN/only455_*.txt . 2>/dev/null
git add hwv455_*.log hwv455V_*.log t455_runner.log t455V_runner.log agents/d10.md agents/from-d10.md t455_checkin.sh t455_runner.sh t455V_runner.sh t455_helpers.sh t455_report.py t455_eta.py t455_spancheck.py t455_common.py t455_jobs.txt only455_*.txt 2>/dev/null
git commit -q -m "d10 agent: C^4x5x5 status + logs $(date -u +%FT%H:%MZ) ($(cat hwv455_*.log 2>/dev/null | grep -c '^lam=') component lines)" "${FOOT[@]}" 2>/dev/null && echo "shared: committed" || echo "shared: nothing new"
push_retry claude/wonderful-fermat-1v76ux && echo "shared: pushed $(git rev-parse --short HEAD)" || echo "!!! shared: PUSH FAILED (retry at the next check-in)"
LAST=$(cat $MAIN/.d10_last_shared 2>/dev/null || echo c17b6d7); echo "-- shared commits since last check-in ($LAST): [method] ones marked --"
git log --format='%h %s' $LAST..HEAD | grep -v '^[0-9a-f]* d10' | sed 's/^\([0-9a-f]* \[method\]\)/*** \1/' || true; git rev-parse --short HEAD > $MAIN/.d10_last_shared
echo "-- messages to d10 (tail) --"; [ -f agents/to-d10.md ] && tail -12 agents/to-d10.md || echo "(none)"
cd $MAIN
# live logs are marked skip-worktree between check-ins (they grow continuously); clear the flag to commit them, then set it again
git ls-files hwv455_*.log hwv455V_*.log t455_runner.log t455V_runner.log | xargs -r git update-index --no-skip-worktree
git add hwv455_*.log hwv455V_*.log t455_runner.log t455V_runner.log agents/d10.md agents/from-d10.md t455_checkin.sh t455_runner.sh t455V_runner.sh t455_helpers.sh t455_report.py t455_eta.py t455_spancheck.py t455_common.py t455_jobs.txt only455_*.txt 2>/dev/null
if git commit -q -m "d10 agent: C^4x5x5 status + logs $(date -u +%FT%H:%MZ)" "${FOOT[@]}" 2>/dev/null || [ -n "$(git log origin/claude/tender-hopper-mcnmta..HEAD --oneline 2>/dev/null)" ]; then
  push_retry claude/tender-hopper-mcnmta && echo "own branch: pushed" || echo "!!! own branch: PUSH FAILED (retry at the next check-in)"
else echo "own branch: nothing new"; fi
git ls-files hwv455_*.log hwv455V_*.log t455_runner.log t455V_runner.log | xargs -r git update-index --skip-worktree
