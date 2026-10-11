#!/bin/bash
# t455_runner.sh: runs the jobs of t455_jobs.txt ("<d> <MAXDIM> [<name>]"; a name restricts the job to the components listed in
# only455_<name>.txt) one after another, NW workers each; started once, detached:
#   setsid nohup bash t455_runner.sh >> t455_runner.log 2>&1 < /dev/null &
# Finished jobs (all worker logs end with a FOUND line) are skipped; dead workers are restarted (at most 5 times each).
MAIN=$(cd "$(dirname "$0")" && pwd); cd $MAIN
NW=3
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1
tag() { local t; if [ "$2" = inf ]; then t=d$1; else t=d$1_max$2; fi; [ -n "$3" ] && t=${t}_$3; echo $t; }
alive() { ps -eo args | grep -v grep | grep -q "sweep_fast.py 4,5,5 $1 8,9 5 $2 $NW noV"; }
finished() { [ -f hwv455_$1_w$2.log ] && tail -1 hwv455_$1_w$2.log | grep -q "^n=4,5,5 d=.* FOUND:"; }
launch() {  # d maxdim worker [name]
  T=$(tag $1 $2 $4); CD=claims455_$T; mkdir -p $CD; O=""; [ -n "$4" ] && O=$MAIN/only455_$4.txt
  for f in $CD/*; do [ -f "$f" ] && [ "$(cat $f)" = "$3" ] && rm -f "$f"; done      # drop the dead worker's claims
  ALL=$(ls hwv455_d$1*.log 2>/dev/null | tr '\n' ':')
  RESUME=$ALL MAXDIM=$2 CLAIMDIR=$CD ONLY=$O setsid nohup python3 sweep_fast.py 4,5,5 $1 8,9 5 $3 $NW noV >> hwv455_${T}_w$3.log 2>&1 < /dev/null &
  echo "runner: launched $T worker $3 -> hwv455_${T}_w$3.log ($(date -u +%FT%TZ))"
}
declare -A RESTARTS
while true; do
  JOB=""
  while read d M O; do
    [ -z "$d" ] && continue; case $d in \#*) continue;; esac
    T=$(tag $d $M $O); ALLFIN=1
    for k in $(seq 0 $((NW-1))); do finished $T $k || ALLFIN=0; done
    [ $ALLFIN = 0 ] && { JOB="$d $M $O"; break; }
  done < t455_jobs.txt
  [ -z "$JOB" ] && { echo "runner: all jobs of t455_jobs.txt complete ($(date -u +%FT%TZ))"; exit 0; }
  set -- $JOB; d=$1; M=$2; O=$3; T=$(tag $d $M $O)
  echo "runner: job $T ($(date -u +%FT%TZ))"
  for k in $(seq 0 $((NW-1))); do finished $T $k || alive $d $k || launch $d $M $k $O; done
  while true; do
    sleep 60; ALLFIN=1
    for k in $(seq 0 $((NW-1))); do
      if ! finished $T $k; then
        ALLFIN=0
        if ! alive $d $k; then
          n=${RESTARTS[$T:$k]:-0}
          if [ $n -lt 5 ]; then RESTARTS[$T:$k]=$((n+1)); echo "runner: worker $k of $T died (restart $((n+1)))"; launch $d $M $k $O
          elif [ $n -eq 5 ]; then RESTARTS[$T:$k]=6; echo "runner: worker $k of $T died 5 times, giving up on it; job continues with the others"; fi
        fi
      fi
    done
    # a job whose remaining workers were all given up on counts as finished for the queue
    STUCK=1; for k in $(seq 0 $((NW-1))); do finished $T $k || [ "${RESTARTS[$T:$k]:-0}" = 6 ] || STUCK=0; done
    [ $ALLFIN = 1 ] || [ $STUCK = 1 ] && break
  done
  echo "runner: $T done ($(date -u +%FT%TZ))"
  [ $STUCK = 1 ] && [ $ALLFIN = 0 ] && { echo "runner: $T has abandoned workers; stopping the queue here"; exit 1; }
done
