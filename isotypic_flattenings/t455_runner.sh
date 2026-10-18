#!/bin/bash
# t455_runner.sh: runs the jobs of t455_jobs.txt ("<d> <MAXDIM> [<name>]", see t455_helpers.sh) one after another, NW workers
# each (NW = 3, or 4 from d = 10 on: jobnw in t455_helpers.sh); started once, detached:
#   setsid nohup bash t455_runner.sh >> t455_runner.log 2>&1 < /dev/null &
# Finished jobs (all worker logs end with a FOUND line) are skipped; dead workers are restarted (at most 5 times each).
MAIN=$(cd "$(dirname "$0")" && pwd); cd $MAIN
NW=3
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1
. $MAIN/t455_helpers.sh
declare -A RESTARTS
while true; do
  JOB=""
  while read d M O; do
    [ -z "$d" ] && continue; case $d in \#*) continue;; esac
    NW=$(jobnw $d $M "$O")
    ALLFIN=1
    for k in $(seq 0 $((NW-1))); do finished $d $M "$O" $k || ALLFIN=0; done
    [ $ALLFIN = 0 ] && { JOB="$d $M $O"; break; }
  done < t455_jobs.txt
  [ -z "$JOB" ] && { echo "runner: all jobs of t455_jobs.txt complete ($(date -u +%FT%TZ))"; exit 0; }
  set -- $JOB; d=$1; M=$2; O=$3; T=$(tag $d $M $O)
  echo "runner: job $T ($(date -u +%FT%TZ))"
  for k in $(seq 0 $((NW-1))); do finished $d $M "$O" $k || alive $d $M "$O" $k || launch $d $M "$O" $k; done
  while true; do
    sleep 60; ALLFIN=1
    for k in $(seq 0 $((NW-1))); do
      if ! finished $d $M "$O" $k; then
        ALLFIN=0
        if ! alive $d $M "$O" $k; then
          n=${RESTARTS[$T:$k]:-0}
          if [ $n -lt 5 ]; then RESTARTS[$T:$k]=$((n+1)); echo "runner: worker $k of $T died (restart $((n+1)))"; launch $d $M "$O" $k
          elif [ $n -eq 5 ]; then RESTARTS[$T:$k]=6; echo "runner: worker $k of $T died 5 times, giving up on it; job continues with the others"; fi
        fi
      fi
    done
    # a job whose remaining workers were all given up on counts as finished for the queue
    STUCK=1; for k in $(seq 0 $((NW-1))); do finished $d $M "$O" $k || [ "${RESTARTS[$T:$k]:-0}" = 6 ] || STUCK=0; done
    [ $ALLFIN = 1 ] || [ $STUCK = 1 ] && break
  done
  echo "runner: $T done ($(date -u +%FT%TZ))"
  [ $STUCK = 1 ] && [ $ALLFIN = 0 ] && { echo "runner: $T has abandoned workers; stopping the queue here"; exit 1; }
done
