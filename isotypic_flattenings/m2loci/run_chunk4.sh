#!/bin/bash
# chunk: re-screen the NEEDFULL? (sample-capped) cases with KCAP 8000, screen the rest of the main list, follow-ups of valid
# screen failures, then the d=11 tail.  4 workers; every worker resumes from ALL logs of its kind.
cd /home/user/claude/isotypic_flattenings
export OPENBLAS_NUM_THREADS=1 MEMLIMIT_GB=3.5 MEMEL=4e7
allogs() { ls $1 2>/dev/null | tr '\n' ':' | sed 's/:$//'; }
screen4() {   # $1 jobs, $2 log prefix, $3 resume glob
  RS=$(allogs "$3"); pids=""
  for w in 0 1 2 3; do RESUME=$RS SCREEN=1 python3 m2cmp2.py LIST $1 8000 $w 4 >> live/$2_w$w.log 2>&1 & pids="$pids $!"; done
  wait $pids
}
deep4() {
  python3 m2loci/joblists.py followups
  RD=$(allogs "live/deep2_*.log"); pids=""
  for w in 0 1 2 3; do RESUME=$RD python3 m2deep2.py LIST live/needfull_valid.txt $w 4 >> live/deep2_d1011_z$w.log 2>&1 & pids="$pids $!"; done
  wait $pids
}
screen4 live/rescreen.txt screen_d1011_k "live/screen_d1011_k*.log"; echo "rescreen done $(date -u +%H:%M)"
screen4 m2loci/jobs_d1011_main.txt screen_d1011_k "live/screen_d1011_*.log"; echo "screen main done $(date -u +%H:%M)"
deep4;                                                            echo "follow-ups done $(date -u +%H:%M)"
screen4 m2loci/jobs_d11_tail.txt screen_d11tail_k "live/screen_d11tail_*.log"; echo "screen tail done $(date -u +%H:%M)"
deep4;                                                            echo "tail follow-ups done $(date -u +%H:%M)"
touch m2loci/run_chunk.alldone
