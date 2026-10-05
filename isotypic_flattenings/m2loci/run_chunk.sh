#!/bin/bash
# resumable d=10/d=11 pipeline (follow-ups first); run as a tracked background task, re-run after a stop or container recycle.
cd /home/user/claude/isotypic_flattenings
export OPENBLAS_NUM_THREADS=1 MEMLIMIT_GB=3.5 MEMEL=4e7
needfull() {   # NEEDFULL lines of the screen logs -> 'lam dirn' jobs, cheapest first (cost g n1 min(g n1, n23))
  grep -h "NEEDFULL" $1 | sed -E 's/^lam=(.*) dir([0-9]) g=([0-9]+) n1=([0-9]+) n23=([0-9]+).*/\3 \4 \5|\1 \2/' \
    | awk -F'|' '{split($1,a," "); m=a[1]*a[2]; if (a[3]<m) m=a[3]; print a[1]*a[2]*m"|"$2}' | sort -t'|' -k1,1n | awk -F'|' '!seen[$2]++' \
    | cut -d'|' -f2 | awk '{d=$NF-1; $NF=""; print $0 d}' > $2
}
stage_screen() {   # $1 jobs, $2 tag
  for w in 0 1 2 3; do RESUME=live/screen_$2_w$w.log SCREEN=1 python3 m2cmp2.py LIST $1 3000 $w 4 >> live/screen_$2_w$w.log 2>&1 & done; wait
}
stage_deep() {     # $1 tag
  needfull "live/screen_$1_w*.log" live/needfull_$1.txt
  R=""; for x in live/deep2_$1_w*.log live/deep2_sample_w*.log; do R="$R:$x"; done
  for w in 0 1 2 3; do RESUME=${R#:} python3 m2deep2.py LIST live/needfull_$1.txt $w 4 >> live/deep2_$1_w$w.log 2>&1 & done; wait
}
stage_deep d1011;                               echo "deep (current screen failures) done $(date -u +%H:%M)"
stage_screen m2loci/jobs_d1011_main.txt d1011;  echo "screen main done $(date -u +%H:%M)"
stage_deep d1011;                               echo "deep main done $(date -u +%H:%M)"
stage_screen m2loci/jobs_d11_tail.txt d11tail;  echo "screen tail done $(date -u +%H:%M)"
stage_deep d11tail;                             echo "deep tail done $(date -u +%H:%M)"
touch m2loci/run_chunk.alldone
