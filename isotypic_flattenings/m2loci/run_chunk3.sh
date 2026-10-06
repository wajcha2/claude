#!/bin/bash
# chunk: pending follow-ups on 1 core while 3 workers continue the screen; then follow-ups of new screen failures (3 workers);
# then the d=11 tail.  Every worker resumes from ALL logs of its kind, so partitions may change between chunks.
cd /home/user/claude/isotypic_flattenings
export OPENBLAS_NUM_THREADS=1 MEMLIMIT_GB=3.5 MEMEL=4e7
allogs() { ls $1 2>/dev/null | tr '\n' ':' | sed 's/:$//'; }
needfull() {   # NEEDFULL lines -> 'lam dirn' jobs, cheapest first
  grep -h "NEEDFULL" $1 | sed -E 's/^lam=(.*) dir([0-9]) g=([0-9]+) n1=([0-9]+) n23=([0-9]+).*/\3 \4 \5|\1 \2/' \
    | awk -F'|' '{split($1,a," "); m=a[1]*a[2]; if (a[3]<m) m=a[3]; print a[1]*a[2]*m"|"$2}' | sort -t'|' -k1,1n | awk -F'|' '!seen[$2]++' \
    | cut -d'|' -f2 | awk '{d=$NF-1; $NF=""; print $0 d}' > $2
}
DLOGS="live/deep2_d1011_*.log live/deep2_sample_*.log live/deep2_d11tail_*.log"
needfull "live/screen_d1011_*.log" live/needfull_pending.txt
RESUME=$(allogs "$DLOGS") python3 m2deep2.py LIST live/needfull_pending.txt >> live/deep2_d1011_p.log 2>&1 &
PPID1=$!
screen3() {   # $1 jobs, $2 tag
  RS=$(allogs "live/screen_$2_*.log"); pids=""
  for w in 0 1 2; do RESUME=$RS SCREEN=1 python3 m2cmp2.py LIST $1 3000 $w 3 >> live/screen_$2_x$w.log 2>&1 & pids="$pids $!"; done
  wait $pids
}
deep3() {     # $1 tag : follow-ups of screen failures not in the pending list of the single worker
  needfull "live/screen_$1_*.log" live/needfull_$1.txt
  grep -vxF -f live/needfull_pending.txt live/needfull_$1.txt > live/needfull_$1_y.txt
  RD=$(allogs "$DLOGS"); pids=""
  for w in 0 1 2; do RESUME=$RD python3 m2deep2.py LIST live/needfull_$1_y.txt $w 3 >> live/deep2_$1_y$w.log 2>&1 & pids="$pids $!"; done
  wait $pids
}
screen3 m2loci/jobs_d1011_main.txt d1011;  echo "screen main done $(date -u +%H:%M)"
deep3 d1011;                                echo "deep main done $(date -u +%H:%M)"
screen3 m2loci/jobs_d11_tail.txt d11tail;   echo "screen tail done $(date -u +%H:%M)"
deep3 d11tail;                              echo "deep tail done $(date -u +%H:%M)"
wait $PPID1; echo "pending follow-ups done $(date -u +%H:%M)"
touch m2loci/run_chunk.alldone
