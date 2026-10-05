#!/bin/bash
# chunk: the last (largest) follow-up on 1 core while 3 workers continue the screen; then follow-ups of new screen failures; then the d=11 tail.
cd /home/user/claude/isotypic_flattenings
export OPENBLAS_NUM_THREADS=1 MEMLIMIT_GB=3.5 MEMEL=4e7
allogs() { ls $1 2>/dev/null | tr '\n' ':' | sed 's/:$//'; }
needfull() {   # NEEDFULL lines -> 'lam dirn' jobs, cheapest first
  grep -h "NEEDFULL" $1 | sed -E 's/^lam=(.*) dir([0-9]) g=([0-9]+) n1=([0-9]+) n23=([0-9]+).*/\3 \4 \5|\1 \2/' \
    | awk -F'|' '{split($1,a," "); m=a[1]*a[2]; if (a[3]<m) m=a[3]; print a[1]*a[2]*m"|"$2}' | sort -t'|' -k1,1n | awk -F'|' '!seen[$2]++' \
    | cut -d'|' -f2 | awk '{d=$NF-1; $NF=""; print $0 d}' > $2
}
LAST="((6, 2, 1, 1), (6, 2, 1, 1), (6, 2, 1, 1)) 2"
echo "$LAST" > live/last_followup.txt
RESUME=$(allogs "live/deep2_d1011_*.log live/deep2_sample_*.log") python3 m2deep2.py LIST live/last_followup.txt >> live/deep2_d1011_last.log 2>&1 &
LASTPID=$!
screen3() {   # $1 jobs, $2 tag : 3 workers, each resuming from ALL screen logs of the tag
  RS=$(allogs "live/screen_$2_*.log"); pids=""
  for w in 0 1 2; do RESUME=$RS SCREEN=1 python3 m2cmp2.py LIST $1 3000 $w 3 >> live/screen_$2_x$w.log 2>&1 & pids="$pids $!"; done
  wait $pids
}
deep3() {     # $1 tag : follow-ups of all screen failures of the tag, 3 workers, skipping LAST while it runs
  needfull "live/screen_$1_*.log" live/needfull_$1.txt
  grep -vF "$LAST" live/needfull_$1.txt > live/needfull_$1_x.txt
  RD=$(allogs "live/deep2_d1011_*.log live/deep2_sample_*.log live/deep2_$1_*.log"); pids=""
  for w in 0 1 2; do RESUME=$RD python3 m2deep2.py LIST live/needfull_$1_x.txt $w 3 >> live/deep2_$1_x$w.log 2>&1 & pids="$pids $!"; done
  wait $pids
}
screen3 m2loci/jobs_d1011_main.txt d1011;  echo "screen main done $(date -u +%H:%M)"
deep3 d1011;                                echo "deep main done $(date -u +%H:%M)"
screen3 m2loci/jobs_d11_tail.txt d11tail;   echo "screen tail done $(date -u +%H:%M)"
deep3 d11tail;                              echo "deep tail done $(date -u +%H:%M)"
wait $LASTPID; echo "last follow-up done $(date -u +%H:%M)"
touch m2loci/run_chunk.alldone
