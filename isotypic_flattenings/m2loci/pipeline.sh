#!/bin/bash
# d=9 screen (already running) -> deep on NEEDFULL; then d=10 candidates screen -> deep on NEEDFULL
cd /home/user/claude/isotypic_flattenings
export OPENBLAS_NUM_THREADS=1 MEMLIMIT_GB=3.5 MEMEL=4e7
running() { ps -eo args | awk -v f="$1" '$1=="python3" && $2=="m2cmp2.py" && $4==f' | grep -c . ; }
while [ "$(running m2loci/jobs_d9_screen.txt)" -gt 0 ]; do sleep 30; done
grep -h "NEEDFULL" m2loci/screen_d9_w*.log | sed -E 's/^lam=(.*) dir([0-9]) g=.*/\1 \2/' | awk '{d=$NF-1; $NF=""; print $0 d}' > m2loci/needfull_d9.txt
for w in 0 1 2 3; do python3 m2deep.py LIST m2loci/needfull_d9.txt $w 4 > m2loci/deep_d9_w$w.log 2>&1 & done; wait
for w in 0 1 2 3; do SCREEN=1 python3 m2cmp2.py LIST m2loci/jobs_d10_cand_full.txt 3000 $w 4 > m2loci/screen_d10_w$w.log 2>&1 & done; wait
grep -h "NEEDFULL" m2loci/screen_d10_w*.log | sed -E 's/^lam=(.*) dir([0-9]) g=.*/\1 \2/' | awk '{d=$NF-1; $NF=""; print $0 d}' > m2loci/needfull_d10.txt
for w in 0 1 2 3; do python3 m2deep.py LIST m2loci/needfull_d10.txt $w 4 > m2loci/deep_d10_w$w.log 2>&1 & done; wait
echo done > m2loci/pipeline.done
