#!/bin/bash
# d=10 + d=11 (cheapest 90%) screen (running) -> m2deep2 on NEEDFULL -> d=11 tail screen -> m2deep2 on its NEEDFULL
cd /home/user/claude/isotypic_flattenings
export OPENBLAS_NUM_THREADS=1 MEMLIMIT_GB=3.5 MEMEL=4e7
running() { ps -eo args | awk -v f="$1" '$1=="python3" && $2=="m2cmp2.py" && $4==f' | grep -c . ; }
needfull() { grep -h "NEEDFULL" $1 | sed -E 's/^lam=(.*) dir([0-9]) g=.*/\1 \2/' | awk '{d=$NF-1; $NF=""; print $0 d}' > $2; }
while [ "$(running m2loci/jobs_d1011_main.txt)" -gt 0 ]; do sleep 30; done
needfull "m2loci/screen_d1011_w*.log" m2loci/needfull_d1011.txt
for w in 0 1 2 3; do python3 m2deep2.py LIST m2loci/needfull_d1011.txt $w 4 > m2loci/deep2_d1011_w$w.log 2>&1 & done; wait
echo done > m2loci/pipeline3_main.done
for w in 0 1 2 3; do SCREEN=1 python3 m2cmp2.py LIST m2loci/jobs_d11_tail.txt 3000 $w 4 > m2loci/screen_d11tail_w$w.log 2>&1 & done; wait
needfull "m2loci/screen_d11tail_w*.log" m2loci/needfull_d11tail.txt
for w in 0 1 2 3; do python3 m2deep2.py LIST m2loci/needfull_d11tail.txt $w 4 > m2loci/deep2_d11tail_w$w.log 2>&1 & done; wait
echo done > m2loci/pipeline3_tail.done
