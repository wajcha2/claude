#!/bin/bash
cd /home/user/claude/isotypic_flattenings
export OPENBLAS_NUM_THREADS=1 MEMLIMIT_GB=3.5 MEMEL=4e7
running() { ps -eo args | awk -v f="$1" '$1=="python3" && $2=="m2cmp2.py" && $4==f' | grep -c . ; }
deepon() {   # $1 = screen log glob prefix, $2 = out tag
  grep -h "NEEDFULL" $1 | sed -E 's/^lam=(.*) dir([0-9]) g=.*/\1 \2/' | awk '{d=$NF-1; $NF=""; print $0 d}' > m2loci/needfull_$2.txt
  for w in 0 1 2 3; do python3 m2deep.py LIST m2loci/needfull_$2.txt $w 4 > m2loci/deep_$2_w$w.log 2>&1 & done; wait
}
screen() {   # $1 = job file, $2 = tag
  for w in 0 1 2 3; do SCREEN=1 python3 m2cmp2.py LIST $1 3000 $w 4 > m2loci/screen_$2_w$w.log 2>&1 & done; wait
}
while [ "$(running m2loci/jobs_d9_screen.txt)" -gt 0 ]; do sleep 30; done
deepon "m2loci/screen_d9_w*.log" d9;          echo d9 done > m2loci/pipeline_d9.done
screen m2loci/jobs_d8_screen.txt d8; deepon "m2loci/screen_d8_w*.log" d8; echo d8 done > m2loci/pipeline_d8.done
screen m2loci/jobs_d10_cand_full.txt d10; deepon "m2loci/screen_d10_w*.log" d10; echo d10 done > m2loci/pipeline_d10.done
