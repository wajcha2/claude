#!/bin/bash
# t455V_runner.sh: V-stack passes (sweep_fast WITHOUT noV: gN, HN and VN) for C^4 (x) C^5 (x) C^5, rank 8 vs 9, on the
# spare 4th core, worker id 0, degrees in the order of $VDEGREES (default "7 8").  Started detached by t455_checkin.sh:
#   setsid nohup bash t455V_runner.sh >> t455V_runner.log 2>&1 < /dev/null &
# Resumable: degree d logs to hwv455V_d<d>.log and resumes from all hwv455V_d<d>*.log; a degree is finished for this
# runner when its log ends in FOUND.  The claim directory claims455V_d<d> is shared with the main runner's V jobs
# ("<d> inf V" in t455_jobs.txt, worker ids 1..3, see t455_helpers.sh), so only this worker's own claims are dropped.
# Added 2026-10-13 after the n x n x n rank-scan session reported (agents/to-all-Vstacks.md on its branch) that in the
# C^4^3 rank 6 vs 7 case 7 of the 8 degree-8 separators are visible only in V-stacks, which the noV sweep never computed.
MAIN=$(cd "$(dirname "$0")" && pwd); cd $MAIN
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1
for d in ${VDEGREES:-7 8}; do
  L=hwv455V_d$d.log; CD=claims455V_d$d
  if tail -1 $L 2>/dev/null | grep -q "^n=4,5,5 d=.* FOUND:"; then continue; fi
  mkdir -p $CD; for f in $CD/*; do [ -f "$f" ] && [ "$(cat $f)" = "0" ] && rm -f "$f"; done
  echo "Vrunner: d=$d start ($(date -u +%FT%TZ))"
  RESUME=$(ls hwv455V_d$d*.log 2>/dev/null | tr '\n' ':') CLAIMDIR=$CD python3 sweep_fast.py 4,5,5 $d 8,9 5 0 4 >> $L 2>&1
  echo "Vrunner: d=$d exit $? ($(date -u +%FT%TZ))"
done
echo "Vrunner: all V degrees done ($(date -u +%FT%TZ))"
