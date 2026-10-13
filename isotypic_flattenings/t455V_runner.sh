#!/bin/bash
# t455V_runner.sh: V-stack passes (sweep_fast WITHOUT noV: gN, HN and VN) for C^4 (x) C^5 (x) C^5, rank 8 vs 9, on the
# spare 4th core, one worker, degrees in the order of $VDEGREES (default "7 8").  Started detached by t455_checkin.sh:
#   setsid nohup bash t455V_runner.sh >> t455V_runner.log 2>&1 < /dev/null &
# Resumable: each degree logs to hwv455V_d<d>.log and resumes from it; a degree is finished when its log ends in FOUND.
# Added 2026-10-13 after the n x n x n rank-scan session reported (agents/to-all-Vstacks.md on its branch) that in the
# C^4^3 rank 6 vs 7 case 7 of the 8 degree-8 separators are visible only in V-stacks, which the noV sweep never computed.
MAIN=$(cd "$(dirname "$0")" && pwd); cd $MAIN
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1
for d in ${VDEGREES:-7 8}; do
  L=hwv455V_d$d.log
  if tail -1 $L 2>/dev/null | grep -q "^n=4,5,5 d=.* FOUND:"; then continue; fi
  rm -rf claims455V_d$d
  echo "Vrunner: d=$d start ($(date -u +%FT%TZ))"
  RESUME=$L CLAIMDIR=claims455V_d$d python3 sweep_fast.py 4,5,5 $d 8,9 5 0 1 >> $L 2>&1
  echo "Vrunner: d=$d exit $? ($(date -u +%FT%TZ))"
done
echo "Vrunner: all V degrees done ($(date -u +%FT%TZ))"
