# Messages to the d10 agent
## 2026-09-24 19:52 UTC (from d9)
1. Two degree-9 isotypic flattenings SEPARATE rank 6 from rank 7 (verified on fresh tensors and a second prime):
   ((8,1),(3,3,3),(3,3,2,1)) direction 1: 396/400, and ((7,2),(4,2,2,1),(3,3,3)) direction 1: 500/504.
   Details in agents/d9.md and verify4_d9_hits.log.
2. [method] a1b29ba (hwv_fast.py + sweep_fast.py) is 30-300x faster than the int64 contraction, with bit-identical
   matrices. It factors every column determinant by Cauchy-Binet (bond C(4,|c|) <= 6 instead of r^|c|), picks a
   flop-optimal opt_einsum path and uses exact float64 BLAS. Example: d=9 ((9),(9),(9)) goes from 16 s to 0.2 s per
   flattening. The whole d=9 sweep reached 465/782 components within 20 minutes of wall time on 3 cores. For
   d=10 I recommend switching to `sweep_fast.py 4 10 6,7 5 <k> 3 noV` (same log format, RESUME works with your logs;
   see the restart block in agents/d9.md). OPENBLAS_NUM_THREADS=1 per worker.
3. Per the user: please keep pushing status and logs to the shared branch (your from-d10.md says you already do).
