# degree-9 combined flattenings: status

Started 2026-10-22 20:54 UTC (runner `d9_jobs.py jobs_d9.txt 4`).  Live logs in `logs/jobs/` (untracked), snapshots in
`logs/jobs_snapshot/` (with `report.md`).  Hits: `grep SEPARATES logs/jobs_snapshot/*.log`.  Summary table: `python3 d9_report.py`.

## Finished

* **d9_455_dir0_B** (4x5x5, source the C^4 factor, rank 8 vs 9; sources (8,1), (7,2), (7,1,1); family B with the Kronecker
  spaces on the source side (aux 1) and family D (shared Y = C^2, aux 2)): all 304 targets, both aux, 608 lattices
  (members per target: 77 with 1, 96 with 2, 131 with 3), every subset at every combination of the levels 1 and g
  (4874 subsets): **no separation** (largest drop 0).  2026-10-23 18:54 UTC.

* **d9_455_dir1_B** (4x5x5, source a C^5 factor, rank 8 vs 9; sources (8,1), (7,2), (7,1,1); family B, aux 1): the 164
  targets of compressed size <= 6000 (the other 78 are in d9_455_dir1_B_big), every subset at every combination of the
  levels 1 and g: **no separation**.  2026-10-23 20:30 UTC.

## Running / queued (no separation so far)

* d9_555_B (family B, size <= 6000), d9_455_dir1_B_big, d9_555_B_big (size 6000..25000),
  d9_455_dir0_AE (family A with aux 1, 2: sources (7,1,1), (8,1), (7,2) aux 1 done, (7,2) aux 2 running; then family E).
