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

* **d9_555_B** (5x5x5, rank 9 vs 10; sources (8,1), (7,2), (7,1,1); family B, aux 1): the 198 targets of compressed size
  <= 6000 (the other 106 are in d9_555_B_big), every subset at every combination of the levels 1 and g: **no separation**.
  2026-10-23 22:50 UTC.

* **d9_455_dir0_AE** (4x5x5, source the C^4 factor, rank 8 vs 9; sources (8,1), (7,2), (7,1,1)): family A (fixed source,
  sums over targets) with the Kronecker spaces on the target side (aux 1) and with a shared X = C^2 on the source side
  (aux 2, family C), 6 lattices of 133-269 targets, 26591 subsets in all (saturated targets dropped, all transposed pairs,
  4000 random pairs, triples, random subsets, one greedy run); family E (reshaped single components, every k x l grid,
  k, l >= 2) on all 238 components with g >= 2: **no separation**.  2026-10-25 23:45 UTC.

* **d9_455_dir0_B_p3** (4x5x5, source the C^4 factor, rank 8 vs 9; sources lam_1 >= 6: (8,1), (7,2), (7,1,1), (6,3), (6,2,1),
  (6,1,1,1); family B, aux 1): 382 targets of compressed size <= 8000 (44 larger ones skipped), every subset of the sources at
  the levels 1 and g (`--exhaust 14`), 20475 subsets: **no separation**.  2026-11-02 11:40 UTC.

* **d9_555_B_p3** (5x5x5, rank 9 vs 10; sources lam_1 >= 6; family B, aux 1): 159 targets of compressed size <= 8000 (267 larger
  ones skipped), every subset of the sources at the levels 1 and g, 3503 subsets: **no separation**.  2026-11-02 13:10 UTC.

* **d9_455_dir0_B_p4** (4x5x5, source the C^4 factor, rank 8 vs 9; sources lam_1 >= 5: (8,1), (7,2), (7,1,1), (6,3), (6,2,1),
  (6,1,1,1), (5,4), (5,3,1), (5,2,2), (5,2,1,1); family B, aux 1): the 205 targets of compressed size <= 3000 (279 larger
  ones skipped; members per target after dropping saturated ones: 36 with 1, 18 with 2, 17 with 3, 34 with 4, 41 with 5,
  22 with 6, 18 with 7, 6 with 8, 4 with 9, 9 with 10), every subset of at most 3 members at the levels 1 and g
  (`--exhaust 14 --maxsub 3`), 12013 subsets: **no separation** (largest drop 0).  2026-11-03 03:48 UTC, 3.1 h.

## Running / queued (no separation so far)

* d9_455_dir1_B_big, d9_555_B_big (size 6000..25000); d9_455_dir1_B_p3 (source a C^5 factor, sources lam_1 >= 6);
  d9_455_dir0_B_p3_big (the 44 dir-0 lam_1 >= 6 targets of size 8000..15000).
