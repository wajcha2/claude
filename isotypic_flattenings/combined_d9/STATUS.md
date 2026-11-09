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

* **d9_455_dir0_B_p5** (4x5x5, source the C^4 factor, rank 8 vs 9; sources lam_1 >= 4 (14: also (4,4,1), (4,3,2), (4,3,1,1),
  (4,2,2,1)); family B, aux 1): the 149 targets of compressed size <= 2000 (361 larger ones skipped; members per target after
  dropping saturated ones from 1 to 14), every subset of at most 3 members at the levels 1 and g, 14494 subsets: **no
  separation** (largest drop 0).  2026-11-03 07:50 UTC, 1.9 h.

* **d9_555_B_p4** (5x5x5, rank 9 vs 10; sources lam_1 >= 5 (11: also (5,4), (5,3,1), (5,2,2), (5,2,1,1), (5,1,1,1,1)); family B,
  aux 1): the 67 targets of compressed size <= 3000 (419 larger ones skipped; members per target after dropping saturated ones:
  32 with 1, 10 with 2, 4 with 3, 2 with 4, 2 with 5, 4 with 9, 5 with 10, 8 with 11), every subset of at most 3 members at the
  levels 1 and g, 2584 subsets: **no separation** (largest drop 0).  2026-11-08 14:32 UTC, 7.4 h in all.

* **d9_555_B_p5** (5x5x5, rank 9 vs 10; sources lam_1 >= 4 (16: also (4,4,1), (4,3,2), (4,3,1,1), (4,2,2,1), (4,2,1,1,1)); family B,
  aux 1): the 53 targets of compressed size <= 2000 (461 larger ones skipped; members per target after dropping saturated ones
  from 1 to 16), every subset of at most 3 members at the levels 1 and g, 1732 subsets: **no separation** (largest drop 0).
  2026-11-08 16:59 UTC, 3.1 h.

* **d9_455_dir1_B_p4** (4x5x5, source a C^5 factor, rank 8 vs 9; sources lam_1 >= 5 (11); family B, aux 1): the 75 targets of
  compressed size <= 3000 (307 larger ones skipped; members per target after dropping saturated ones from 1 to 11), every subset
  of at most 3 members at the levels 1 and g, 4381 subsets: **no separation** (largest drop 0).  2026-11-08 19:42 UTC, 10 h in all.

* **d9_455_dir1_B_p5** (4x5x5, source a C^5 factor, rank 8 vs 9; sources lam_1 >= 4 (16); family B, aux 1): the 61 targets of
  compressed size <= 2000 (342 larger ones skipped; members per target after dropping saturated ones from 1 to 16), every subset
  of at most 3 members at the levels 1 and g, 7603 subsets: **no separation** (largest drop 0).  2026-11-08 22:01 UTC, 7.5 h.

* **d9_455_dir1_B_p3** (4x5x5, source a C^5 factor, rank 8 vs 9; sources lam_1 >= 6; family B, aux 1): the 142 targets of
  compressed size <= 8000 (193 larger ones skipped; members per target after dropping saturated ones: 43 with 1, 32 with 2, 18 with
  3, 13 with 4, 18 with 5, 18 with 6), every subset of the members at the levels 1 and g (`--exhaust 14`), 3514 subsets: **no
  separation** (largest drop 0).  2026-11-09 02:32 UTC.

* **d9_555_B_p4_mid** (5x5x5, rank 9 vs 10; sources lam_1 >= 5 (11); family B, aux 1): the 18 targets of compressed size
  3000..4500 (members per target after dropping saturated ones: 8 with 2, 2 with 8, 4 with 9, 2 with 10, 2 with 11), every subset
  of at most 3 members at the levels 1 and g, 3248 subsets: **no separation** (largest drop 0).  2026-11-09 05:43 UTC, 12.7 h.

* **d9_455_dir0_B_p5_mid** (4x5x5, source the C^4 factor, rank 8 vs 9; sources lam_1 >= 4 (14); family B, aux 1): the 44 targets of
  compressed size 2000..3000 (members per target after dropping saturated ones from 5 to 14), every subset of at most 3 members at the
  levels 1 and g, 15288 subsets: **no separation** (largest drop 0).  2026-11-09 10:52 UTC, 5.1 h.

* **d9_455_dir1_A1, sources (7,1,1) and (8,1)** (4x5x5, source a C^5 factor, rank 8 vs 9; family A aux 1, one pass without a flattening
  cache): 55 members (159 of 214 left out as saturated per the dir-1 B logs; 3 more saturated), all named groups, 1326 pairs,
  1000 triples, 100 random subsets and every all-but-one sum at levels 1 and g, 2616 subsets: **no separation** (largest drop 0;
  the sum of all members is S_(7,1,1) C^5, 1540).  2026-11-09 07:09 UTC, 4.6 h.
  Source (8,1): 46 members (61 of 107 left out per the B logs; 1 more saturated), 2254 subsets: **no separation** (largest drop
  0).  2026-11-09 14:10 UTC, 7.0 h.  Source (7,2) running.

## Running / queued (no separation so far)

* d9_455_dir1_B_big, d9_555_B_big (size 6000..25000); d9_455_dir1_B_p3 (source a C^5 factor, sources lam_1 >= 6);
  d9_455_dir0_B_p3_big (the 44 dir-0 lam_1 >= 6 targets of size 8000..15000).
