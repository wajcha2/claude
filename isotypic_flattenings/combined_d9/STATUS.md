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

* **d9_455_dir0_B_p3_big** (4x5x5, source the C^4 factor, rank 8 vs 9; sources lam_1 >= 6; family B, aux 1): the 44 targets of
  compressed size 8888..14340 that d9_455_dir0_B_p3 skipped (6 members each), every subset of the members at the levels 1 and g
  (`--exhaust 14`), 6036 subsets: **no separation** (largest drop 0).  2026-11-22 14:28 UTC (10 parts; two OOM kills, at 6.8
  and 9.85 GB, the last 4 targets alone with hint 11.76 GB; a fresh container on 2026-11-21 cost target 41 once).  **With
  d9_455_dir0_B_p3 every one of the 426 dir-0 targets of the lam_1 >= 6 sources is done, with every subset of its members.**

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

* **d9_455_dir0_B_p5_all** (4x5x5, source the C^4 factor, rank 8 vs 9; sources lam_1 >= 4 (14); family B, aux 1): the same 149
  targets of compressed size <= 2000 as d9_455_dir0_B_p5 (members per target after dropping saturated ones from 1 to 14), now
  with EVERY subset of the members at the levels 1 and g (`--exhaust 14`, no `--maxsub`; supersets of a saturated subset are
  pruned), 75816 subsets: **no separation** (largest drop 0).  2026-11-22 05:05 UTC, 5.6 h, next to d9_455_dir0_B_p3_big.

* **d9_555_B_p4** (5x5x5, rank 9 vs 10; sources lam_1 >= 5 (11: also (5,4), (5,3,1), (5,2,2), (5,2,1,1), (5,1,1,1,1)); family B,
  aux 1): the 67 targets of compressed size <= 3000 (419 larger ones skipped; members per target after dropping saturated ones:
  32 with 1, 10 with 2, 4 with 3, 2 with 4, 2 with 5, 4 with 9, 5 with 10, 8 with 11), every subset of at most 3 members at the
  levels 1 and g, 2584 subsets: **no separation** (largest drop 0).  2026-11-08 14:32 UTC, 7.4 h in all.

* **d9_555_B_p5** (5x5x5, rank 9 vs 10; sources lam_1 >= 4 (16: also (4,4,1), (4,3,2), (4,3,1,1), (4,2,2,1), (4,2,1,1,1)); family B,
  aux 1): the 53 targets of compressed size <= 2000 (461 larger ones skipped; members per target after dropping saturated ones
  from 1 to 16), every subset of at most 3 members at the levels 1 and g, 1732 subsets: **no separation** (largest drop 0).
  2026-11-08 16:59 UTC, 3.1 h.

* **d9_555_B_p5_all** (5x5x5, rank 9 vs 10; sources lam_1 >= 4 (16); family B, aux 1): the same 53 targets of compressed size
  <= 2000 as d9_555_B_p5 (members per target after dropping saturated ones from 1 to 16), now with EVERY subset of the members
  at the levels 1 and g (`--exhaust 16`; supersets of a saturated subset are pruned), 9112 subsets: **no separation** (largest
  drop 0).  2026-11-22 09:48 UTC, 4.7 h, next to d9_455_dir0_B_p3_big.

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

* **d9_455_dir1_A1** (family A of a C^5 source, all three sources (7,1,1), (8,1), (7,2)) (4x5x5, source a C^5 factor, rank 8 vs 9; family A aux 1, one pass without a flattening
  cache): 55 members (159 of 214 left out as saturated per the dir-1 B logs; 3 more saturated), all named groups, 1326 pairs,
  1000 triples, 100 random subsets and every all-but-one sum at levels 1 and g, 2616 subsets: **no separation** (largest drop 0;
  the sum of all members is S_(7,1,1) C^5, 1540).  2026-11-09 07:09 UTC, 4.6 h.
  Source (8,1): 46 members (61 of 107 left out per the B logs; 1 more saturated), 2254 subsets: **no separation** (largest drop
  0).  2026-11-09 14:10 UTC, 7.0 h.  Source (7,2): 48 members (161 of 209 left out; 3 more saturated), 2255 subsets: **no
  separation** (largest drop 0).  2026-11-09 19:36 UTC, 5.4 h.  Job finished: 17.0 h in all, peak about 3 GB.

* **d9_455_dir1_B_p4_mid** (4x5x5, source a C^5 factor, rank 8 vs 9; sources lam_1 >= 5 (11); family B, aux 1): the 20 targets of
  compressed size 3000..4500 (members per target after dropping saturated ones from 2 to 11), every subset of at most 3 members at
  the levels 1 and g, 4397 subsets: **no separation** (largest drop 0).  2026-11-09 18:48 UTC, 20.7 h.

* **d9_455_dir1_B_p5_mid** (4x5x5, source a C^5 factor, rank 8 vs 9; sources lam_1 >= 4 (16); family B, aux 1): the 22 targets of
  compressed size 2000..3000 (members per target after dropping saturated ones from 1 to 16), every subset of at most 3 members at
  the levels 1 and g, 6759 subsets: **no separation** (largest drop 0).  2026-11-10 02:22 UTC.

* **d9_455_dir1_B_p5_mid2** (4x5x5, source a C^5 factor, rank 8 vs 9; sources lam_1 >= 4 (16); family B, aux 1): the 11 targets
  of compressed size 3000..4000 (members per target after dropping saturated ones from 5 to 16).  The 8 targets with at most 14
  members: every subset of at most 3 members at the levels 1 and g.  The 3 targets with 15 or 16 members (5211|32211,
  6111|51111, 3321|333): every pair and every triple of full members, the all-but-one sums, the named groups, 300 random subsets
  and 2 greedy runs.  7728 subsets in all: **no separation** (largest drop 0).  2026-11-21 16:40 UTC (10 parts, 59151 s of
  computing; the 15-member target alone took ~18 h, with its subset dims saved across restarts).  With dir1_B_p5 and p5_mid
  every 4x5x5 dir-1 lam_1 >= 4 target of compressed size up to 4000 is covered.

* **d9_555_B_p5_mid** (5x5x5, rank 9 vs 10; sources lam_1 >= 4 (16); family B, aux 1): the 22 targets of compressed size
  2000..3000 (members per target after dropping saturated ones from 1 to 16), every subset of at most 3 members at the levels 1 and
  g, 5912 subsets: **no separation** (largest drop 0).  2026-11-10 03:50 UTC.

* **d9_555_B_p5_mid2** (5x5x5, rank 9 vs 10; sources lam_1 >= 4 (16); family B, aux 1): the 14 targets of compressed size
  3000..4000 (members per target after dropping saturated ones from 5 to 16), every subset of at most 3 members at the levels 1
  and g, 9680 subsets: **no separation** (largest drop 0).  2026-11-20 05:52 UTC (4 parts).  With p5 and p5_mid every 5x5x5
  lam_1 >= 4 target of compressed size up to 4000 is covered.

* **d9_455_dir0_B_p5_mid2** (4x5x5, source the C^4 factor, rank 8 vs 9; sources lam_1 >= 4 (14); family B, aux 1): the 51 targets of
  compressed size 3000..4000 (members per target after dropping saturated ones from 8 to 14), every subset of at most 3 members at
  the levels 1 and g, 22953 subsets: **no separation** (largest drop 0).  2026-11-10 13:13 UTC, 9.4 h.

* **d9_455_dir0_B_p5_mid3** (4x5x5, source the C^4 factor, rank 8 vs 9; sources lam_1 >= 4 (14); family B, aux 1): the 30 targets of
  compressed size 4000..5000 (members per target after dropping saturated ones from 9 to 14), every subset of at most 3 members at
  the levels 1 and g, 18408 subsets: **no separation** (largest drop 0).  2026-11-10 23:20 UTC, 10.5 h.

* **d9_455_dir0_B_p5_mid4** (4x5x5, source the C^4 factor, rank 8 vs 9; sources lam_1 >= 4 (14); family B, aux 1): the 24 targets of
  compressed size 5000..6000 (members per target after dropping saturated ones from 11 to 14), every subset of at most 3 members at
  the levels 1 and g, 15758 subsets: **no separation** (largest drop 0).  2026-11-10 23:54 UTC, 10.6 h.

* **d9_455_dir0_B_p5_mid5** (4x5x5, source the C^4 factor, rank 8 vs 9; sources lam_1 >= 4 (14); family B, aux 1): the 57 targets of
  compressed size 6000..8000 (members per target after dropping saturated ones from 11 to 14), every subset of at most 3 members at
  the levels 1 and g, 40459 subsets: **no separation** (largest drop 0).  2026-11-18 14:58 UTC (6 parts across the container
  stops and restarts since 2026-11-11; the last part 9.9 h).

* **d9_455_dir0_B_p5_mid6** (4x5x5, source the C^4 factor, rank 8 vs 9; sources lam_1 >= 4 (14); family B, aux 1): the 36 targets of
  compressed size 8000..11000 (members per target after dropping saturated ones from 11 to 14), every subset of at most 3 members
  at the levels 1 and g, 25688 subsets: **no separation** (largest drop 0).  2026-11-19 06:36 UTC (7 parts since 2026-11-11).
  With mid..mid6 every dir-0 lam_1 >= 4 target of compressed size up to 11000 is covered.

* **d9_555_A1, sources (7,1,1), (8,1) and (7,2)** (5x5x5, rank 9 vs 10; family A aux 1, one pass without a flattening cache): 63 members (206 of
  269 left out as saturated per the 5x5x5 B logs; 7 more saturated), all named groups, pairs, 1000 triples, 100 random subsets
  and every all-but-one sum at levels 1 and g, 2892 subsets: **no separation** (largest drop 0).  2026-11-10 23:59 UTC, 11.1 h.
  Source (8,1): 61 members (72 of 133 left out per the B logs; 7 more saturated), 2759 subsets: **no separation** (largest drop
  0).  2026-11-11 11:39 UTC, 9.8 h (rebuilt after the container restart of 01:46).  Source (7,2): 97 members (163 of 260 left out per the B logs; 7 more saturated, 90 tested), the sum of all
  members at levels 1 and g, the 90 all-but-one sums, all named groups, 4000 pairs, 1000 triples and 100 random subsets, 5481
  subsets: **no separation** (largest drop 0).  2026-11-19 04:38 UTC (members built 2026-11-17 23:57 .. 2026-11-18 09:00 with
  per-member checkpoints, subset tests 09:03 .. 04:38 with saved subset dims, across the restarts of 00:50, 05:03 and 01:15).
  So family A of the C^5 source finds no separation for 5x5x5 on any of the sources (8,1), (7,2), (7,1,1).

## Running / queued (no separation so far)

* Running (2026-11-22 14:28 UTC): d9_455_dir0_B_p5_mid7 (dir 0, sources lam_1 >= 4, size 11000..15000; 6 of 42 done,
  resumed after d9_455_dir0_B_p3_big; its target-7 checkpoints were lost in the fresh container), d9_555_B_p5_mid3 (5x5x5,
  sources lam_1 >= 4, size 4000..5000), the small d9_455_dir1_B_p5_all (4x5x5 dir 1, sources lam_1 >= 4, size <= 2000,
  every subset of the members; 59 of 61 on 2026-11-23).  (4 CPUs; memory is the limit.)
* Paused (2026-11-23 09:57, memory): d9_455_dir0_B_p5_mid_all (dir 0, sources lam_1 >= 4, size 2000..3000, every subset of the
  members; 7 of 44 done, all without separation, among them 32211|32211 with 14 members and 32794 subsets).
* Queued: d9_455_dir1_B_p5_mid3 (sources lam_1 >= 4, size 4000..5000), then d9_555_B_big and d9_455_dir1_B_big, each alone
  (sources lam_1 >= 7, size 6000..25000, ~12 GB each).
* Dropped: d9_455_dir0_B_p4_mid (dir 0, sources lam_1 >= 5, size 3000..6000, subsets of at most 3 members): subsumed by the
  finished lam_1 >= 4 bands d9_455_dir0_B_p5_mid2..mid5 (same test on a superset of members; see README, 2026-11-20).
