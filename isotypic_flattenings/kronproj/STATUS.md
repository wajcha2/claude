# kronproj status (random projections of the Kronecker spaces)
Session https://claude.ai/code/session_016hXfA1TEXGV2WrtJUbf7Kp, branch `claude/zealous-mendel-i9qpdu`.  Started 2026-10-22 15:08 UTC.
Jobs: `jobs.txt` (runner `kp_jobs.py jobs.txt 4`, logs `logs/jobs/`).  Hits: `grep SEPARATES logs/jobs/*.log`.

## Results so far (2026-11-09 08:35 UTC): NO separation anywhere
**Degree 7 grids complete** (kpE incl. the compressed ones) for both formats; no separation.

**Degree 6 complete** for 4x5x5 (both sources) and 5x5x5: every family (single components H_s / V_s, kpA, kpB incl. the
large targets, kpE, kpG), no separation.

| job | what | result |
|---|---|---|
| k455_d5_dir0 | 4x5x5 d=5, source C^4: kpA, kpB (all level vectors, g <= 2), 300 kpG | none (320 s) |
| k455_d5_dir1 | 4x5x5 d=5, source C^5: same | none (1695 s) |
| k555_d5 | 5x5x5 d=5: same | none (1963 s) |
| k455_d6_dir0 | 4x5x5 d=6, source C^4: kpA 8 lattices (all saturated: every level vector gives n1), kpB 32 lattices with all level vectors, kpE 13 components (rank-s grids, all full: k n1) | none (11053 s) |
| k455_d6_dir1 | 4x5x5 d=6, source C^5: kpA all 10 sources (all saturated), kpB 24 lattices with all level vectors (largest 3111|321: 6479 level vectors), kpE 13 components (all full) | none (21026 s after the restart); 6 kpB lattices above the cap -> k455_d6_dir1_big, s455_d6_dir1 |
| k555_d6 | d=6: kpA all 10 sources (all saturated), kpB 22 lattices with all level vectors; 1 left (3111|3111), then kpE | none so far (running) |
| s455_d7_dir1 (w0, w1) | H_s / V_s for all s, 4x5x5 d=7, source C^5, g >= 3 | **complete**: all 176 components, 1352 H_s / V_s values, none; 38 values below the size bound, all with equal ranks on rank 8 and 9 (4729 s + 5450 s) |
| s555_d7 (w0, w1) | H_s / V_s for all s, 5x5x5 d=7, g >= 3 (188 components) | **complete**: 188 components, 1432 values, none; 7 values below the size bound, all equal on rank 9 and 10 (10852 s + 11735 s) |
| s455_d7_dir0 | H_s / V_s for all s, 4x5x5 d=7, source C^4, g >= 3 | **complete**: 176 components, 1352 values, none; all but 1 value at the size bound (1093 s) |
| k455_d6_dir0_G | 500 random general block matrices (2-3 sources x 2-3 targets, random ranks s_ij), 4x5x5 d=6 source C^4 | **complete**, none (142 s) |
| k555_d6_G | 500 random general block matrices, 5x5x5 d=6 | **complete**, none (2011 s) |
| k455_d6_dir1_G | 500 random general block matrices, 4x5x5 d=6 source C^5 | **complete**, none (1956 s) |
| k455_d7_dir0 | 4x5x5 d=7 source C^4: kpA, kpB (size <= 3000), kpE | **complete (with k455_d7_dir0_big: 4x5x5 d=7 source C^4 fully done)**, none (kpA 10 lattices, kpB 102 + 93 mirrors, 3 above the cap -> k455_d7_dir0_big; kpE 99 components, all 496 grid values at the size bound) |
| k555_d7 | 5x5x5 d=7: kpB (size <= 2500), kpE | **complete**, none (12999 s): kpB 27 lattices + 133 mirrors, 47 above the cap -> k555_d7_big; kpE 107 components + 81 mirrors, all 356 computed grid values at the size bound, 164 grid values (12 components) above --emax -> k555_d7_E2 (compressed grids) |
| k455_d7_dir1 | 4x5x5 d=7 source C^5: kpB (size <= 2500), kpE | **complete**, none (16953 s): kpB 32 lattices, 67 above the cap -> k455_d7_dir1_big; kpE 176 components, 672 grid values (663 at the size bound, 9 below it but equal on rank 8 and 9, e.g. ((3,3,1),(3,2,1,1),(3,1,1,1,1)) 2x3/s2: 480/480 vs bound 630), 160 above --emax -> k455_d7_dir1_E2 |
| s555_d6 | H_s / V_s for all s, 5x5x5 d=6, the 13 components with g >= 3 | **complete**, none: every value at the size bound (e.g. 321|321|321 g=5: V_s = 280 s) (377 s) |
| s455_d6_dir1 | same, 4x5x5 d=6 source C^5 | **complete**, none: every value at the size bound (329 s) |
| k555_d6_big | the 5x5x5 d=6 kpB lattices with size 3128-3408 (one per mirror pair) | **complete**, none: 42|321 by the exhaustive walk (5183 level vectors, 11874 s), 321|2211, 411|321, 321|3111 by the direct-sum certificate (196-378 s each); only 321|321 (size 5713) left at 5x5x5 d=6 |
| k455_d6_dir1_big | the 4x5x5 d=6 dir 1 kpB lattices with size 3128-3408 | **complete**, none: 4 by the certificate (34-47 s each), 321|3111 (not direct, 2650 < 3400) by the exhaustive walk (6479 level vectors, 6555 s) |
| k555_d6_321, k455_d6_dir1_321 | the deferred 321|321 lattices (size 5713, 10 members, g = 1234254232) | **complete**, none: both direct sums (5705/5705), certified (269 s / 154 s, peak ~1.6 GB) |
| s455_d8_dir1_H_w0/w1 | H_s for all s, 4x5x5 d=8 source C^5, the 977 components with g >= 3 | **complete**, none: 4874 H_s values, 60 below the size bound but equal on rank 8 and 9 (e.g. 611|3221|32111 g=3: H_1 = H_2 = H_3 = 300/300 vs bound 600-945) |
| s555_d8_H_w0/w1, s455_d8_dir0_H | H_s for all s, 5x5x5 d=8 (645 components after mirrors) and 4x5x5 d=8 source C^4 (g >= 3, --nomirror) | 5x5x5 **complete**, none: 645 components, 3218 H_s values, 51 below the size bound but all equal on rank 9 and 10 (e.g. 521|32111|22211 g=5: H_3 = 980/980, H_4 = 1160/1160 vs bound 1200-1440) (15032 s + 16226 s); 4x5x5 source C^4 **complete**, none: 527 components, 2677 H_s values, 8 below the size bound but equal on rank 8 and 9 (e.g. 611|32111|32111 g=4: H_s = 183/183 vs bound 189) (2806 s).  **All d=8 single-component H_s done (three directions), no separation.** |
| s455_d8_dir0_V, s555_d8_V, s455_d8_dir1_V | V_s for all s at d=8 (incremental exact row basis; 5x5x5 and source C^5 cut at --maxcost 4e7: 580 of 645 / 891 of 977 components) | running (started 10:45 UTC), none so far: 4x5x5 source C^4 **complete**, none: 527 components, 2677 V_s values, 69 (in 39 components) below the size bound but all equal on rank 8 and 9 (e.g. 5111|4211|22211 V_3 = 95/95 vs 105) (9402 s); 4x5x5 source C^5 **complete** (all 891 components under --maxcost 4e7; 86 larger ones not run), none: 4204 V_s values, 254 (in 133 components) below the size bound but all equal on rank 8 and 9 (e.g. 41111|4211|22211 V_3 = 95/95 vs 105) (40823 s of the last run), 5x5x5 **complete** (all 580 components under --maxcost 4e7; 65 larger ones not run), none: 2713 V_s values, 117 (in 53 components) below the size bound but all equal on rank 9 and 10 (e.g. 5111|4211|22211 V_3 = 755/755 vs 945) (35132 s of the last run); the new V_s is identical to the old one on all 13 components of 5x5x5 d=6 and all 176 of 4x5x5 d=7 source C^4 (`logs/test_vinc_*.log` vs the s555_d6 / s455_d7_dir0 logs), 4x5x5 d=7 source C^5: all 176 components identical (`logs/test_vinc_455_d7_dir1.log`; the last, 421|3211|421 g=8, V_8 = 5350/5350, in 209 s single-threaded) |
| s555_d8_V_b, s455_d8_dir1_V_b | the next cost band of the d=8 V_s: 4e7 < g N1 K <= 1e8 (`--mincost`), 46 / 63 components with g = 5..17 | running (from 2026-11-01 22:35 UTC), none so far: 5x5x5 **complete**, none: 46 components, 325 V_s values, 21 (in 10 components) below the size bound but all equal on rank 9 and 10 (e.g. 431|422|32111 g=6: V_6 = 6000/6000 vs 6300) (46025 s) -- with s555_d8_V: V_s done for 626 of the 645 components at 5x5x5 d=8; the last 19 (g N1 K up to 3.5e8, ~10 GB peak) are left out for memory while the big-lattice jobs run; 4x5x5 source C^5 (from 00:03) 58 of 63 (409 values, 42 below the bound but equal on rank 8 and 9); PAUSED at 15:25 (line commented out in jobs.txt, process stopped; resumes from its log) because k555_d7_big jumped to 7.9 GB on its next lattice and the total reached 12.6 of 16 GB |
| k555_d7_big, k455_d7_dir1_big | the d=7 kpB lattices above the first runs' caps (size 2500-12000; 5x5x5 one of each mirror pair) | 5x5x5: 39 lattices done (30 by the direct-sum certificate; the latest five, 322|322 .. 421|4111 of size 7598-11008, certified in 790-1522 s, peak ~8 GB at size 11008, the others by the walk / samples; 421|31111 size 6458, not direct (4950 < 6450), 1171 level vectors, maxdrop 0, 32934 s; 3211|2221 size 7008, full sum 7000/7000 but singles not all equal-saturated, 1142 level vectors, maxdrop 0, 51827 s; 4111|4111 size 7473, not direct (5890 < 7470), 1085 level vectors, maxdrop 0, 38313 s; 331|331 size 7598 certified, 871 s), none (running); 4x5x5 source C^5: 40 lattices done (3211|322 size 4208: not direct, 1474 level vectors, maxdrop 0, 34123 s; then 8 of size 4448-4808 certified, 169-277 s each; 511|4111 size 5168 not direct (4110 < 5160), 918 level vectors, maxdrop 0, 12552 s; 43|331 certified, 360 s; 4111|511 size 5168 not direct, 917 level vectors, maxdrop 0, 10664 s; 5 more of size 5168-5408 certified, 151-255 s each; 421|2221 size 5608 not direct (4700 < 5600), 1122 level vectors, maxdrop 0, 22832 s -- the lattice cut off by the two outages, done on the third try; 322|4111 size 5768 not direct (4000 < 5760), 1030 level vectors, maxdrop 0, 16717 s; 511|511, 52|52 certified, 149-166 s; 4111|331 size 6008 not direct (3600 < 6000), 1031 level vectors, maxdrop 0, 16127 s): 2221|421, 4111|4111, 3211|4111 (~2.6 h each), 4111|3211 (25592 s, all 2650 < 3500), 3211|3211 (45129 s, 2553 level vectors) -- not direct sums, maxdrop 0 -- and 12 of size 3758-4208 by the direct-sum certificate (80-165 s each); 18th: 4111|322 size 4208, not direct (3000 < 4200), 1031 level vectors, maxdrop 0, 14075 s, none (running, multi-day) |
* Smoke runs: 4x5x5 d=5 dir 0 (`logs/smoke_455_d5_dir0.log`) and the 13 components with g >= 3 at 4x5x5 d=6 dir 0, H_s and V_s
  for all s (`logs/smoke_single_455_d6_dir0.log`): all full rank, no separation.
* Validation: `test_kp.py full` 382 ok / 0 failures (`logs/test_full.log`), including C^4 d=8 ((6,2),(3,2,2,1),(3,2,2,1)):
  H_1 225/225, H_2 = H_3 = H_4 = 304/309 (the known values); `test_kp.py quick` 143 ok / 0 failures (`logs/test_quick.log`).

* Container down 2026-11-03 07:49 UTC (last mem.log line) to 2026-11-08 13:50 UTC (5 days); runner, memory log and watch
  relaunched at 13:51.  The big-lattice jobs restart their current lattices again (k555_d7_big: 4111|3211, size ~11000, needs
  ~10+ h without interruption; it has now been cut off twice).

* Container restart 2026-11-03 ~01:09 UTC (last mem.log line 01:08:41); runner, memory log and watch relaunched at 01:10.  The
  big-lattice jobs restart their current lattices (k555_d7_big had been on 4111|3211, size ~11000, since ~15:50).

* Container down 2026-10-26 06:49 UTC (last mem.log line) to 2026-11-01 12:42 UTC (6 days); runner, memory log and watch
  relaunched at 12:43, jobs resume from their logs (the big-lattice jobs restart their current lattice).

* 2026-10-25 10:35-19:15 UTC: the V_s validation runs were started by hand without OPENBLAS_NUM_THREADS=1 (the runner sets
  it), so they ran 4 BLAS threads at 1.6 cores despite nice and the 4 jobs got ~58% of a core each.  Stopped; the last
  validation component now goes through the runner (single-threaded).

* Container restart 2026-10-25: the jobs stopped at 11:42 UTC (last mem.log line), the container came back at 17:08;
  runner, memory log and watch relaunched at 17:09 (jobs resume from their logs).

* Incident 2026-10-22 19:52-20:21 UTC: `kp_single.py` lacked `FOUND = []` (lost in the resume edit); worker 0 of s455_d7_dir1
  finished its 88 components and crashed on the final summary line, so the runner relaunched it every 30 s (57 empty part
  logs, removed).  No result lost (a hit line would have been printed before the crash).  Fixed; the watch now flags
  relaunch loops.

* 2026-10-22 20:57 UTC: `hwv_fast.minors_of_points` replaced by the faster version of the degree-9 agent (same output on 108
  test cases, kp_single smoke run reproduces every rank, single components 10-40x faster); kp_single workers restarted.

* 2026-10-23 03:40 UTC: container restart (not memory: 10.5 GB steady before it); disk, logs and caches survived, runner
  relaunched with --resume (only the lattices in progress were redone, e.g. 4x5x5 d=6 dir 1 3111|321).

* Gap filling (queued 2026-10-23 05:00): the d=6 components with g >= 3 all sit in kpB lattices above the size cap, so
  their V_s were not tested (H_s were, as kpA singles).  Jobs s555_d6 / s455_d6_dir1 (H_s, V_s of every g >= 3 component)
  and k555_d6_big / k455_d6_dir1_big (those lattices with the cap at 3500; 5x5x5 one of each mirror pair).  321|321 (size
  5713, ~8 GB of lattice matrices) is deferred.  The runner now re-reads `jobs.txt` and adopts running workers.

* 2026-10-23 10:50 UTC: `--nomirror` (kp_search, kp_single): when the two target factors have equal dimension (5x5x5, 4x5x5
  with source C^4) only one of each mirror pair mu|nu ~ nu|mu (kpB) and (lam, mu, nu) ~ (lam, nu, mu) (kpE, kp_single) is
  computed: swapping the target factors maps generic rank-r tensors to generic rank-r tensors.  Checked: every mirror pair
  computed both ways so far gave identical members, g and ranks; a --nomirror rerun of 4x5x5 d=5 dir 0 reproduces the
  processed lattices line for line.  k455_d7_dir0 and k555_d7 restarted with it (resume), the d=8 kp_single jobs of 5x5x5
  and 4x5x5 dir 0 queued with it.

* 2026-10-23 14:05 UTC: **direct-sum certificate** in kp_search (lattices A, B): if on r_lo the full sum (all members,
  full levels) is direct (dim = sum of the single dims) and every single (member, level) has equal dims on r_lo and r_hi,
  then every configuration S has dim_lo(S) = sum of its single dims = sum of the r_hi single dims >= dim_hi(S), so no
  level vector separates and the walk is skipped.  Exact, not a heuristic.  From the logs: 74 of 88 kpB lattices of
  k455_d7_dir0 (97% of its time), 18 of 24 of k555_d6, 14 of 26 of k555_d7 are certifiable.  Checked: 4x5x5 d=6 dir 0
  42|321 certified in 11 s (exhaustive walk 262 s, same verdict); non-direct lattices still get the walk (3111|3111:
  same line as before).  Also a saturation cut in the walk (skip supersets once the sum reaches the lattice cap on
  r_lo).  k455_d7_dir0, k555_d7, k555_d6_big restarted with it (resume); k455_d7_dir1 left running (13%).

* 2026-10-23 14:25 UTC: **switched to the fast low-memory combflat.py** of `claude/project-thread-ttahoa-kronproj`
  (see `SWITCH.md`; merged with --nomirror / saturation cut / certificate) and the faster `isoflat.modrank` (panel 64) of
  `claude/project-thread-ttahoa-sweepfast`.  Checked here: test_comb quick 0 failures; test_kp quick 200 ok / 0 failures
  in 455 s (`logs/test_quick_newcode.log`; old code >50 min); 4x5x5 d=6 dir 0 lattices 3111|3111 / 42|321, the d=5
  --nomirror run and kp_single 4x5x5 d=6 dir 0 reproduce the earlier singles, full sums and H_s / V_s values (kp_single
  15 s vs 239 s originally).  All four workers restarted on it (resume).

* 2026-10-23 18:05 UTC: kpE grids larger than --emax entries are now ranked after a random right compression of each
  column block (c = min(K, k N1) + 8 columns per block; the grid's row space has dim <= k N1, so a generic compression of
  each column block is injective on its projection and the rank is preserved w.h.p.).  Checked: forcing it on all 13
  components of 4x5x5 d=6 dir 0 reproduces every grid value (`logs/test_ecompress_455_d6_dir0.log`).

* 2026-10-24 00:56 UTC -> 2026-10-25 05:32 UTC: the container was down (~28.5 h); disk, logs and scratchpad survived.
  Runner relaunched with --resume (only the lattices / components in progress are redone).

## Running
Snapshot of the job logs: `logs/jobs_snapshot/` (live logs in the untracked `logs/jobs/`).
