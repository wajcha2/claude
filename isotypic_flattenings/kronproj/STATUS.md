# kronproj status (random projections of the Kronecker spaces)
Session https://claude.ai/code/session_016hXfA1TEXGV2WrtJUbf7Kp, branch `claude/zealous-mendel-i9qpdu`.  Started 2026-10-22 15:08 UTC.
Jobs: `jobs.txt` (runner `kp_jobs.py jobs.txt 4`, logs `logs/jobs/`).  Hits: `grep SEPARATES logs/jobs/*.log`.

## Results so far (2026-10-23 11:55 UTC): NO separation anywhere
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
| k455_d7_dir0 | 4x5x5 d=7 source C^4: kpA, kpB (exhaustive up to 8000 level vectors, size <= 3000), kpE (families always run in the order A, B, E) | kpA done, kpB 96 lattices (e.g. 421|22111: g=11322242, 6495 level vectors), none (running) |
| k555_d7 | 5x5x5 d=7: kpB (size <= 2500), kpE | 24 lattices (e.g. 3211|22111: 11 members, g up to 4, sampled level vectors), 5 mirrors skipped, none (running) |
| k455_d7_dir1 | 4x5x5 d=7 source C^5: kpB (size <= 2500), kpE | 19 lattices, none (running) |
| s555_d6 | H_s / V_s for all s, 5x5x5 d=6, the 13 components with g >= 3 | **complete**, none: every value at the size bound (e.g. 321|321|321 g=5: V_s = 280 s) (377 s) |
| s455_d6_dir1 | same, 4x5x5 d=6 source C^5 | **complete**, none: every value at the size bound (329 s) |
| k555_d6_big | the 5x5x5 d=6 kpB lattices with size 3128-3408 (one per mirror pair) | running |
* Smoke runs: 4x5x5 d=5 dir 0 (`logs/smoke_455_d5_dir0.log`) and the 13 components with g >= 3 at 4x5x5 d=6 dir 0, H_s and V_s
  for all s (`logs/smoke_single_455_d6_dir0.log`): all full rank, no separation.
* Validation: `test_kp.py full` 382 ok / 0 failures (`logs/test_full.log`), including C^4 d=8 ((6,2),(3,2,2,1),(3,2,2,1)):
  H_1 225/225, H_2 = H_3 = H_4 = 304/309 (the known values); `test_kp.py quick` 143 ok / 0 failures (`logs/test_quick.log`).

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

## Running
Snapshot of the job logs: `logs/jobs_snapshot/` (live logs in the untracked `logs/jobs/`).
