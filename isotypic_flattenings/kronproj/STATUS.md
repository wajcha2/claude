# kronproj status (random projections of the Kronecker spaces)
Session https://claude.ai/code/session_016hXfA1TEXGV2WrtJUbf7Kp, branch `claude/zealous-mendel-i9qpdu`.  Started 2026-10-22 15:08 UTC.
Jobs: `jobs.txt` (runner `kp_jobs.py jobs.txt 4`, logs `logs/jobs/`).  Hits: `grep SEPARATES logs/jobs/*.log`.

## Results so far (2026-10-22 21:24 UTC): NO separation anywhere
| job | what | result |
|---|---|---|
| k455_d5_dir0 | 4x5x5 d=5, source C^4: kpA, kpB (all level vectors, g <= 2), 300 kpG | none (320 s) |
| k455_d5_dir1 | 4x5x5 d=5, source C^5: same | none (1695 s) |
| k555_d5 | 5x5x5 d=5: same | none (1963 s) |
| k455_d6_dir0 | 4x5x5 d=6, source C^4: kpA 8 lattices (all saturated: every level vector gives n1), kpB 32 lattices with all level vectors, kpE 13 components (rank-s grids, all full: k n1) | none (11053 s) |
| k455_d6_dir1 | d=6, source C^5: kpA all 10 sources (all saturated), kpB 14 lattices with all level vectors | none so far (running) |
| k555_d6 | d=6: kpA all 10 sources (all saturated), kpB 12 lattices with all level vectors | none so far (running) |
| s455_d7_dir1 (w0, w1) | H_s / V_s for all s, 4x5x5 d=7, source C^5, g >= 3 | 173 of 176 components (worker 0 complete), none (running); 21 of the first 960 H_s / V_s values are below the size bound, all with equal ranks on rank 8 and 9 |
| s555_d7 (w0) | H_s / V_s for all s, 5x5x5 d=7, g >= 3 | 62 of ~94 (worker 0 half), none (running) |
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

## Running
Snapshot of the job logs: `logs/jobs_snapshot/` (live logs in the untracked `logs/jobs/`).
