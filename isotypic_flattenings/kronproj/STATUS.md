# kronproj status (random projections of the Kronecker spaces)
Session https://claude.ai/code/session_016hXfA1TEXGV2WrtJUbf7Kp, branch `claude/zealous-mendel-i9qpdu`.  Started 2026-10-22 15:08 UTC.
Jobs: `jobs.txt` (runner `kp_jobs.py jobs.txt 4`, logs `logs/jobs/`).  Hits: `grep SEPARATES logs/jobs/*.log`.

## Results so far (2026-10-22 18:16 UTC): NO separation anywhere
| job | what | result |
|---|---|---|
| k455_d5_dir0 | 4x5x5 d=5, source C^4: kpA, kpB (all level vectors, g <= 2), 300 kpG | none (320 s) |
| k455_d5_dir1 | 4x5x5 d=5, source C^5: same | none (1695 s) |
| k555_d5 | 5x5x5 d=5: same | none (1963 s) |
| k455_d6_dir0 | 4x5x5 d=6, source C^4: kpA 8 lattices (all saturated: every level vector gives n1), kpB 32 lattices with all level vectors, kpE 13 components (rank-s grids, all full: k n1) | none (11053 s) |
| k455_d6_dir1 | d=6, source C^5: kpA 8 of 10 sources (all saturated) | none so far (running) |
| k555_d6 | d=6: kpA 6 of 10 sources (all saturated) | none so far (running) |
| s455_d7_dir1 (w0, w1) | H_s / V_s for all s, 4x5x5 d=7, source C^5, g >= 3 | 77 components, none (running) |
* Smoke runs: 4x5x5 d=5 dir 0 (`logs/smoke_455_d5_dir0.log`) and the 13 components with g >= 3 at 4x5x5 d=6 dir 0, H_s and V_s
  for all s (`logs/smoke_single_455_d6_dir0.log`): all full rank, no separation.
* Validation: `test_kp.py full` 382 ok / 0 failures (`logs/test_full.log`), including C^4 d=8 ((6,2),(3,2,2,1),(3,2,2,1)):
  H_1 225/225, H_2 = H_3 = H_4 = 304/309 (the known values); `test_kp.py quick` 143 ok / 0 failures (`logs/test_quick.log`).

## Running
Snapshot of the job logs: `logs/jobs_snapshot/` (live logs in the untracked `logs/jobs/`).
