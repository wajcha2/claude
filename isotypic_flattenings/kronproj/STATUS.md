# kronproj status (random projections of the Kronecker spaces)
Session https://claude.ai/code/session_016hXfA1TEXGV2WrtJUbf7Kp, branch `claude/zealous-mendel-i9qpdu`.  Started 2026-10-22 15:08 UTC.
Jobs: `jobs.txt` (runner `kp_jobs.py jobs.txt 4`, logs `logs/jobs/`).  Hits: `grep SEPARATES logs/jobs/*.log`.

## Results so far (2026-10-22 16:15 UTC): NO separation anywhere
| job | what | result |
|---|---|---|
| k455_d5_dir0 | 4x5x5 d=5, source C^4: kpA, kpB (all level vectors, g <= 2), 300 kpG | none (320 s) |
| k455_d5_dir1 | 4x5x5 d=5, source C^5: same | none (1695 s) |
| k555_d5 | 5x5x5 d=5: same | none (1963 s) |
| k455_d6_dir0 | 4x5x5 d=6, source C^4: kpA 8 lattices (all saturated: every level vector gives n1), kpB 27 of 33 lattices exhaustive | none so far (running) |
| k455_d6_dir1, k555_d6 | d=6, source C^5: kpA running (lattices done so far all saturated) | none so far (running) |
| s455_d7_dir1 | H_s / V_s, 4x5x5 d=7, source C^5, g >= 3 | 16 components, none so far (running) |
* Smoke runs: 4x5x5 d=5 dir 0 (`logs/smoke_455_d5_dir0.log`) and the 13 components with g >= 3 at 4x5x5 d=6 dir 0, H_s and V_s
  for all s (`logs/smoke_single_455_d6_dir0.log`): all full rank, no separation.
* Validation (`test_kp.py quick`): 143 checks ok, 0 failures so far (still running).

## Running
Snapshot of the job logs: `logs/jobs_snapshot/` (live logs in the untracked `logs/jobs/`).
