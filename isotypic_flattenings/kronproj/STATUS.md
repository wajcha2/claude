# kronproj status (random projections of the Kronecker spaces)
Session https://claude.ai/code/session_016hXfA1TEXGV2WrtJUbf7Kp, branch `claude/zealous-mendel-i9qpdu`.  Started 2026-10-22 15:08 UTC.
Jobs: `jobs.txt` (runner `kp_jobs.py jobs.txt 4`, logs `logs/jobs/`).  Hits: `grep SEPARATES logs/jobs/*.log`.

## Results so far
* 4x5x5 d=5 dir 0 (smoke run, `logs/smoke_455_d5_dir0.log`, A, B, E; d=5 has g <= 2, so only mixed levels): no separation.
* 4x5x5 d=6 dir 0, single components with g >= 3 (13), H_s and V_s for all s (`logs/smoke_single_455_d6_dir0.log`): all
  full rank (sources S^λC^4 have dim <= 126, H_s = n1 and V_s = s n1 on rank 8 already): no separation.

## Running
(see `logs/jobs/runner.status`)
