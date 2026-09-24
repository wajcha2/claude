# Task for a separate agent: isotypic flattenings at d = 10 on (C^4)^{(x)3}  (long-running: 1-2 weeks)

## Goal
Decide whether some isotypic flattening in degree d = 10 separates a general tensor of rank 6 from a general
tensor (rank 7) in C^4 (x) C^4 (x) C^4: strictly smaller flattening rank on random rank-6 tensors than on random
rank-7 tensors. Report every component checked, negative ones included.

## Code
Repository github.com/wajcha2/claude, branch `claude/wonderful-fermat-1v76ux`, directory `isotypic_flattenings/`.
Read `RESULTS.md`, `PROGRESS.md`, `PROMPT_d9.md` and the docstrings first. `pip install numpy sympy`.
Exact arithmetic modulo p = 524287 (`hwv.py`).
* `sweep_hwv.py n d r_low,r_high seed slice nslices [noV]` is the main tool (all unordered components with nonzero
  Kronecker coefficient, 3 flattening directions, generic functional, stacked U for g >= 2; `noV` skips the
  U^* (x) S^{l1}V^* stack). Env `CHUNK` bounds memory, env `RESUME=log1:log2` skips components already logged.
  Hits are lines `*** SEPARATES`; the last line prints `FOUND: [...]`.
* Secondary tools (only after the sweep, or on hits): `specialU.py`, `pencil.py`, `plane.py`, `koszul.py`, `schur2.py`.

## Size at d = 10
1578 components, Weyl-module dimensions up to 770, Kronecker coefficients up to ~60. A complete sweep is weeks of
compute on a 4-core machine. Therefore:
1. Sanity check first (1 minute): `python3 sweep_hwv.py 4 4 6,7` -> full ranks, `FOUND: []`;
   `python3 test_hwv.py 3 5 4,5 "((3,2),(3,1,1),(2,2,1))"` -> 12 vs 15.
2. Order components by cost (largest Weyl dimension, then Kronecker coefficient) and process cheapest first.
   Add a maximum-dimension filter to the sweep (state the bound in each log name), pass 1 with bound 150,
   pass 2 with 300, pass 3 unbounded. Always run `noV` and `CHUNK=32`; use one process per core minus one.
3. Never run more processes than cores; the container has a hidden memory cgroup limit and kills processes
   silently (`dmesg | grep -i oom`). Restart killed slices with `RESUME` pointing to all existing logs.

## Long-running discipline (this is expected to take 1-2 weeks)
* Start every computation with `nohup ... &` (or setsid) so it survives the end of a turn; never block a turn on it.
* Do NOT poll with foreground sleeps. Schedule check-ins instead (a scheduled wake-up / routine / cron every
  2-4 hours). On each check-in: verify the processes are alive, count finished components, grep for
  `SEPARATES`, `ERROR`, `Killed`, commit and push the logs and an updated `PROGRESS.md`, restart anything dead
  with `RESUME`, then go idle again. Keep this going until all passes are complete or the user stops you.
* Push the logs at least every hour of compute. If the container is reclaimed, a fresh session must be able to
  continue from the pushed logs alone (clone branch, `RESUME=<all logs>`), so write the exact restart command
  into `PROGRESS.md`.
* Report to the user briefly at each check-in only when something changed (new pass finished, a hit, a crash);
  otherwise just re-arm the next check-in silently.

## On a hit
If a `SEPARATES` line appears: re-run that component alone with a different seed and, if possible, a second prime
(change `p` in `hwv.py` to another prime below 2^20, e.g. 1048573 is NOT prime; use 786433), and report the
component, dimensions, Kronecker coefficient, direction, and both ranks. Then (optional) run `koszul.py` and
`schur2.py` on it and `specialU.py` / `plane.py` for special U.

## Final report
(a) table of components checked (component, dims, g, ranks low/high) per pass, (b) hits with verification,
(c) components not checked, with the bound that excluded them, (d) total compute time. A negative result is a
result: "no isotypic flattening in degree 10 among the checked components separates rank 6 from rank 7".
