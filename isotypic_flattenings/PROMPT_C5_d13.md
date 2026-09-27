# Task for a separate agent: isotypic flattenings on (C^5)^{(x)3}, rank 9 vs rank 10, degrees d = 13 and 14

## Goal
Find an isotypic flattening in degree d = 13 (then 14) that separates a general tensor of rank 9 from a general
tensor (rank 10) in C^5 (x) C^5 (x) C^5: strictly smaller rank on random rank-9 tensors than on random rank-10
tensors. Report every component checked. A negative result is a result.

## Code and context
Repository github.com/wajcha2/claude, branch `claude/wonderful-fermat-1v76ux`, directory `isotypic_flattenings/`.
Read `PROGRESS.md`, `agents/README.md`, `agents/d7d8.md`, `agents/d9.md`, `PROMPT_d10.md` and the docstrings of
`sweep_fast.py` / `hwv_fast.py`.  `pip install numpy sympy opt_einsum`.  Exact arithmetic mod p = 524287.
Known results: C^4, rank 6 vs 7: first separators at d = 8 (stacked U) and d = 9 (g = 1 components); C^5 rank 9 vs 10:
nothing up to d = 12 so far on the "promising" lists (see PROGRESS.md; the d7d8 agent keeps running d = 10..12).

## Which components
Generate the list as the d7d8 agent did (see how `prom5_d12.txt` was made, in the conversation summary in
PROGRESS.md and this file): components lam = (l1, l2, l3) of partitions of d with at most 5 rows, Kronecker
coefficient g > 0, l1 with at most 2 rows, l2 and l3 with at least 4 rows, and dim S^{l1} >= (dim S^{l2} dim S^{l3})/2.
Write them to `prom5_d13.txt` (one `repr(lam)` per line), same for d = 14.  Process cheapest first (the sweep does this
with `ORDER=cost`, default).  Prefer components whose two target modules are small (dim <= 200): those are affordable
and are where a rank drop would be visible.

## How to run (one process per core, never more)
    export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
    mkdir -p live claims5_p13; MEMCAP=8388608 ONLY=prom5_d13.txt CLAIMDIR=claims5_p13 \
      nohup python3 -u sweep_fast.py 5 13 9,10 5 <k> <N> noV > live/d13_w<k>.log 2>&1 &
`ROWCAP` (default on) samples only min(n1, g*n23)+8 rows and min(n1, n23)+8 columns; `MEMCAP` bounds intermediates
(the evaluator splits batches, verified); `RESUME=<log>` skips components already logged; workers share `CLAIMDIR`.
Sanity first: `python3 sweep_fast.py 4 4 6,7` must give full ranks / `FOUND: []`, and
`ONLY=<file with ((6, 2), (3, 2, 2, 1), (3, 2, 2, 1))> python3 sweep_fast.py 4 8 6,7 5 0 1 noV` must print H1:304/309.
Components at d = 13 with source dimension in the thousands take hours each; expect days.  Keep `live/` logs
untracked (it is in .gitignore) and snapshot them into tracked files (`hwv5_d13_prom_done.log`) at every check-in:
`grep '^lam' live/d13_w*.log >> hwv5_d13_prom_done.log; sort -u ...`.  Never let git replace a file a worker writes to.

## Long-running discipline
Start everything with nohup, never block a turn; schedule check-ins every 2-4 hours (a routine / scheduled wake-up);
at each check-in verify the workers are alive (`pgrep -fa sweep_fast`), check `dmesg | grep -i oom`, snapshot logs,
commit and push (`git pull --rebase --autostash` first), restart dead workers with RESUME, update `agents/d13.md`
(status, counts, restart command).  Report to the user only when something changed.  Continue with d = 14 when
d = 13 is exhausted or if its remaining components exceed ~6 h each (then interleave).

## On a hit
Re-run the component alone with another seed and with the prime 524269 (`verify_hit.py "lam" <dir> 8,9,10,11 2 524269`
if it supports n=5, else adapt), and report component, dims, g, direction, ranks.  Write it to `agents/d13.md`
and `agents/to-d7d8.md`.
