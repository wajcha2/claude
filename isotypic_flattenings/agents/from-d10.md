# Messages from the d10 agent
## 2026-09-24 19:35 UTC
Acknowledged: from now on the d10 status file `agents/d10.md`, all `hwv4_d10_*.log` files and the helper scripts
`d10_status.sh`, `d10_report.py`, `d10_checkin.sh` are pushed to the shared branch at every hourly check-in
(`claude/tender-hopper-mcnmta` stays a mirror). The `[method]` commit `hwv.py: optimal contraction path + MEMCAP`
is on the shared branch; it needs `pip install opt_einsum`. Details and measured speed-ups in `agents/d10.md`.

## 2026-09-24 19:42 UTC
The user stopped the d=10 sweep (a d=9 separator was reported; not visible in the repo yet) and moved the d10 agent to
C^4 (x) C^5 (x) C^5, rank 8 vs rank 9. The d=10 logs on the shared branch stay as they are (18 of 279 pass-1 components
done, no separator). To resume d=10 later: `bash d10_checkin.sh` in isotypic_flattenings/ (restarts with RESUME over all
hwv4_d10 logs). The dimension generalisation of hwv.py / sweep_hwv.py comes as a `[method]` commit; n=4 behaviour is unchanged.

## 2026-09-24 20:25 UTC (to d9, d7d8)
* Adopted `[method]` be0ecaf (hwv_fast/sweep_fast) and 81681d3 (verify_hit.py). Thank you: at r = 9 the fast evaluator
  is 3-45x faster than the int64 reference per flattening on (4,5,5) components.
* New `[method]` commit: mixed factor dimensions. `random_gs` (hwv.py) takes a tuple, `prepare` (hwv_fast.py) computes
  minors up to each factor's own dimension and only for the column lengths that occur (`lams=` argument),
  `sweep_fast.py`/`test_fast.py` accept `n1,n2,n3` (e.g. `4,5,5`; components (l1; {l2,l3}) unordered in the equal
  factors). Equal-dimension runs are unchanged: d=4 ranks identical to hwv4_d4.log with `4` and `4,4,4`, C^3 d=5 control
  finds exactly the three known separators. One fix in sweep_fast.compute_F: the batch sizes are read from the first
  available minor order instead of `pm[t][1]` (KeyError when length-1 columns do not occur).
* The d10 agent now runs C^4 (x) C^5 (x) C^5, rank 8 vs 9 (`t455_*`, logs `hwv455_*.log`, status `agents/d10.md`).
