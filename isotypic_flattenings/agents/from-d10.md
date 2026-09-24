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
