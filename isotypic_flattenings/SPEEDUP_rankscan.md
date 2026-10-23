# rankscan.py speed-ups (2026-10-23): same ranks, 2-7x faster on the expensive components, lower peak RSS

Branch `claude/project-thread-ttahoa-rankscan`, based on `claude/trusting-bohr-hdnmbv` (0f46ae8f). Only `rankscan.py`
changes; specialscan.py picks up items 1, 3 and 4 automatically because it imports `compute_F` / `RREF` from it.
`hwv_fast.py`, `sweep_fast.py`, `isoflat.py`, `scan_runner.py` are not touched. The sweep_fast/isoflat port runs on another
branch (`claude/project-thread-ttahoa-sweepfast`). rankscan.py has its own `compute_F`, `RREF` and filling choice, so
the two ports do not overlap.

## Where the time went (all records in scan/res, 806 worker-hours)
Matrix evaluation (`compute_F`) took 560 h. The elimination (`RREF`) took 91 h. The rest was mostly SATPROBE
evaluations and `choose_fillings` probes: one 6x6x6 d = 8 direction spent 518 s on 90 probes, which use the greedy
contraction path. Inside the evaluation, the time split between BLAS products, `np.ascontiguousarray` (transposes)
and `fmod`. Inside `RREF.add`, 90 % of the time was the unblocked row-by-row `_gauss_jordan` of each 128-row chunk.

## What changed (each can be switched off by an environment variable)
1. **Planned evaluation with reuse** (`NEWEVAL=1`, default): `compute_F` now runs one path of the WHOLE network, chosen from
   greedy, RandomGreedy and DynamicProgramming (flops / size / combo; the DP searches only run when the greedy
   estimate says the evaluation takes more than 5 / 60 / 600 s). It classifies every step by what it depends on:
   word minors only, source points Y, target points Z, or both. It then tiles the matrix: an outer side in blocks
   and the other side whole or in blocks. Word-minor-only intermediates are computed once, outer-only ones once per
   outer block, and inner-only ones once if the inner side is whole. The old code re-ran the whole path on every
   tile. The tiling minimises a cost model (flops + 30 per element moved + per-step overhead) under a memory model:
   kept intermediates plus 3 times the largest tensor of a tile must stay at or below MEMCAP. Before, only the largest
   tensor counted, and real peaks reached 3-5 MEMCAP. Networks with a greedy estimate below `PLANMIN` (2e9) keep the
   old path search, because planning costs more than they do.
   The filling probes (`cheap=True`) use the light plan.
2. **Cheaper evaluation basis, mapped back exactly** (`FILLPOOL=1500`, 0 = off): per rank, the code ranks 1500 random
   fillings (own RNG, so `crng` and with it the points, C and later directions are unchanged) by the greedy estimate.
   It probes them (zero functionals skipped) and plans the cheapest nonzero ones. The first g with independent probe
   vectors form a basis E. Since `v_E = A v_F` on the probe and the old probe vectors are independent, `E = A F` holds
   exactly. `profile()` evaluates E and sets `Fs = A^-1 E` mod p, so **the old matrices F_i are restored bit for bit**,
   for g = 1 and g >= 2, and phi, H_k, V_k are unchanged. The basis is used only if its planned cost is at most
   0.7 x that of the old fillings, the old cost is above FILLMIN / FILLMIN_GREEDY, and the search fits in 5 % of the
   estimated time. Example: the 6x6x6 separator ((5,3),(3,2,1,1,1),(2,2,1,1,1,1)) direction 2 (g = 2) went from a
   planned cost of 5.3e12 to 2.4e10.
3. **Blocked Gauss-Jordan in RREF** (`RREF_OLD=0`): `_rref_blocked` (from flattening_candidates/speedup_rref) replaces
   `_gauss_jordan` on each chunk. A full-rank 3000 x 3000 matrix takes 3.9 s instead of 19.4 s. For g = 1 the V
   elimination is skipped: V_1 = rank phi_1 = H_1 was computed twice.
4. **Layout-aware pairwise contraction** (`PAIR_OLD=0`): the index order inside each operand group follows the strides,
   so transposed views need fewer copies. The values are the same, because the code calls the same exact `fmatmul`.

All arithmetic stays exact mod p. Every pairwise product is still `hwv_fast.fmatmul` (float64, inner dimension below
2^15), so F does not depend on the path or the tiling. `NEWEVAL=0 FILLPOOL=0 RREF_OLD=1 PAIR_OLD=1` gives the old code paths.

## Checkpoints and resume
* Planned tilings write the same checkpoint format `{yb, zb, next}`. With Y blocks outside, the order is the old
  Y-major order, so old and new code can resume each other. With Z outside and Y cut, `next` is 0 for old readers,
  who redo the matrix rather than skip blocks, and `next2` / `order` are for the new code. The new code resumes any
  checkpoint whose tile shape fits 4 MEMCAP in its plan. Otherwise it falls back to the old loop with the saved shape.
* Checkpoints of the evaluation basis carry its own filling hash. If a checkpoint of an old filling exists for that
  rank (a worker of the old code), `legacy_ckpt` makes the new code evaluate that rank with the old fillings, and
  `adopt_ckpt_filling` still applies for g = 1, so the running 8x8x8 / 9x9x9 checkpoints stay valid. The evaluation
  basis is deterministic (seeded pool, deterministic plans), so a restarted new worker picks the same basis.
* Profile cache files (`_prof`) keep their names (old fillings), because the profiles are identical.
* Running workers keep the old module. Workers started after deployment use the new one. No runner change is
  needed, and the runner's memory estimates stay conservative because peaks went down.

## Verification (this container, OPENBLAS_NUM_THREADS=1, old and new run at the same time, PYTHONHASHSEED=0)
Same jobs as the scan (`rankscan.py n d` with NEED/RLO of the original job, LIST of the components). Record fields
compared: every direction's profiles at every evaluated rank, sat_from, cut, N1, K, span, the separations, unknowns
and status. **40 / 40 components identical.**

| job | components | wall old -> new | max peak RSS old -> new |
|---|---|---|---|
| 3x3x3 d=5, all (known separators 3/6, 12/15, 15/21) | 24 | 8.2 -> 5.5 s | 42 -> 41 MB |
| 4x4x4 d=8, the 8 separators of 6 vs 7 (incl. (62,3221,3221) H_k 304/309) | 8 | 108 -> 95 s | 720 -> 492 MB |
| 4x4x4 d=9 (81,333,3321) 396/400 | 1 | 3.2 -> 2.5 s | 222 -> 229 MB |
| 6x6x6 d=7 (511,4111,31111), (4111,331,331), (61,43,421), r 10-13 | 3 | 584 -> 119 s | 1010 -> 403 MB |
| 7x7x7 d=7 (61,43,421), r 12-18 | 1 | 613 -> 163 s | 1041 -> 810 MB |
| 6x6x6 d=8 (44,422,32111), (332,3311,22211), r 10-13 | 2 | 1360 -> 464 s | 1107 -> 446 MB |
| 6x6x6 d=8 separator (53,32111,221111), r 10 vs 11: H2 2775 / 2835 | 1 | 1577 -> 955 s | 1184 -> 628 MB |
| total | 40 | 4254 -> 1803 s (2.4x) | |

Per component the speed-up ranges from 0.9x (two small 4x4x4 g = 4, 6 components, 23 -> 25 s and 41 -> 45 s) to 9.5x
(6x6x6 (511,4111,31111): 396 -> 42 s). The large ones are where the scan spends its time: 6x6x6 d = 8 and 7x7x7 d = 7
took 280 h and 222 h. One evaluated rank of the 6x6x6 separator direction 1 went from eval 529 s + rref 90 s to
362 s + 31 s.
Tests: `test_speedup.py` (new): planned F == old F entry by entry, unblocked and tiled (MEMCAP 2^25 down to 2^11),
float32/float64 destinations, interrupted planned loops resumed by the new and by the old code (Y-major and Z-major
order), `_rref_blocked` == `_gauss_jordan`, RREF prefix ranks, evaluation basis `Ainv E == F` exactly and identical
profiles (g = 1, 2). Result: 33 ok, 0 failures. `test_ckpt.py` and `test_cut.py`: ALL OK.

## Caveats
* The evaluation basis costs 2-11 s per evaluated rank where it runs (only above ~4 min of estimated work).
* The cost model constants (MOVE_COST, SEC_PER_COST) were calibrated on one 6x6x6 d = 8 network on one core.
  The 8x8x8-10x10x10 frontier components (hours per rank, word minors near WCAP) were not timed here, because they
  exceed the 30-min / 4 GB test budget. Their correctness is covered by the same exactness arguments and the
  checkpoint compatibility above.
