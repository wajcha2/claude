# Faster combflat.py: what changed and how to switch (2026-10-23)

This branch (`claude/project-thread-ea3b99`) is `claude/tender-ride-7mz2gl` at commit 934660c plus one change:
a faster `isotypic_flattenings/combined/combflat.py`. Nothing else in the pipeline (comb_search.py, comb_jobs.py,
test_comb.py, isoflat, hwv_fast) is touched. Ranks, lattice dimensions and separations are the same as before;
only the cost of evaluating a flattening changes.

Requirements are unchanged: `pip install sympy opt_einsum`.

## What changed

Only `Context.basis()` and `best_path()` change, plus three tunables.

1. **Choice of fillings (`Context.basis`).** An isotypic flattening of a component (λ, μ, ν) with multiplicity g is
   evaluated through g fillings of the three Young diagrams. Which word positions a filling puts in which columns
   decides the shape of the tensor-contraction network, and for the same component the cost of two random fillings
   differs by a factor 10 to 10^7 (e.g. 555 d=10 (91 | 61111, 61111): cheapest of 1500 is 5e10 flops, the median is
   4e15). The old code took the cheapest of about 6 random fillings. The new code
   * draws a pool of up to `FILLPOOL` = 1500 random fillings, in chunks of 100, and scores each by the greedy-path
     flop estimate of its network (shapes only, a few ms each), penalised when the largest intermediate exceeds
     `MEMCAP` (that forces block splitting);
   * stops enlarging the pool as soon as a filling below `FILLCHEAP` = 1e8 flops is found (small components do not
     pay for the scoring);
   * probes the fillings in order of increasing cost on small probe points (as before) and keeps the first g whose
     functionals are linearly independent.
2. **Contraction path (`best_path`).** For networks with at most `DPMAX` = 40 operands (2·(λ_1+μ_1+ν_1), i.e. every
   component up to d = 10 at least) the optimal path from opt_einsum's `DynamicProgramming(minimize='flops')` is used
   (and the `minimize='size'` optimum if the flop-optimal path exceeds MEMCAP). Before, `RandomGreedy(128)` was used
   and DP only as a fallback up to 24 operands. Above DPMAX and for the cheap probes nothing changes.

## Why the results are identical

* The isotypic component of the flattening is the span of the g functionals given by g linearly independent
  fillings; any g independent fillings span the same g-dimensional space. So the full-level subspaces (`levels g`)
  are the same subspaces, and every dimension computed from them is the same. For g = 1 the matrix is the same up
  to a nonzero scalar.
* Level 1 (and the partial levels) use a random generic combination Ψ of the g functionals, exactly as before; its
  rank is the generic rank for either basis (both are exact computations mod p = 524287 at random points, with the
  same probability of an accidental drop as the old code).
* The contraction path only changes the order of multiplication, never the result (exact modular arithmetic).
* Sample points, tensors (seed), source/target lists and the lattice enumeration are untouched.

## How to switch an existing checkout

```bash
git fetch origin claude/project-thread-ea3b99
cp isotypic_flattenings/combined/combflat.py isotypic_flattenings/combined/combflat.py.bak   # optional backup
git checkout origin/claude/project-thread-ea3b99 -- isotypic_flattenings/combined/combflat.py
```

(or copy the single file by hand; it is a drop-in replacement for the combflat.py of `claude/tender-ride-7mz2gl`
at any commit from 4af96b5 on).

* **Running jobs:** processes already running keep the old module in memory and finish normally. Every process
  started afterwards (comb_jobs.py starts a new comb_search process per job part) uses the new module. No restart
  is needed; restarting a long job early is worth it only if its remaining lattices are large (see timings).
* **Disk cache (`--cache`, default `live/cache/`) stays valid.** A cached file `r<r>_<λ>_<μ>_<ν>.npy` holds the
  flattening for one rank; files written by the old code differ from fresh ones only by the choice of basis of the
  same functional space, so mixing old and new files gives the same dimensions. No need to clear it.
* **`--resume` works unchanged:** it reads summary lines of earlier logs, whose format did not change. Only stderr
  gains one `#   basis ...: pool N, chosen cost ... (pool median ...)` line per component.
* **Tunables** (environment variables): `FILLPOOL` (1500), `FILLCHEAP` (1e8), `DPMAX` (40; set `DPMAX=0` to get the
  old RandomGreedy path back if a DP search ever stalls), `MEMCAP` unchanged.

## Test results (2026-10-23, 4 cores, OPENBLAS_NUM_THREADS=1, old and new run side by side with fresh caches)

All rank lines and summaries of the old and new runs are identical (diff of the logs after removing timings).

| test | result (both versions) | old wall / peak RSS | new wall / peak RSS |
|---|---|---|---|
| `test_comb.py quick` | 322 checks ok, 0 failures | 103 s / 0.17 GB | 77 s / 0.09 GB |
| `test_comb.py full` (new only, d8 555 thread) | 508 checks, 0 failures, incl. the known C^4 d=8 separators (62,3221,3221) H4 and (53,3311,3311) V2 | | 720 s |
| C^3 d=4, B, target (211, 211), ranks 3/4/5 | separator {22, 31}: 3/6/9, as in README | 1.1 s | 0.8 s |
| C^4 d=6, B, sources {51, 42, 411}, ranks 5/6/7 | (321,222) 196/316/320, (411,321) 392/512/516 (separate 6 vs 7); (411,3111) 146/150/150, (33,321) flat, as in README / ranked_candidates.md | 54 s / 0.25 GB | 53 s / 0.15 GB |
| 455 d=8 dir 0, sources {71, 62, 611}, target (3221, 2222), ranks 7/8/9 | singles 315, 360, 189; all 848/848/848 (no separation) | 158 s / 0.94 GB | 103 s / 0.64 GB |
| 455 d=9 dir 0, sources {711, 6111}, targets (3222, 22221), (42111, 22221) | 332/332/332 and 67/67/67, as in the d=9 job logs | 25 s / 0.54 GB | 23 s / 0.21 GB |
| 555 d=8 pattern:3, targets (2222,2222), (41111,22211), (41111,2222), ranks 9/10 | all flat, same singles as the d=8 555 job logs | 221 s / 0.77 GB | 120 s / 0.85 GB |

Per lattice (old → new): 555 d=8 (2222,2222) 87 → 36 s, (41111,22211) 116 → 46 s, (41111,2222) 18 → 38 s;
455 d=8 (3221,2222) 158 → 103 s. Small lattices can be a little slower (the pool scoring, ~5–20 s per component,
is paid once per component and cached in memory only); the gain grows with the component: on the large 455/555
d = 8, 9 components a single flattening evaluation is 12–30x faster (455 d=9 (72 | 3222, 3222) 87 s → 6 s,
555 d=8 (71 | 3221, 2222) 38–46 s → 3–3.6 s) and the largest intermediates shrink 5–100x, which is what lets
memory-bound jobs run.
