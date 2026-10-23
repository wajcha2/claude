# Lower-memory combflat.py: what changed and how to switch (2026-10-23)

Branch `claude/project-thread-xi7m9v` = `claude/project-thread-ea3b99` (the faster combflat.py, GUIDE.md)
+ the blocked `rref` of the "Degree 8 tests for 555" thread (`flattening_candidates/speedup_rref/`)
+ the memory changes below. Only `isotypic_flattenings/combined/combflat.py` changes; comb_search.py, comb_jobs.py,
test_comb.py, hwv_fast.py and isoflat.py are untouched. Requirements unchanged: `pip install sympy opt_einsum`.

## Where the memory went

1. **Lattices (`LatticeFamily`).** Every (member, level, rank) was stored as a `size x size` uint32 matrix
   (size = compressed ambient dimension, up to 12000-14000 for 555 at d = 9, 10), and building it and every
   `dims()` call made several `size x size` int64/float64 temporaries plus a `size x size` int64 random matrix R.
   555 d=10, target (61111, 61111), sources {91, 82, 811}: 8 matrices of 641 MB, temporaries of 1.3 GB each.
   This, not the contraction, is what pushed the d = 9, 10 family-B jobs to 8-11 GB and forced `--bmax 13000`.
   (The "new 11.4 GB vs old 8.4 GB" note in GUIDE.md compared runs stopped after 40 min at different points of the
   same lattice; the full run of the ea3b99 code peaks at 10.1 GB.)
2. **Flattening evaluation (`eval_F`).** Blocks were sized only by the largest single intermediate (MEMCAP = 2^25
   elements), but each pairwise contraction also holds both operands, their transposed copies and the product, so one
   evaluation reached 3-5 MEMCAP (0.4-1.3 GB). Each block also recomputed everything that does not depend on the
   block's sample points.
3. **Flattening outputs.** `flats()` stacked int64 matrices and then converted to uint32 (3x the final size), and all
   flattenings of a lattice stayed in memory until the lattice was done.

## What changed

* **Thin lattice storage.** Each subspace is kept as a matrix with about `dim + 8` rows (random combinations of its
  spanning rows, or the rows themselves when there are few) on the first `ncols = sum of the members' top dims + 8`
  generic coordinates (the sample points, as the old `dims()` already used; random combinations when aux >= 2).
  The single dims are found first on small sketches (t = 512, 1024, ... coordinates until dim <= t - 8). `dims(S)` is
  the rank of the stacked thin matrices (about h x h, h = sum of the single dims): the same number the old code got
  from `R[:c] (sum of size x c slices)`, now without the size x size objects and faster. Singles cost no rank at all.
  The RREF bases of `--exhaust` / greedy are taken from the thin matrices (ncols columns instead of size).
* **Memory-sized contraction blocks with reuse.** `eval_F` simulates the live memory of `execute()` along the path
  (`slice_plan`: live intermediates, transposed copies, products) and evaluates in blocks of source points (Y) or
  target points (Z) when it exceeds `EVALMEM` float64 elements (default 2^23 = 64 MB). The optimal path of the whole
  network is run block by block; the steps that do not involve the block's points are computed once (first block)
  and their results kept (`execute(..., reuse)`). The old halving search (one DP path per block shape) is only the
  fallback. Because the block-independent part is no longer repeated, small blocks cost little extra time.
* **Outputs.** `flats()` writes each functional straight into the uint32 result; lattice blocks are built in row
  chunks with float64 `fcombine` (no int64 temporaries); after a member's thin matrices are built its flattenings
  leave memory if the disk cache holds them (`Context.release`; they are reloaded from the cache when needed again).
* `execute()` / `_contract()` release each pairwise operand as soon as its transposed copy exists.
* `block_matrix` / `compressed_rank` (family E) build float64 directly.

## Why the results are identical

* The fillings, Psi, sample points and tensors are unchanged (MEMCAP, which steers the filling choice, keeps its
  value), and the contraction only changes order and blocking in exact arithmetic: the flattening matrices are
  bit-identical (md5 checked) and the disk cache stays valid.
* Lattice dimensions: a prefix of c generic coordinates is injective on a space of dim <= c - 8 (the argument the old
  `dims()` already relied on), and dim + 8 random combinations of a spanning set span it, both except with
  probability < p^-8; the dims are the exact ranks, as before.

## Results

(filled in below)

## How to switch

```bash
git fetch origin claude/project-thread-xi7m9v
git checkout origin/claude/project-thread-xi7m9v -- isotypic_flattenings/combined/combflat.py
```

Drop-in for the combflat.py of `claude/tender-ride-7mz2gl` (4af96b5 on), ea3b99 and speedup_rref. Running processes
keep the old module; every new comb_search process uses the new one. Cache and `--resume` stay valid; log format
unchanged (the `size=` in summary lines is still the nominal compressed size).

Tunables (environment): `EVALMEM` (float64 elements one evaluation may hold, default 2^25 = 256 MB; 2^23 gives
~70 MB at about the same speed), `STEPCOST` (2e5, block overhead in the block-size choice), `MEMCAP` (2^25, still
used for the filling choice and the path search; changing it changes the chosen fillings, not the ranks).
