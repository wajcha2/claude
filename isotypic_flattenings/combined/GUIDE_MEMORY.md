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
  The lattice is built in two passes over the members: first the single dims, on small sketches (t = 512, 1024, ...
  coordinates until dim <= t - 8), then the thin matrices directly on the ncols coordinates (with the disk cache the
  flattenings are reloaded in between instead of kept). For aux >= 2 the projection W is kept as float32 column blocks
  of 512. `dims(S)` is the rank of the stacked thin matrices (about h x h, h = sum of the single dims): the same number
  the old code got from `R[:c] (sum of size x c slices)`, now without the size x size objects and faster. Singles cost
  no rank at all.
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

Wall time and peak RSS (ru_maxrss of the process), `OPENBLAS_NUM_THREADS=1`, fresh caches, old and new run at the same
time on the same 4-core container (13-15 GB). "old" = ea3b99 + speedup_rref (blocked rref). Every row: the rank lines of
the log are identical between old and new.

| job | old | new |
|---|---|---|
| 555 d=10 `5 10 9,10 --fam B --aux 1 --allsub 3 --sources "91;82;811" --only-mn "61111\|61111" --bmax 16000` | 2677 s, 10.07 GB | 1034 s, 0.76 GB |
| 455 d=9 `4,5,5 9 7,8,9 --dir 0 --fam B --aux 1 --exhaust 14 --sources "711;6111" --bmax 16000 --only-mn "3222\|22221;42111\|22221"` | 26.1 s, 0.21 GB | 23.5 s, 0.13 GB |
| 555 d=8 `5 8 9,10 --fam B --aux 1 --exhaust 14 --sources pattern:3 --bmax 4000 --only-mn "2222\|2222;41111\|22211;41111\|2222"` | 175 s, 0.85 GB | 129 s, 0.14 GB |
| 455 d=8 `4,5,5 8 7,8,9 --dir 0 --fam B --aux 1 --exhaust 14 --sources "71;62;611" --only-mn "3221\|2222"` | 41.6 s, 0.64 GB | 28.6 s, 0.14 GB |
| 455 d=6 aux 2 `4,5,5 6 8,9 --dir 1 --fam B --aux 2 --exhaust 14 --bmax 4000` (both stopped at 1500 s) | 53 lattices, 1.34 GB | 59 lattices, 0.25 GB |
| C^4 d=6 separator check (`4 6 5,6,7 ... --only-mn "321\|222;411\|321"`) | 28 s | 19.5 s, 0.13 GB, 316/320 and 512/516 as before |
| `test_comb.py quick` | 87.6 s, 0.09 GB | 98 s, 0.07 GB, 0 failures |

The old code on 555 d=10 with 4 BLAS threads: 2348 s, 10.08 GB. Where the d=10 time goes now: the flattenings of the
member 82 (2 x 3858 x 12658 per rank) take 350 s per rank, the rest is the other members and the 11 sums. The new peak
there is the 82 flattenings themselves (391 MB per rank) plus one evaluation block. The test_comb slowdown (about 10 s)
is the block planning on tiny cases; real jobs are faster.

**Parallel jobs.** The work is mostly single-threaded numpy (fmod, copies, small products), so 4 BLAS threads in one
job oversubscribe the cores when several jobs run. Run each job with `OPENBLAS_NUM_THREADS=1` and run up to one job per
core: at d <= 9 they stay under 0.2-0.5 GB each, at 555 d=10 under 1 GB.

## How to switch

```bash
git fetch origin claude/project-thread-xi7m9v
git checkout origin/claude/project-thread-xi7m9v -- isotypic_flattenings/combined/combflat.py
```

Drop-in for the combflat.py of `claude/tender-ride-7mz2gl` (4af96b5 on), ea3b99 and speedup_rref. Running processes
keep the old module; every new comb_search process uses the new one. Cache and `--resume` stay valid; log format
unchanged (the `size=` in summary lines is still the nominal compressed size).

Tunables (environment): `EVALMEM` (float64 elements one flattening evaluation may hold, default 2^23 = 64 MB; larger
values give fewer, bigger blocks, e.g. 2^25 = 256 MB, at about the same speed), `STEPCOST` (2e5, block overhead in the
block-size choice), `MEMCAP` (2^25, unchanged; still used for the filling choice and the path search: changing it changes
the chosen fillings, so the cache, not the ranks), `OPENBLAS_NUM_THREADS=1` (see Parallel jobs above). `RREF_OLD=1`
restores the old rref (comparison only).
