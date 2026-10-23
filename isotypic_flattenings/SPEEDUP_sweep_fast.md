# sweep_fast.py: what the combflat speed/memory techniques give here (2026-10-23)

Branch `claude/project-thread-ttahoa-sweepfast` = `claude/wonderful-fermat-1v76ux` (at bebaf658) + changes to
`hwv_fast.py`, `isoflat.py`, `sweep_fast.py` only. Same tensors, same random streams, same fillings, same sample points:
every matrix whose rank is taken is bit-identical (SHA1 of every ranked matrix compared, see Verification), so claims,
done-logs, `RESUME` logs, `#partial` lines and `CKPT_SECS` checkpoint files stay valid and old and new workers can be
mixed in one claim directory. To switch: check out the three files from this branch; running workers keep the old code
until relaunched (the check-in scripts relaunch with `RESUME`).

## What changed

1. **Pairwise contraction (`hwv_fast.pair_contract_fast`, default; `HWV_PC=ref` = old).** The old code copied both
   operands into (batch, free, contracted) order and called one batched `np.matmul`. Now: an operand already in a
   usable order is passed as a (transposed) view; the batch is a loop of 2-D `np.dot` into a preallocated result
   (numpy's batched matmul with OpenBLAS threads > 1 is up to 12x slower than the loop; `np.matmul(out=...)` with a
   transposed operand falls out of BLAS); products without a summed index are one broadcast multiply; small sums with
   many batches (or whose BLAS layout would need a big transposed copy) go through `np.einsum` on the operands'
   layouts (a rough time model decides). Exactness is unchanged: every entry is an integer sum of < 2^15 products
   < p^2, exact in float64 in any order, then `fmod`. `execute` drops its operand references after each contraction.
2. **`isoflat.modrank` panel width 256 -> 64** (`MODRANK_BLOCK`). The panel elimination / forward substitution is
   O(n m block) and dominated at 256. Single thread: 1184^2 rank 1176: 2.75 s -> 0.88 s; 3000^2: 19.2 s -> 8.6 s.
   New `overwrite=True`: a float64 H stack is ranked in its own buffer (one full-size copy less).
3. **Low-memory streaming of the noV H stacks (`LOWMEM=1`, default; `LOWMEM=0` = old code).** F stays float64,
   Fgen and the compressed H are updated in row chunks (no full-size `c*F`, `F % p`, float copy and product
   temporaries), H is ranked in place. Same random draws (R is still drawn block by block as before).
4. **Path refinement (`REFINE`=1e11 flops, `REFINE_REPEATS`=1024; `REFINE_REPEATS=0` = off).** A flattening whose
   path estimate (x number of blocks) exceeds REFINE gets a 1024-trial RandomGreedy search on its (block) network; the
   new path is kept if cheaper and its largest intermediate stays within MEMCAP. Costs 1-2 s per flattening.
   MAXFLOPS is still decided on the unrefined estimate, so 'NOT CHECKED' decisions are the same as before.
5. **Vector minors memoized** (`hwv_fast.minors_of_vectors`): prepare() recomputed them for every direction, rank and
   probe (3 s of a 31 s d = 13 component).

## What does not apply (measured)

* **Blocked RREF** (speedup_rref): `modrank` already was a blocked LU (getrf style); only the panel width was too big (2.).
* **DP path, minimize='flops' (fillpool_dp).** On the block networks that are actually executed DP gains ~2 %
  (d = 10, 4,5,5: 1.435e9 vs RandomGreedy(128) 1.463e9); on 38-42-operand d = 13/14 networks DP needs 50-90 s per
  call (and the d13 agent saw 7.4 GB in the DP table at 44 operands), so RandomGreedy(1024) refinement (4.) is used
  instead. The filling pool is not adopted: a different filling choice changes the random stream and the matrices.
* **Reuse of the block-independent part (combflat `execute(reuse)`).** In sweep_fast's block plans the part that does
  not depend on the sliced points is 0.1-0.3 % (Z blocks, d = 10) and 0.01 % (Y blocks, d = 14) of the block flops.
  Running the whole-network optimal path block by block with reuse (combflat's scheme) needs 1.0-1.35x fewer flops than
  the halving plan on the measured flattenings (d = 10: 3.70e9 -> 3.14e9, 5.05e9 -> 3.74e9, 5.85e9 -> 5.73e9;
  d = 13 ((12,1),(5,2,2,2,2),(4,3,2,2,2)): 3.56e10 -> 2.85e10, 6.48e10 -> 5.21e10; d = 14
  ((9,5),(6,2,2,2,2),(4,3,3,3,1)): 6.0e12 vs DP whole path 5.8e12), and the refinement (4.) already reaches most of
  that on the expensive ones (3.56e10 -> 2.88e10). Not implemented.

## Measured (old = bebaf658, new = this branch)

Whole components, old and new run side by side on the same (shared, loaded) container, `OPENBLAS_NUM_THREADS=1` as the
agents run, seed 5, `noV`; MEMCAP 2^25 (d = 10) / 2^26 (d = 13) as in the agents' jobs. CPU = user seconds (wall times
are inflated by other jobs on the machine). Every rank line and the SHA1 of every ranked matrix are identical.

| component | old CPU s / peak RSS | new CPU s / peak RSS |
|---|---|---|
| 4,5,5 d=10 ((7,2,1),(5,5),(4,4,2)) g=1 | 39.1 / 815 MB | 29.6 / 562 MB |
| 4,5,5 d=10 ((8,2),(3,3,2,1,1),(3,3,2,1,1)) g=5 | 84.3 / 1166 MB | 80.9 / 800 MB |
| 4,5,5 d=10 ((5,5),(5,3,1,1),(3,3,3,1)) g=1 | 144.2 / 785 MB | 133.1 / 773 MB |
| 4,5,5 d=10 ((4,4,2),(5,2,2,1),(3,3,3,1)) g=7 | 479 / 1172 MB | 506 / 1159 MB |
| 5 d=13 ((12,1),(3,3,3,3,1),(3,3,3,2,2)) g=1 | 15.4 / 500 MB | 12.4 / 489 MB |
| 5 d=13 ((12,1),(5,2,2,2,2),(4,3,2,2,2)) g=1 | 44.2 / 588 MB | 39.5 / 586 MB |
| 5 d=13 ((10,3),(4,3,2,2,2),(3,3,3,2,2)) g=4 | 132.6 / 1131 MB | 113.4 / 759 MB |

So on small and medium components (the d10 agent's queue) the gain is modest: 0-25 % CPU, up to 35 % less memory.
At one BLAS thread the old batched matmul was not the bottleneck; the contraction is bound by the elementwise `fmod`
(about a third of the time and unavoidable: products must be reduced before the next contraction), by copies and by the
path search (~15 % at d = 10: RandomGreedy plus the DP-size fallback in every halving step, for both ranks). With
OpenBLAS threads > 1 the old code is much slower (batched-matmul thread overhead) and the new one 1.5-3x faster per block.

Where the d13 agent's hours go -- single flattenings of a C^5 d = 14 component cut into thousands of blocks -- the gain is
large. ((9,5),(6,2,2,2,2),(4,3,3,3,1)) (done-log: 66638 s), N1 x K = 9808 x 4908, CPU per block measured on 4-6 blocks
(old path + old contraction vs refined path + new contraction; the blocks compared equal), extrapolated to the flattening:

| flattening | block plan | old | new |
|---|---|---|---|
| filling A | 3 x 4908, 3270 blocks | 1.72 s/block, 1.6 h | 1.03 s/block, 0.9 h (x1.7) |
| filling B | 1 x 2454, 19616 blocks | 1.06 s/block, 5.8 h | 0.15 s/block, 0.8 h (x7.3: refined path 1.45e9 -> 9.8e8 flops/block, largest intermediate 3.8e7 -> 5.0e6) |
| filling C | 3 x 4908, 3270 blocks | 2.29 s/block, 2.1 h | 1.32 s/block, 1.2 h (x1.7) |
| filling D | 1 x 2454, 19616 blocks | 1.44 s/block, 7.9 h | 1.05 s/block, 5.7 h (x1.4) |

Memory of the noV H streaming at full size (fake flattenings, real N1 x K = 4958 x 3508, g = 2, d = 14 component
((7,7),(4,4,2,2,2),(4,3,3,3,1))): peak RSS 3.09 GB -> 2.13 GB, CPU 387 s -> 276 s (mostly modrank), same ranks.

## Verification

* `sweep_fast.py 4 4 6,7`: 15 rank lines identical to the old code, FOUND: []; every pairwise contraction of that run
  computed by both `pair_contract_ref` and `pair_contract_fast`: 7166 contractions, all equal.
* C^4 d = 8 hit ((6,2),(3,2,2,1),(3,2,2,1)): H1:304/309, `*** SEPARATES`, SHA1 of all 12 ranked matrices identical
  (noV, also with `CKPT_SECS` checkpoints written after every filling), and all ranked matrices identical without noV.
* The seven components above: rank lines and SHA1 of every ranked matrix identical (6-12 matrices each).

## Caveats

* The container was shared with other jobs during all measurements (load 3-5 on 4 cores); wall times vary by +-30 %.
  The side-by-side runs above (old and new at the same time, one BLAS thread each, as the agents run) are the fair
  comparison; user CPU seconds are given too.
* The peak RSS of large components is dominated by contraction intermediates (several of MEMCAP elements live at
  once, MEMCAP = 2^26 doubles = 512 MB in the d13 runs). Sizing blocks by simulated live memory (combflat's EVALMEM)
  would cut that further at the price of more blocks; not done here. Lower MEMCAP if memory is tight.
* `REFINE` changes the path (never the result); `HWV_PC=ref LOWMEM=0 REFINE_REPEATS=0 MODRANK_BLOCK=256` restores the
  old code paths exactly.
