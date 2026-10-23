# Rank scan: which tensor ranks do isotypic flattenings separate? (n x n x n, n = 3..10, d = 1..10)

Live results: `scan/STATUS.md` (snapshot committed every 30 min; the live copy in the untracked `scan/live/` is regenerated every 15 min and after every job), machine-readable `scan/summary.json`,
raw per-component records `scan/res/<job>.jsonl`, resources `scan/monitor.log`, runner log `scan/runner.log`.

## Question
For T in C^n (x) C^n (x) C^n and each rank r < r_gen (generic rank: 5 for n = 3, ceil(n^3/(3n-2)) otherwise,
i.e. 5, 7, 10, 14, 19, 24, 30, 36 for n = 3..10): what is the lowest degree d such that some isotypic flattening of
degree d has strictly smaller rank on a general rank-r tensor than on a general rank-(r+1) tensor, and which
components (partition triples) do it in that degree?  For each n the scan stops raising d once r_gen - 1 vs r_gen
is separated (or at d = 10).

## What is computed (`rankscan.py`)
For each component lam = (l1, l2, l3) of degree d (Kronecker coefficient g > 0) and each flattening direction:
* a basis F_1..F_g of the isotypic flattenings (g fillings with independent functionals, as in `sweep_fast.py`),
  and generic functionals phi_j = sum_i C_ji F_i (random C);
* for every k = 1..g, with U_k = span(phi_1..phi_k) a generic k-dimensional subspace of the multiplicity space:
  `H_k`: S^{l1}V^* -> U_k^* (x) S^{l2}V (x) S^{l3}V and `V_k`: U_k (x) S^{l1}V^* -> S^{l2}V (x) S^{l3}V
  (k = 1: one generic functional; k = g: the whole multiplicity space).  All prefix ranks come from one exact
  incremental elimination mod p = 524287;
* these ranks on random tensors of rank r.  The flattening rank is non-decreasing in r, so only a few r are
  evaluated: upwards from the smallest unresolved rank with doubling steps until every rank has reached its upper
  bound (min of the matrix dimensions; then nothing changes any more), then bisection of every interval whose ends
  differ.  Equal ends prove there is no jump inside.
* Evaluation of the flattening matrices: `hwv_fast.py` (highest weight vectors evaluated on the rank decomposition,
  Cauchy-Binet network, exact float64 BLAS), sampled on N1 = min(n1, g n23) + 8 source points and
  K = min(g n1, n23) + 8 target points, which preserves the ranks of all H_k and V_k.  New here: minors by Laplace
  recursion (the old ell!-term expansion is infeasible for n >= 6) and an exact float64 incremental RREF.
* Validation: C^3 d = 5 reproduces the three known rank-4 separators (3/6, 12/15, 12/15 and V2 15/21); C^4 d = 8
  reproduces ((6,2),(3,2,2,1),(3,2,2,1)) H_k = 304/309 for k >= 2 (225/225 for k = 1, 160 on rank 5) and d = 9
  ((8,1),(3,3,3),(3,3,2,1)) 396/400.

## Scheduling (`scan_runner.py`)
Jobs (n, d, stage): stage s holds the components of degree d whose cost proxy g * sum_dir N1 K lies in the band
(CAPS[s-1], CAPS[s]], CAPS = 3e5, 3e6, 3e7, 3e8, 3e9.  For each format, degree d is completed in every band before
degree d + 1 starts (the lowest separating degree needs all of degree d), and degrees above the lowest degree that
separates the target rank (r_gen - 1, or lower if a rank is skipped) are not run.  A job resolves only the ranks
not yet separated in a lower degree.  4 worker processes (one BLAS thread each) take the runnable jobs: up to 2026-10-06 18:30 in the order
(band, n) (cheap bands first, small formats first); since then by fair share -- a free slot goes to the format with
the fewest running workers, ties to the format with the fewest unchecked components left in its current degree (since
2026-10-07 07:08: ties to a degree with <= 10 components left, else round robin by the oldest last worker start -- the
fewest-left rule let 9x9x9 and 7x7x7 win every tie and starved 10x10x10 d = 6 and 8x8x8 d = 7 for hours) (the
old order let the 3-4.5 h components of 7x7x7 d = 7 hold every slot while 6x6x6 d = 7 and 8x8x8 d = 6 waited with
3 and 5 components left). Memory admission (since 2026-10-06 23:07): a worker is started only if the estimated peak memory of the
component it will take plus that of the running components fits 15 GB (15.3 GB since 2026-10-08 02:20, 15.8 GB since 2026-10-13 10:45: every one of the 2657 recorded network peaks is at least 0.25 GB below its estimate -- 6x6x6 d = 8 at least 1.3 GB, median estimate 3.1 x the peak -- so k workers stay 0.25 k GB below the budget; since 2026-10-18 07:43 the evaluation-phase estimate no longer adds a second 0.8 GB on top of its calibrated 0.5 GB margin -- 6x6x6 d = 8 2.9 -> 2.4 GB, 8x8x8 d = 7 4.1 -> 3.3 GB, every recorded peak still >= 0.2 GB below its estimate; since 2026-10-19 11:29 a rerun with a larger WCAP adds its largest word-minor tensor + 1 GB instead of a flat 4 GB (8x8x8 hook rerun 7.9 -> 6.7 GB; every recorded rerun peak >= 0.4 GB below); at 15.3 GB the 9.4 GB 9x9x9 component plus two 6x6x6 d = 8 components (3.0 GB each, real peaks <= 1.4 GB) did not fit and two cores idled; the container has 16 GB, no swap;
adjustable in scan/live/membudget).  Estimate per component: two phases of its largest direction -- evaluation
(g flattenings N1 x K + word minors and contraction blocks, calibrated per (n, d) on the recorded peaks) and
elimination (flattenings + combination + eliminations 8 (N1 K + N1^2 + K^2) bytes) -- checked against all 2376 recorded
peaks (none above its estimate).  Trigger: the 8x8x8 d = 6 component ((3,2,1),(3,2,1),(3,1,1,1)) (g = 4, V
elimination 21512^2) and the 6x6x6 d = 7 component ((4,2,1)^3) (g = 9) need ~7 GB each; ((3,2,1)^3) on 8x8x8 (g = 5)
~10 GB.  A component that does not fit waits (it is not skipped); the two youngest workers were stopped at 23:07
(their components are redone).  While a component waits, later jobs may backfill only as long as the backfilled
components together leave room for it (it fits as soon as the other running components finish; since 2026-10-07 01:42).
Exception (to keep cores busy behind a long waiting component): cheap (cost band <= 3) or small (<= 4 GB) components
-- and, since 2026-10-20 07:47, components of any size while non-backfilled components alone keep the waiting one out (the 4.8 GB 7x7x7 d = 7 components were starved behind the 9.4 GB 9x9x9 one, which could not start before the 8x8x8 hook rerun ends anyway) -- may backfill regardless, and since 2026-10-20 09:19 a job whose next component cannot start before a non-backfilled component running > 4 h finishes holds no reservation at all (the next job in line does; the 4.8 GB 7x7x7 components never fitted between the small ones while the 9.4 GB 9x9x9 one waited for the hook rerun); but not past a waiting extra-job component and, since 2026-10-12 13:48, not for more than
BFWAIT s (scan/live/bfwait; 1 h, 30 min since 15:52) of the time in which only backfilled components keep the waiting
one out (since 15:52; before, the clock ran from the start of the wait, so a component blocked by a long
non-backfilled one left cores idle to no effect): the 10x10x10 d = 6 component ((5,1),(2,2,1,1),(2,2,1,1))
(~7.4 GB) waited behind a stream of small 6x6x6 d = 8 components -- every freed slot was refilled at once, so the
running estimates never dropped below budget - 7.4 GB; it started 1 h 45 min after it began to wait, 11 min after
the exceptions ended.  When the clock has run out, only backfills that the waiting component fits beside, as soon as the backfills that kept it out at that moment have finished, are admitted (since 2026-10-18 12:46; it then starts no later than without them -- before, nothing backfilled and a core sat idle 1.5 h behind a 3.4 h 8x8x8 backfill); originally nothing backfilled at all until the waiting component started; and since 2026-10-18 19:19, while every backfill still keeping it out has run more than 4 h (LONGRUN), cheap/small components may backfill again (each delays it by at most its own run time once the long one finishes; a core had idled behind the 10 h 8x8x8 component ((6,1),(2,1^5),(2,1^5)) that the waiting 9.4 GB 9x9x9 component needs gone)
(since 19:25; the reservation rule alone, room once the non-backfilled components finish, still let small
components in while a long non-backfilled one ran).  A restarted runner re-reads the backfill set and the wait start
from runner.log.  A component running longer than the time limit is stopped and listed as
not checked (time limit; 4 h since 2026-10-04 17:00, 8 h since 2026-10-06 17:30 when the 7x7x7 d = 7 components reached 3.4 h, 16 h since 2026-10-06 20:05 (two of them past 5 h, CPU-bound, steady memory), 30 h since 2026-10-11 13:05 (10x10x10 ((5,1),(2,1^4),(2,1^4)) probed at r = 12 needs ~20 h: its 15023 x 15023 matrix is evaluated in 60092 blocks of one column), 72 h since 2026-10-18 18:55 (user: do not stop long components unless they run for days -- they may be worth a closer look; running then: the 8x8x8 d = 7 components ((6,1),(2,1^5),(2,1^5)) at 9.5 h and ((6,1),(2,2,1,1,1),(2,2,1,1,1)) at 4 h), adjustable at run time in scan/live/tlimit, the worker limit in
scan/live/ncores) -- the cost proxy counts matrix entries only and underestimates large n, d by up to 1e5.
Skipped ranks: 5x5x5 rank 9 vs 10 (left to the d13 agent, needs d >= 13).
Limits: an intermediate of the contraction is capped at max(MEMCAP = 2^25, largest input) elements (larger ones
are split into blocks of evaluation points); a rank r whose word-minor tensor C(n, ell) r^ell exceeds 2^26 elements
cannot be evaluated and is reported as unknown (this is what limits large n and long columns).
Per component the record holds wall and CPU time and the peak RSS; `scan/monitor.log` has memory, per-worker
RSS and load every 5 minutes.

## Beyond the word-minor limit: the family ((d),(1^d),(1^d)) (`wedge_family.py`)
For this component (g = 1) every word with a repeated letter dies, and the isotypic tensor of
T = sum a_i (x) b_i (x) c_i is d! sum_{|S| = d} a_S (x) wedge b_S (x) wedge c_S.  Its flattening ranks are computed
exactly from C(r,d) x C(n,d) minors and products of linear forms -- no r^d tensor -- validated against rankscan.py on
five cases (3x3x3 d=2, 4x4x4 d=3, 6x6x6 d=4, 7x7x7 d=5, 10x10x10 d=3: identical ranks).  It resolved three
frontier ranks that rankscan.py could not evaluate (word-minor tensor above WCAP; records in scan/res/n*_w1.jsonl,
log scan/wedge_frontier.log): 8x8x8 rank 12 vs 13 at d = 6 (742 / 784), 9x9x9 rank 13 vs 14 at d = 6 (1716 / 3003),
10x10x10 rank 13 vs 14 at d = 5 (1287 / 2002), direction 1 (S^d V^* -> wedge^d V (x) wedge^d V).  The other
components with a (1^d) partition at those degrees are rerun with WCAP = 2^28 as extra jobs (n10_d5_x1, n8_d6_x1:
one worker at a time over all extra jobs, ~5 GB each).

## One-row components ((d), mu, mu): closed-form fast path (`onerow_family.py`, used by rankscan.py since 2026-10-05 03:40)
A component with a one-row partition has g = 1 and is ((d), mu, mu).  At alpha^d the isotypic tensor is the S^mu-part
of T(alpha)^{(x)d}, T(alpha) = B^T diag(A alpha) C, and its value at (g' v_mu) (x) (g'' v_mu) is the highest-weight
matrix coefficient prod_{columns j of mu} Delta_{mu'_j}(g'^T T(alpha) g'') (leading principal minors).  rankscan.py
evaluates these components this way (env ONEROW=1, default; record field dirs[].method = 'onerow'): O(n^3) per entry,
no word-minor tensor.  Validated: 122 stored (component, direction, rank) values (scan/onerow_check.log) and a rerun of
65 components of n = 4..6 jobs with identical ranks and separations (140 values).  Example: the 7x7x7 d = 7
components ((7),(2,2,1,1,1),(2,2,1,1,1)) and ((7),(2,2,2,1),(2,2,2,1)) at ranks 12, 13 take 80 s each (saturated,
no separation of rank 12; scan/onerow_frontier.log).

## Components (lam, lam^T, (1^d)): one determinant per entry (`colwedge_family.py`, used by rankscan.py since 2026-10-07 14:40)
A one-column partition (1^d) forces g = delta(mu, lam^T), so these components are (lam, lam^T, (1^d)).  Antisymmetrising
the (1^d) factor leaves X_T = sum_{|S| = d} wedge_{i in S}(a_i (x) b_i) (x) wedge_{i in S} c_i, the highest weight vector of
S^lam A (x) S^{lam^T} B inside wedge^d(A (x) B) is wedge_{boxes x} e_{row x} (x) f_{col x}, and Cauchy-Binet turns the sum over S
into one d x d determinant: F(g', g'', g''') = det(sum_i <a_i, g'_{row x}> <b_i, g''_{col x}> <c_i, g'''_k>)_{x in lam, k <= d}.
Cost O(r d^2) per entry and no word-minor tensor -- rankscan.py's evaluator needs C(n, d) r^d entries for the column, which
is above any WCAP for the frontier (8x8x8 d = 7 at r = 13: 8 * 13^7 = 5e8).  Validated against the network evaluator on
IDENTICAL tensors (n = 4..7, d = 4..6, all three directions, ranks d .. r_gen, including ranks below the bound):
scan/colwedge_check.log, no mismatch.  Example: 8x8x8 ((6,1),(2,1^5),(1^7)) at r = 13 in 60 s (all directions at their
bounds 1728, 216, 8), previously not evaluable.

## Frontier components above the word-minor limit: reruns n8_d7_x1, n9_d6_x1, n10_d6_x1 (2026-10-07)
At the frontier ranks, 42 of the 341 components of 8x8x8 d = 7 (r = 13), 25 of 119 of 9x9x9 d = 6 (r = 14) and 25 of
119 of 10x10x10 d = 6 (r = 15) have a word-minor tensor above WCAP = 2^26 and were recorded as unknown.  Of these, 7, 5
and 5 are (lam, lam^T, (1^d)) (closed form above), the other 35, 20, 20 fit WCAP = 2^28; the extra jobs n*_x1 rerun them
(closed-form ones first).  Without them those degrees cannot be reported complete.  Correction (2026-10-08 05:50):
the lists were made from the word-minor size at the frontier rank alone, but the normal jobs start one rank lower
(r = 13 for 9x9x9) where most of these components fit and were already at their rank bounds, which settles every
larger rank; 17 of the 25 9x9x9 reruns were redundant (about 7 worker-hours, including one 5.4 h component).  The
lists now hold only components a normal job left unresolved at the frontier rank; components not yet tried by a
normal job are added by the runner (refresh every 15 min) only if their normal record leaves that rank open.  In addition rankscan.py now probes
the highest feasible rank when the needed ranks are above the limit (SATPROBE, at most 4 below): a direction at its
bounds there separates no larger rank.

## Open candidate: 10x10x10 d = 6, ((5,1),(2,1^4),(2,1^4)) (2026-10-12)
The only frontier component so far that is NOT at its rank bounds where it could be evaluated: its normal run (rank 14
is above WCAP = 2^26, so SATPROBE evaluated r = 12; 18.4 h) gave direction 0 (S^{(5,1)}V^* -> S^{(2,1^4)}V (x) S^{(2,1^4)}V)
rank 6996 of 15015 at r = 12; direction 1 is at its bound 2310.  So this component may separate 15 vs 16 at d = 6 (the
10x10x10 frontier) -- or not.  Deciding it needs direction 0 at r = 15 and 16 (WCAP 2^28; word-minor tensor 2.6e8 at
r = 16): the 15023 x 15023 evaluation is split into ~30000 blocks of ~10 s, about 90 h per rank on one core.  The rerun
was stopped after 5 min and the component taken off the queue (state.json: jobs.n10_d6_x1.open_candidates); options:
parallelise the block loop over all cores (~1 day per rank with the machine to itself), or a closed form for this
hook-shaped component.  Until then 10x10x10 d = 6 is not complete for r = 15.

## 10x10x10 paused (2026-10-13 09:23 UTC, at the user's request: smaller formats first)
scan/live/pause lists the paused formats (now: 10); the runner starts no worker for them.  The running 10x10x10 d = 6
component ((5,1),(2,2,1,1),(2,1^4)) was stopped after 11.6 h (SATPROBE at r = 12 -- like the open candidate it has
a five-row hook factor, so its direction 0 would most likely end below its bound and need the same ~90 h per rank
reruns); its claim was released, so it is redone when 10x10x10 resumes.  Its 7.6 GB reservation had kept the 9.4 GB
9x9x9 d = 6 components waiting.  The open candidate stays open.  10x10x10 state when paused: d <= 5 complete for
r = 15, d = 6: 24 of 119 components of band 4 (29 of 119 overall) checked, none separating.

## Checkpoints of long block evaluations (2026-10-20)
Container restarts kill every worker (2026-10-13 12:45 to 10-18 07:10; 10-18 23:52; 10-20 00:35), and the 8x8x8 d = 7
rerun of ((6,1),(2,1^5),(2,1^5)) (ranks 13, 14 with WCAP 2^28) lost 1.5 h and then 24.7 h of work.  rankscan.py now
saves the block loop of compute_F (the matrix so far and the next block) every CKPT_EVERY = 1800 s to <CKPT>/
(scan/live/ckpt, set by the runner; untracked) and resumes from it.  The file name is a hash of everything the matrix
depends on (evaluation points, the rank-r tensor, the filling, prime, sizes), so only the identical computation
resumes it; the saved block shape is reused (the path search is randomised); a finished matrix is kept until the
rank profile of that rank is done, then all its checkpoints are deleted.  Test (test_ckpt.py, 4x4x4 d = 6,
MEMCAP 2^12, 88 blocks): interrupted at block 6, resumed, matrix identical to the uninterrupted one; the profile with
checkpoints equals the one without.  Workers started before 2026-10-20 00:46 run without checkpoints.
Fix 2026-10-20 19:38: the first real resume failed.  The filling (highest weight vector) is chosen among random candidates by a path-cost ranking whose ties depend on Python's per-process string hashing, so the restarted 8x8x8 hook rerun picked candidate 4 instead of 6 and found no checkpoint (13 h of work at block 15069 of 41216 would have been redone).  Now (a) a checkpoint stores its filling and is named <points/tensor hash>_<filling hash>; (b) for g = 1 -- every filling with a nonzero vector gives the same flattening up to a nonzero scalar, so the rank does not depend on it -- a worker adopts the filling of an existing checkpoint of the same slot (rankscan.Direction.adopt_ckpt_filling); (c) workers run with PYTHONHASHSEED=0, so the choice is reproducible (for g >= 2 too).  The old checkpoint's filling was identified by replaying the candidate draws (candidate 6) and the file moved to the new scheme.  test_ckpt.py also tests (b).

## Finished ranks kept; adjacent ends decided on a leading block (2026-10-21 20:12)
The 8x8x8 hook rerun finished rank 13 at 19:52 (direction 0, source S^{61}: H1 = V1 = 6208 on the random rank-13
tensor, bound min(n1, n23) = 10296, so not saturated; the SATPROBE of the normal run had given 3359 at r = 11).  Two
gaps showed: (1) a finished profile(r) was not stored -- the matrix checkpoints are deleted once the rank is known, so
a restart during rank 14 would have evaluated rank 13 again (~28 h); (2) rank 14 is the last feasible rank under
WCAP 2^28 (word minors 2.1e8 at r = 14, 3.2e8 at r = 15), so resolve() evaluates only r = 13 and r = 14 and asks only
whether the rank at 14 exceeds 6208.  Changes in rankscan.py:
* Direction.profile writes each finished profile to <CKPT>/<points/tensor hash>_prof[_<fillings hash> if g > 1]
  [_c<cut>].json and returns it when the file exists; main() deletes these files once the component's record is
  written.
* resolve(), ends-first branch with adjacent ends (hi = rlo + 1) and g = 1: rank at hi is evaluated on the leading
  cut x cut block of F only (the first cut random evaluation points on each side), cut = rank at rlo + EXTRA.  Its rank
  is min(cut, rank F) -- the same argument as the EXTRA margin of the full N1 x K evaluation (generic points of the
  orbit of highest weight vectors, which spans the representation) -- so it is > rank at rlo exactly when the rank at
  hi is, at (cut / N1)^2 of the cost: 6216^2 / 10304^2 = 36 % for the hook.  The record gets 'cut': {r: cut}; the
  profile value there is min(cut, rank).  Env CUT=0 disables.  Checkpoints of a cut evaluation carry _c<cut>.
* test_cut.py: every adjacent pair of three g = 1 directions (4x4x4 d = 3, 5x5x5 d = 5, 6; MEMCAP 2^12, block mode)
  gives leading-block rank = min(cut, full rank) and the same decision (pairs with and without a rank increase);
  a cached profile is reused by a new Direction without any evaluation; resolve() with adjacent ends gives the same
  separations with and without the cut.  test_ckpt.py still passes.
The rank-13 result was written to its cache file from the worker's progress line (the reconstructed checkpoint hash
matched the worker's, n8_t0_r13_f0_34ad6c5b243bd45b); the worker (pid 462, 20 min into rank 14, no checkpoint yet)
was stopped and the runner restarted the component (worker 445078) with the new code.
Result (2026-10-22 06:48): rank 14 on the leading 6216 x 6216 block = 6208 = rank 13, so ((6,1),(2,1^5),(2,1^5))
does not separate 13 vs 14 (record: sep {}, unknown 14..23, 'cut': {14: 6216}).  The rank stands at 6208 for
r = 13, 14, far below the bound 10296: most likely its generic value (then nothing >= 13 is separated by it; r >= 15
is beyond WCAP).  Rank 14 took 10.5 h of evaluation (two sessions; the container restart of 01:20 resumed it from the
01:19 checkpoint at block 3066 of 6216, rank 13 from its cache file) instead of ~35 h for the full matrix.  Peak RSS
7.0 GB (estimate 6.5 GB).  The rerun continues with ((6,1),(2,2,1,1,1),(2,1^5)) and ((6,1),(3,1^4),(2,1^5)).

## Planned evaluation with reuse, cheaper evaluation basis, blocked RREF (adopted 2026-10-23 12:50)
From branch claude/project-thread-ttahoa-rankscan (commit b15eff6, based on this branch at 0f46ae8, after the float32
change; cherry-picked unchanged, details in SPEEDUP_rankscan.md): compute_F plans one contraction path of the whole
network and reuses the intermediates that depend only on the word minors or on one side's points across tiles
(NEWEVAL); each rank is evaluated in the cheapest of up to 1500 random fillings and mapped back exactly to the old
basis (Fs = A^-1 E mod p, so F_i, phi, H_k, V_k are bit-identical; FILLPOOL); a blocked Gauss-Jordan replaces the
row-by-row one inside RREF, and V_1 is not eliminated again for g = 1 (= H_1); layout-aware pairwise contractions.
Their check: 40 scan components (3x3x3 .. 7x7x7, including the 4x4x4 rank-6 separators and the 6x6x6 rank-10
separator) give identical records, 2.4x faster overall (up to 9.5x), lower peaks.  Here: test_speedup.py 33 ok,
test_cut.py and test_ckpt.py pass.  Checkpoints stay compatible both ways (old Y-major format; a rank with an old
filling's checkpoint is finished with the old fillings), profile caches keep their names.  Running workers keep the
module they started with; every worker started since the cherry-pick uses it.  The runner's memory estimates are
unchanged (conservative: the peaks went down).

## Float32 matrices (2026-10-23 04:58; idea from the combined agents' float32 RREF storage)
Checked at the user's request: the method changes of the other agents since 2026-10-21 (branches charming-heisenberg,
tender-ride, zealous-mendel): (a) hwv_fast.minors_of_points over the C(n, l) row subsets by Leibniz (l! terms): not
needed here -- rankscan.py has computed both minors by Laplace recursion since its first version (2026-10-04; cost
~ sum_k k C(n, k) per point or per vector tuple), which also handles l = 8..10; (b) isoflat.modrank as a blocked LU: rankscan.py uses
its own incremental float64-BLAS RREF; (c) sweep_fast.py streaming of the g flattenings (noV mode only) and (d) the
combined agent's float32 storage of RREF bases: adopted in spirit.  Residues mod p = 524287 < 2^24 are exact in
float32; every product is still formed in float64 (fmatmul), so the arithmetic is unchanged.  rankscan.py now
* evaluates each flattening directly into a float32 slot of Fs (compute_F(dest=...)): no float64 F per filling;
  checkpoints are written in float32, and float64 checkpoints of older workers are resumed into the float32 slot;
* frees the word minors before the elimination;
* builds phi_j = sum_i C_ji F_i on row chunks in float64 and stores it as float32 (before: float64 plus two
  full-size temporaries);
* stores the RREF basis blocks as float32.
Checks: profiles identical old vs new on 6x6x6 d = 6 ((3,2,1),(3,2,1),(3,1,1,1)) g = 4, d = 7 ((3,2,1,1)^3) g = 8 and
((4,2,1),(4,1,1,1),(2,2,2,1)) g = 2 (direction 1, r = 10, all H_k and V_k); block mode with MEMCAP 2^12 into a
float32 dest equals the float64 matrix; an old float64 checkpoint (interrupted old worker) resumed by the new code
gives the same matrix and profile (4x4x4 d = 6 g = 4, 5x5x5 d = 6 g = 1); test_cut.py, test_ckpt.py pass.  Peak RSS
of ((3,2,1,1)^3) direction 1: 1192 -> 1016 MB (its peak is in the evaluation phase).  The big savings are expected
where the elimination dominates: 7x7x7 ((4,2,1),(4,2,1),(3,1,1,1,1)) g = 3 (V basis 22058^2: 3.7 -> 1.9 GB, phi
3 x 1.2 GB -> 0.6 GB; recorded peak 7.65 GB) and 9x9x9 ((3,2,1),(3,1,1,1),(3,1,1,1)) (9.2 GB).
scan_runner.py: mat_parts(old=False) = 4 g N1 K and 4 (N1 K + N1^2 + K^2) for workers started since F32_SINCE
(2026-10-23 04:58:04); the estimates drop from 8.4 to 5.7 GB (7x7x7 above) and 9.7 to 6.4 GB (9x9x9).  They are used
only when <SCAN>/f32model contains 1 -- off until a large component has run on the new code and its recorded peak
confirms them (until then every estimate is the float64 one).  Runner restarted 05:21 (workers adopted).
Switched on 10:01 (a 6x6x6 backfill had taken the slot of the waiting 8.4 GB 7x7x7 component again; the old-code
workers keep their float64 estimates).  Validation on 9x9x9 d = 6 ((3,2,1),(3,1,1,1),(3,1,1,1)), g = 2, direction 1
N1 = 11096, K = 22184 (the component whose float64 run had peaked at 9218 MB): float32 run started 10:01 at an
estimate of 6.2 GB (6349 MB), both flattenings evaluated by 11:20, elimination 11:17-12:00 with RSS rising from 2.3
to 5.6 GB; peak (VmHWM) 5734 MB, 0.6 GB below the estimate and 38 % below the float64 peak.

## 6x6x6, rank 10 vs 11 at d = 8: the two separators, rechecked (2026-10-22)
Components ((5,3),(3,2,1,1,1),nu) with nu = (2,2,1,1,1,1) (dims 4410 x 384 x 15) and nu = (3,1,1,1,1,1) (4410 x 384 x
21), g = 2 for both (found 2026-10-12 and 2026-10-18; d <= 7 has no separator of 10 vs 11).  Direction 1 (source
S^{53}V^*): F_u : S^{53}V^* -> S^{32111}V (x) S^nu V for u in the 2-dim multiplicity space M; the separating
configuration is H2 = [F_u1 | F_u2] : S^{53}V^* -> M^* (x) S^{32111}V (x) S^nu V (U = M), 4410 x 2 n23.  Directions
2 and 3 (sources of dim 384 and 15 / 21) are at their bounds from r = 10 on.  Ranks (H1 = V1, H2, V2):
| r | 9 | 10 | 11 | 12 | 14 = r_gen |
|---|---|---|---|---|---|
| H1 | 2322 | 2700 | 2700 | 2700 | 2700 |
| H2 | 2517 | **2775** | **2835** | 2835 | 2835 |
| V2 | 2598 | 2880 | 2880 | 2880 | 2880 |
(bounds: H 4410, V2 min(8820, n23) = 5760 / 8064).  Both components have the same numbers in every entry.  r = 10, 11,
12, 14 from the scan (seed 5); recheck_sep.py with seeds 6 and 7 (other random tensors, evaluation points,
fillings and generic U; logs scan/recheck_n6_d8_A.log, _B.log, 7 to 20 min per rank) reproduces r = 10, 11 exactly
for both components and gives r = 9.  So H2 reaches its generic value 2835 at r = 11 and separates exactly 10 vs 11;
one functional (H1) separates 9 vs 10 but not 10 vs 11, and V2 is constant from r = 10 on.  S^{221111} = det (x)
Lambda^2 and S^{311111} = det (x) S^2, which differ only in the C-factor after the determinant twist, and the profiles
coincide; whether that has a structural reason is open.

## Saturation certificates in the report (2026-10-07)
A component whose every direction is at its rank bounds (H_k = min(n1, k n23), V_k = min(k n1, n23) for all k) at
rank s has equal flattening ranks for all r >= s, so it separates no rank >= s.  scan_report.py now counts these ranks
as resolved even when the record was run for fewer ranks: the WCAP reruns n8_d6_x1 (asked only for r = 12; all five
components saturated at r = 12) complete 8x8x8 d = 6 for r = 13, and the wedge records n10_d5_w1/w2 (((5),(1^5),(1^5))
at its bounds 2002 and 252 from r = 14) complete 10x10x10 d = 5 for r = 15.  For records without a stored 'sat_from'
(closed-form families) the saturation rank is read off the profile and the matrix dimensions.

## Correction (2026-10-05): no component ever reached the time limit
Up to 2026-10-05 03:40 the runner's time-limit check measured every claim file of a live worker, including the
claims of components that worker had finished hours before; all nine 'TIMEOUT' lines in the runner log were such
finished components (each has a result), and each stop killed the worker in the middle of its current component,
which was then redone.  Fixed: only a worker's newest claim without a result is timed.  The false entries were
removed from state.json.

Restart after a container loss: `cd isotypic_flattenings; pip install numpy sympy opt_einsum; mkdir -p scan/live; cp -r scan/state.json scan/res scan/jobs scan/logs scan/runner.log scan/monitor.log scan/live/;
setsid nohup python3 -u scan_runner.py >> scan/live/runner.log 2>&1 < /dev/null &; setsid nohup ./scan_autosave.sh >> scan/live/autosave.log 2>&1 < /dev/null &` (continues from scan/state.json and
the result files; components without a result are redone).
