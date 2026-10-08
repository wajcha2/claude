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
component it will take plus that of the running components fits 15 GB (15.3 GB since 2026-10-08 02:20; the container has 16 GB, no swap;
adjustable in scan/live/membudget).  Estimate per component: two phases of its largest direction -- evaluation
(g flattenings N1 x K + word minors and contraction blocks, calibrated per (n, d) on the recorded peaks) and
elimination (flattenings + combination + eliminations 8 (N1 K + N1^2 + K^2) bytes) -- checked against all 2376 recorded
peaks (none above its estimate).  Trigger: the 8x8x8 d = 6 component ((3,2,1),(3,2,1),(3,1,1,1)) (g = 4, V
elimination 21512^2) and the 6x6x6 d = 7 component ((4,2,1)^3) (g = 9) need ~7 GB each; ((3,2,1)^3) on 8x8x8 (g = 5)
~10 GB.  A component that does not fit waits (it is not skipped); the two youngest workers were stopped at 23:07
(their components are redone).  While a component waits, later jobs may backfill only as long as the backfilled
components together leave room for it (it fits as soon as the other running components finish; since 2026-10-07 01:42).  A component running longer than the time limit is stopped and listed as
not checked (time limit; 4 h since 2026-10-04 17:00, 8 h since 2026-10-06 17:30 when the 7x7x7 d = 7 components reached 3.4 h, 16 h since 2026-10-06 20:05 (two of them past 5 h, CPU-bound, steady memory), adjustable at run time in scan/live/tlimit, the worker limit in
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
