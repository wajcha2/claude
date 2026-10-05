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
not yet separated in a lower degree.  4 worker processes (one BLAS thread each) take the runnable jobs in the order
(band, n): cheap bands first, small formats first.  A component running longer than the time limit is stopped and listed as
not checked (time limit; 4 h since 2026-10-04 17:00, adjustable at run time in scan/live/tlimit, the worker limit in
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

## Correction (2026-10-05): no component ever reached the time limit
Up to 2026-10-05 03:40 the runner's time-limit check measured every claim file of a live worker, including the
claims of components that worker had finished hours before; all nine 'TIMEOUT' lines in the runner log were such
finished components (each has a result), and each stop killed the worker in the middle of its current component,
which was then redone.  Fixed: only a worker's newest claim without a result is timed.  The false entries were
removed from state.json.

Restart after a container loss: `cd isotypic_flattenings; pip install numpy sympy opt_einsum; mkdir -p scan/live; cp -r scan/state.json scan/res scan/jobs scan/logs scan/runner.log scan/monitor.log scan/live/;
setsid nohup python3 -u scan_runner.py >> scan/live/runner.log 2>&1 < /dev/null &; setsid nohup ./scan_autosave.sh >> scan/live/autosave.log 2>&1 < /dev/null &` (continues from scan/state.json and
the result files; components without a result are redone).
