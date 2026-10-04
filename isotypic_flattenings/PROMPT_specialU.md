# Task for a separate agent: special subspaces U of the Kronecker (multiplicity) space

## Goal
For T in C^n (x) C^n (x) C^n, an isotypic component lam = (l1, l2, l3) of degree d with Kronecker coefficient g gives,
for every subspace U of the g-dimensional multiplicity space M^*, stacked flattenings
  H_U : S^{l1}V^* -> U^* (x) S^{l2}V (x) S^{l3}V   and   V_U : U (x) S^{l1}V^* -> S^{l2}V (x) S^{l3}V
(and the same with the roles of the three factors permuted: "directions" 1, 2, 3).  U *separates rank r from r+1*
if the flattening has smaller rank on a general rank-r tensor than on a general rank-(r+1) tensor.

A running scan (`rankscan.py`, `scan_runner.py`, method in `SCAN.md`) tests **generic** U only: for each k = 1..g a
random k-dimensional U (one random flag U_1 < ... < U_g) plus U = M^*, both H and V, for n = 3..10, d up to 10.
Its results: `scan/STATUS.md` (per format and rank: lowest separating degree and all separators there),
`scan/summary.json`, raw per-component records `scan/res/*.jsonl` (rank profiles of every H_k, V_k at the
evaluated tensor ranks).  A *special* U can give a lower rank on sigma_r than a generic one and so separate where no
generic U does.  Your task: find out whether special subspaces separate ranks that generic ones do not, in a lower
degree than the scan's lowest degree, or ranks the scan has not separated at all.  Report every case checked,
negative ones included.  Only components with g >= 2 matter (for g = 1 there is no choice of U).

Two families of special U to study (the user's suggestion; both have worked before, see "Known facts"):

### A. Rank-drop loci
For a tensor T, the set D_T = {phi in P(M^*) : rank F_phi(T) < generic rank} is a determinantal variety.  Its
**tensor-independent** part (common to independent random tensors of rank r) is a candidate set of special U: a
point phi on it with rank F_phi(T_r) < rank F_phi(T_{r+1}) separates (k = 1).  Also try k >= 2: U spanned by
several such points, or the linear span of a tensor-independent component, with H_U and V_U.
* Lines in P(M^*) (`pencil.py`): drop points = roots of the gcd of maximal minors of F_0 + t F_1, gcd over two
  independent rank-r tensors.  Complete for g = 2.  Planes (`plane.py`): drop curves, their common components and
  intersections; complete for g = 3.  For g >= 4 a line or plane through the generic point sees only loci of
  codimension <= 1 or 2 -- also try lines through special points already found, and lines inside natural
  subspaces (B).
* The old code computes minors with a Python determinant loop and sympy polynomials -- fine for 300 x 300, not for
  the 1000-5000 sized matrices now common.  Suggested: project to a rho x rho pencil R (F_0 + t F_1) S with random
  R, S (rho = generic rank); drop points = roots of det(A + t B) = eigenvalues of -B^{-1} A, i.e. the characteristic
  polynomial mod p (Hessenberg reduction, O(rho^3) with numpy, exact mod p); take the gcd over two projections and
  two tensors; rational roots by gcd with t^p - t (polynomial powering mod h) and equal-degree splitting.
  Drop points are algebraic numbers: if a common factor has no roots in F_p, try other primes or work in F_{p^k}
  (a separating point over F_{p^k} is as good, the ranks are field-independent for a generic choice).

### B. Spaces of equations of low secants
U_k = {phi in M^* : phi(iso_lam(T^{(x)d})) = 0 for every T of rank <= k} -- the highest weight vectors of the
component that vanish on sigma_k (a flag M^* = U_0 > U_1 > U_2 > ...; U_k = 0 for k >= d since the ideal of
sigma_k is zero in degree <= k).  Test for each k, both H and V and every direction: a generic element of U_k,
U = U_k itself, and generic subspaces of U_k of every dimension; also U_k intersected with the swap eigenspaces
when two partitions of lam are equal (`specialU.py` has both, for n = 4, generic element + full U only).
U_k is computed exactly by evaluating the basis functionals on several random rank-k tensors at random probe
points and taking the null space (the probe must have at least g + 8 independent conditions).
Natural follow-ups: sums U_k + (generic vectors), differences between consecutive members of the flag.

## Where to look (from the scan, see scan/STATUS.md for the current state)
1. **Positive controls first** (must be reproduced before anything else):
   * C^3, d = 6, ((4,2),(3,2,1),(3,2,1)), g = 3, direction 1, rank 4 vs 5: generic U gives 27/27; on a random plane
     the rank-4 drop locus is a tensor-independent curve of degree 10 and at its rational points the ranks are
     26 (rank 4) vs 27 (rank 5) (`plane.py`, PROGRESS.md).
   * C^4, d = 8, ((6,2),(3,2,2,1),(3,2,2,1)), g = 4, direction 1, rank 6 vs 7: a special 1-dim U separates
     220 vs 225 (generic 1-dim U: 225/225; generic dim >= 2: 304/309): on a random line the rank-6 drop locus has
     degree 146 and is entirely tensor-independent (`hit_d8_special.py`, `pencil.py`, PROGRESS.md).
2. **Can a special U lower the lowest separating degree?**  For each format and rank r with lowest degree d_min(r)
   in the scan, check the g >= 2 components of degrees < d_min(r).  Best first targets:
   * 4x4x4, rank 6 vs 7: generic U first separates at d = 8 (8 separators, scan/verify/README.md); nothing at d = 7
     for any generic U, H or V.  Earlier agents found no special U at d = 5, 6 (lines, g = 2; planes, g >= 3) and
     no natural U (U_k flag, swaps; generic element + full U, H only) at d = 6, 7.  **Rank-drop loci at d = 7 and
     the full U_k analysis (subspaces, V stacks) at d = 6, 7 are open.**
   * 5x5x5: rank 8 first at d = 6 (one separator), rank 7 first at d = 5 -> check d = 5 (resp. d <= 4) components.
   * 6x6x6 to 10x10x10: ranks n+1, n+2, ... first at d = 3, 4, 5 -> check the degree below.
3. **Ranks the scan does not separate** (frontier, growing as the scan runs): 6x6x6 rank 10 vs 11 (nothing for
   generic U at d <= 6, d = 7 nearly done), 7x7x7 rank 12 (d <= 5, d = 6 nearly done), 8x8x8 rank 12 (d <= 5),
   9x9x9 rank 13 and 10x10x10 rank 13 (d <= 4).  5x5x5 rank 9 vs 10 is handled by another agent at d = 13, 14
   (agents/d13.md): do not spend much on it, a cheap check of special U at d <= 8 is welcome.
Promising components: g >= 2 with moderate matrix sizes; the scan records tell which flattenings are not
saturated (generic rank below min of the dimensions) on sigma_{r+1}, i.e. where a drop on sigma_r is possible.

## Code to reuse
* `rankscan.py` (scan evaluator; read its docstring): class `Direction(n, lam, g, t, crng, vecs, rmax)` chooses g
  fillings with independent functionals and holds the evaluation points; `compute_F(f, vm, pm, path, info)` gives the
  flattening matrix of one filling (exact mod p = 524287, block splitting under MEMCAP, raises `Infeasible`);
  `vector_minors` / `point_minors` (Laplace recursion, needed for n >= 6); `RREF` (exact incremental rank, float64
  BLAS) and `prefix_ranks` for nested stacks; `word_minor_size` for feasibility (an evaluation at rank r is only
  possible if C(n, ell) r^ell <= 2^26 for every column length ell).  Write your own driver; to test a special U
  with basis B (k x g), form phi_j = sum_i B[j, i] F_i from the g filling matrices F_i of one tensor and feed H/V
  stacks to `RREF`.  **Compute the F_i once per (component, direction, tensor) and reuse them for all candidate U.**
  Sampling sizes as in `Direction`: N1 = min(n1, g n23) + 8 source points, K = min(g n1, n23) + 8 target points.
* `pencil.py`, `plane.py`, `specialU.py` (old, n = 4 era, slow evaluator): algorithms to port, not to run as is.
* `verify_scan.py`: re-evaluates a component with fresh tensors, points and fillings, optionally another prime
  (`PRIME=524269`); extend it to special U for verification.

## Verification of a hit
Re-derive the special U from fresh independent tensors (it must be tensor-independent), then evaluate the ranks on
fresh tensors of rank r and r+1, with two seeds and the second prime 524269.  Report component, direction, type of U
(drop point / U_k / swap / ...), dim U, H or V, ranks on rank r-1, r, r+1, r+2 tensors, and the generic-U ranks of the
same flattening for comparison.

## Workspace, coordination, resources
* Same repository and directory: `isotypic_flattenings/`, branch `claude/trusting-bohr-hdnmbv` (unless told
  otherwise).  Put your code in new files (e.g. `specialscan.py`), your results under `special/`
  (`special/RESULTS.md`: one table of checked (format, d, component, direction, method) with outcome; hits first),
  your status in `agents/special.md` (running jobs, coverage, timings, peak memory, exact restart command).
  Messages to the scan agent: append to `agents/to-scan.md`.  Do not edit `rankscan.py`, `scan_runner.py`,
  `scan_report.py` or anything under `scan/`; improvements to shared code go in separate commits prefixed
  `[method]` and are described in your status file.
* The scan's autosave commits `isotypic_flattenings/scan` every 30 min and pushes.  If you work in the **same
  container**: never leave files staged (always `git add <your files> && git commit` in one command), skip git while
  `.git/index.lock` exists, and `git pull --rebase` before pushing.  In a **separate container**: `git pull --rebase`
  before every push; conflicts are impossible as long as you only touch your own files.
* CPU: the scan runs 4 worker processes (one BLAS thread each) on a 4-core machine.  In the same container, write a
  number into `isotypic_flattenings/scan/live/ncores` (e.g. `2`) to lower the scan's worker limit and free cores
  for yourself (it is read every few seconds; running components are not interrupted); restore 4 when you stop.
  Never run more processes than cores.  Use `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1`.  Memory: 15 GB total, the
  scan uses up to ~6 GB; keep each of your processes below ~2.5 GB (check `/proc/<pid>/status` VmHWM).
* Record time and peak memory per component (the user asked for this, to see problems early).
* Long runs: start with `setsid nohup ... &`, never block a turn, check in with a Monitor or scheduled wake-up,
  commit and push results at least hourly, report to the user only when something changed (new hit, a method
  finished on a format, a crash), in the form "for 6x6x6 with special U up to d = 6: rank 10 separated by ... /
  not separated (checked: ...)".
