# Task for a separate agent: isotypic flattenings at d = 9 on (C^4)^{(x)3}

## Goal
Decide whether some isotypic flattening in degree d = 9 separates a general tensor of rank 6 from a general
tensor (rank 7) in C^4 (x) C^4 (x) C^4. "Separates" means: the flattening has strictly smaller rank on random
rank-6 tensors than on random rank-7 tensors. Report every component checked, even negative ones.

## Code
Repository github.com/wajcha2/claude, branch `claude/wonderful-fermat-1v76ux`, directory `isotypic_flattenings/`.
Read `RESULTS.md`, `PROGRESS.md` and the docstrings first. Requirements: `pip install numpy sympy`.
Everything is exact modulo the prime p = 524287 (in `hwv.py`).

* `hwv.py` computes, for a component lam = (l1,l2,l3) of partitions of d (at most 4 rows), the flattening
  S^{l1}V^* -> S^{l2}V (x) S^{l3}V of the isotypic tensor by evaluating highest weight vectors
  (Hauenstein-Ikenmeyer-Landsberg style) on tensors given by a rank decomposition; no tensor power is ever formed.
* `sweep_hwv.py n d r_low,r_high seed slice nslices [noV]` runs all unordered components with nonzero Kronecker
  coefficient, all 3 flattening directions, a generic functional on the multiplicity space and (for multiplicity
  g >= 2) the stacked flattenings with U = whole multiplicity space. `noV` skips the expensive
  U^* (x) S^{l1}V^* -> ... stack. Env `CHUNK` (default 48) bounds memory; env `RESUME=log1:log2` skips components
  already present in those logs. Lines `*** SEPARATES` mark a hit; the last line prints `FOUND: [...]`.
* `specialU.py n d r_low,r_high` tests natural subspaces U of the multiplicity space (functionals vanishing on
  sigma_k, k<=6, and swap eigenspaces), `pencil.py` / `plane.py` search tensor-independent rank-drop loci on a
  random line / plane in P(U^*), `koszul.py` and `schur2.py` apply Koszul and degree-2 isotypic flattenings to the
  isotypic tensor. These are secondary; the sweep is the priority.

## What to run
1. Sanity check (1 minute):  `python3 sweep_hwv.py 4 4 6,7`  must report full ranks and `FOUND: []`
   (compare with `hwv4_d4.log`), and `python3 test_hwv.py 3 5 4,5 "((3,2),(3,1,1),(2,2,1))"` must show 12 vs 15.
2. d = 9 sweep. There are 782 components; Weyl-module dimensions go up to 540 and Kronecker coefficients up to ~30,
   so the biggest components cost hours each. Run
       CHUNK=32 python3 sweep_hwv.py 4 9 6,7 5 <k> <N> noV > hwv4_d9_s<k>.log
   for k = 0..N-1 with N = number of cores minus one. Prefer processing cheap components first: add a filter
   (e.g. skip components whose largest dimension exceeds a bound, raising the bound in later passes) and say in
   the log which bound was used. Use `RESUME` to restart after a crash.
3. Memory: the container may have a cgroup limit far below `free`; processes get OOM-killed silently. Keep
   CHUNK small, do not run more processes than cores, and check `dmesg | grep -i oom` when a process disappears.
4. Commit and push the logs and a short summary table (component, dims, g, ranks low/high) every 30-60 minutes,
   so partial progress survives. Record explicitly which components were NOT checked.

## Reporting
Report (a) the list of components checked with their ranks, (b) any `SEPARATES` line with the full ranks of both
classes verified on a second pair of random tensors and a second prime if possible, (c) components skipped and
why, (d) total compute time. A negative result is a result: state it as "no isotypic flattening in degree 9 among
the checked components separates rank 6 from rank 7".
