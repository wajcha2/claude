# Agent "special": special subspaces U of the multiplicity space (task: PROMPT_specialU.md)

Code: `specialscan.py` (docstring has the method), results `special/res/*.jsonl` (one record per component and
direction: every case checked, profiles, hits, wall/CPU/F time, peak RSS), logs `special/logs/*.log`, summary
`special/RESULTS.md`.  Runs in a separate container (4 cores, 15 GB, all of them used by this agent; the scan's
`scan/live/ncores` is not touched).

## Method (short)
* `line`: tensor-independent rank-drop points of one functional on random lines a + t b of P(M^*): minimal
  polynomial of the projected pencil (rho x rho, python-flint, exact mod p) for two rank-r tensors, gcd, factor;
  every irreducible factor tested over F_{p^e} on a third rank-r tensor (independence) and on the rank profile
  r_lo .. r_hi + 1 (ends + bisection).  Points of equal rank signature from g + 2 lines: if they span a proper
  subspace W (a linear drop component), U = W and W + generic are tested (H and V prefixes), and lines inside W are
  analysed again (depth 2).  For a rank range where no generic flattening separates (frontier), the generic rank is
  constant, so D_r is contained in D_{r_lo}: lines are derived at r_lo only.
* `flag`: U_k (functionals vanishing on sigma_k, k = 1..d-1), swap eigenspaces E+/E- (equal partitions), U_k cap E;
  ordered bases [random basis of W, generic completion] -> generic subspaces of W of every dim, W, W + generic;
  one flag-adapted basis.  H and V prefixes over the rank range.
* `pflag`: lines through a generic point of each natural W and lines inside W.
* `plane` (g >= 3, rho <= PLANEMAX = 160): isolated (codim-2) tensor-independent drop points on a random plane
  (all of P(M^*) for g = 3): for lines O + u (b + v c) through a fixed point O, r(v) = lc_u(h)^(2(rho-e))
  Res_u(P_1/h, P_2/h) (P_i = determinants of two random rho x rho projections, h = drop curve of degree e) has
  degree <= rho^2 - e^2 (isobaric weight), interpolated from that many exact samples (subproduct tree); the gcd over
  two tensors gives the lines through common isolated points, which are then analysed by the line method.  Cost
  ~ rho^5 (rho = 140: ~10 min per tensor).  First test: C^3 d=6 ((4,1,1),(3,2,1),(3,2,1)) g=4 (rank 4 vs 5, a
  degree already separated generically): a codim-2 drop locus with rank 9 on rank-4 vs 10 on rank-5 tensors
  (generic 10/10) -- invisible to lines and to the old plane.py (which only found drop curves).
* Note: specialU.py's swap action was the identity (it permuted filling, tensor and points together, which gives
  back the same functional); here tau acts as Phi_f -> Phi_{f o tau} (fillings exchanged), checked tau^2 = 1 and
  against the S^2 / Lambda^2 multiplicities of the character table.

## Positive controls (special/logs/controls.log): reproduced
* C^3 d=6 ((4,2),(3,2,1),(3,2,1)) dir 1, rank 4 vs 5: on every random line two rational drop points: 26/26/26 vs 27
  (separates; generic 27/27) and 18 vs 18.  Both drop components are LINES of P^2 (5 points on 5 lines span dim 2);
  U = the 26-line (dim 2): H 26 vs 27, V 26 vs 35 (generic V2 36/45).  Inside it a point with 18 vs 27.
* C^3 d=5 ((3,2),(3,1,1),(3,1,1)): drop point 9 vs 15 (as pencil.py, t = 2/3).
* C^4 d=8 ((6,2),(3,2,2,1),(3,2,2,1)) dir 1, rank 6 vs 7: drop points 220 vs 225 (rank 5: 105, rank 8: 225) and
  84/84; both components are HYPERPLANES of P^3; U = the 220-hyperplane (dim 3): H 285 vs 290, V 220 vs 225.

## Running jobs
* 4x4x4 rank 6 vs 7, d = 5, 6, 7, methods line flag pflag: `special/run4.sh` (done for d = 5, 6; d = 7 finishing).
* `special_runner.py special/jobs.txt` (job list in order; one process per component; slots in
  special/live/ncores, time limit special/live/tlimit (default 3 h); log special/runner.log).

## Restart
`cd isotypic_flattenings; pip install numpy sympy opt_einsum python-flint; mkdir -p special/live; echo 4 > special/live/ncores;
setsid nohup python3 -u special_runner.py special/jobs.txt >> special/runner.log 2>&1 < /dev/null &`
(components/directions with a record for the same ranks and methods in special/res/n<n>_d<d>*.jsonl are skipped).
Report: `python3 special_report.py` -> special/RESULTS.md.
