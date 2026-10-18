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

## Results so far (2026-10-04 23:10 UTC; details special/RESULTS.md) -- no separating special U anywhere
* 4x4x4 rank 6 vs 7 (lowest generic d = 8): d = 5, 6, 7 complete (all g >= 2 components, all directions):
  lines (+ linear components, recursion), U_k flag / swaps / intersections (H, V, all dims), lines through and inside
  natural U, plane resultants (codim 2; 94 of 96 g >= 3 directions, the 2 with rho = 224 running as 'planebig'),
  Grassmannian pencils H_k / V_k.  Tensor-independent drop loci are common at d = 7 (22 of 210 directions on lines:
  hyperplane arrangements; 12 directions with isolated codim-2 points), but every one lowers rank-6 and rank-7
  tensors by the same amount.
* 5x5x5: rank 8 at d = 5 and rank 9 at d = 5, 6: not separated (d = 5: both g = 2 components injective at every
  target rank, no drop point on P(M^*) = P^1; d = 6: drop points in 3 of 53 directions, equal on rank 9 and 10).
* 6x6x6 r = 10-13 at d = 5, 6; 7x7x7 r = 12-18, 8x8x8 r = 12-23, 9x9x9 r = 13-29, 10x10x10 r = 13-35 at d = 5:
  not separated; no tensor-independent drop point at all at the lowest frontier rank (the flattenings stay
  injective for every functional), natural U and Grassmannian pencils give the generic ranks.
* 2026-10-11 23:06 UTC: 6x6x6 d = 7 complete (122 components, 310 directions): not separated; tensor-independent
  drop points in 4 directions, equal at r = 10 and 14.  Last component ((4,2,1)^3) (g = 9, K = 22688): 16 h wall,
  peak 6.7 GB (13 natural-U orderings at ~45 min each, V_9 elimination; lines ~100 s each, Grassmannian pencils
  skipped by the size cap).  5x5x5 rank 9 d = 8: 958 of 1090 directions, not separated (drop points in 83
  directions, equal on 9 and 10).  7x7x7 d = 5, 6, 8x8x8 d = 5, 6, 9x9x9, 10x10x10 d = 5: not separated.
* Timings / memory: per direction up to 1 h (10x10x10 d = 5, rho = 4950: F 33 min, minpoly 32 min), peak 3.6 GB.

## Running jobs
* 4x4x4 rank 6 vs 7, d = 5, 6, 7, methods line flag pflag: done (`special/run4.sh`).
* `special_runner.py special/jobs.txt`: job list in priority order, one process per component, live output in the
  untracked special/live (res, logs, runner.log); slots in special/live/ncores (4), time limit special/live/tlimit
  (default 3 h; 24 h since 2026-10-08 09:15 (8x8x8 d=6 ((3,2,1)^3): ~1 h per V_5 elimination with K = 26888), 12 h since 2026-10-07 06:30, 8 h on 2026-10-06 after 8x8x8 d=6 ((4,2),(2,2,1,1),(2,2,1,1)) timed out: one F evaluation
  there takes ~1 h); memory guard: at most special/live/maxbig (2) jobs with max(N1, K) > 6000 or g N1 K > 5e7 at once,
  launches only while MemAvailable >= special/live/minfree (5000 MB); a restarted runner adopts the specialscan.py
  processes still running (counted as slots, not relaunched).  Job lines may start with KEY=VALUE environment
  tokens (MEMCAP, CACHE, CACHEMIN, ...); EXCLUSIVE=1 jobs run alone (the queue is drained when one comes first).
  2026-10-07 18:31: 6x6x6 d=7 ((4,2,1)^3) (g = 9, K = 22688: 2 GB per cached tensor + 4 GB V_9 elimination) was
  OOM-killed next to another big job; it ran alone with 2 cached tensors (EXCLUSIVE=1 CACHEMIN=2 CACHE=2) and
  finished 2026-10-11 22:58 (16 h).  8x8x8 d=6 ((3,2,1),(3,2,1),(2,1,1,1,1)) 12..15 done 2026-10-12 00:25
  (87 min, peak 4.7 GB): 8x8x8 d = 6 complete.  Now (ncores 4): the rest of 5x5x5 d = 8 rank 9 (50 components,
  126 directions on 2026-10-12 00:40; the last jobs of special/jobs.txt).  2026-10-12 18:16: 13 components left,
  all with mem_estimate_gb > 3 (actual peaks so far 60-75 % of the estimate), maxbig raised to 3 (19:47: 4).
  2026-10-13 06:25: tlimit 36 h (((5,2,1),(3,2,2,1),(3,2,2,1)) dir 1: g = 9, K = 12968, 20-80 min per filling
  evaluation with 4 jobs running); it finished 2026-10-13 12:52 (18 h, peak 2.9 GB, no hit).  The container was then
  reclaimed (the 30-min check-ins lapsed); restarted 2026-10-18 07:11 for the last component,
  ((5,2,1),(4,2,1,1),(4,2,1,1)) (2 directions; dir 1 filling evaluations checkpointed in special/live/fcache).
  2026-10-18 12:15: candidate (generic, not special U): this component, dir 1 (source S_521, g = 13, n1 = 1440,
  n23 = 202500), generic V-stack with U = M: 17280 on a rank-9 tensor vs 18205 on a rank-10 tensor (bound 18720).
  REFUTED 15:30 by fresh tensors (specialverify.py, each tensor in one process): seed 101 / p 524287 rank 9: 18205,
  rank 10: 18205; seed 202 / p 524269 rank 10: 18205.  Cause: the rank-9 tensor's filling matrices came from two
  processes (11 checkpoints of 2026-10-13, 2 evaluated 2026-10-18) that had chosen different fillings --
  rankscan.Direction's choice depends on PYTHONHASHSEED -- and checkpoint f11 duplicated f10 (12 x 1440 = 17280).
* Fix (commit [method] 40b1f61): specialscan.py / specialverify.py run with PYTHONHASHSEED=0 (re-exec; the runner
  sets it) and the checkpoint name contains a CRC of the chosen fillings.  9 earlier directions that may have
  resumed from another process's checkpoints (started more than once since checkpoints exist, 2026-10-07, F time
  > 60 s) are superseded (special/superseded.jsonl) and rerun: 5x5x5 d=8 ((5,2,1),(3,3,1,1),(2,2,2,1,1)),
  ((5,2,1),(4,2,2),(3,3,2)), ((6,1,1),(4,2,1,1),(3,2,2,1)) dir 1; 6x6x6 d=7 ((4,2,1),(3,1,1,1,1),(3,1,1,1,1)),
  ((4,2,1)^3), ((5,2),(3,1,1,1,1),(3,1,1,1,1)) dir 1; 8x8x8 d=6 ((4,2),(2,2,1,1),(2,2,1,1)),
  ((4,2),(3,1,1,1),(3,1,1,1)) dir 1, ((4,2),(4,1,1),(3,2,1)) dir 3.  Runs started before 2026-10-07 had no
  checkpoints; a direction evaluated in one process is consistent (the fillings only differ between processes).  `special/sync.sh` copies special/live into
  special/res, special/logs, regenerates special/RESULTS.md, commits and pushes.

## Restart
`cd isotypic_flattenings; pip install numpy sympy opt_einsum python-flint; echo 4 > special/live/ncores; ./special/start_runner.sh`
(if special/live is lost: `mkdir -p special/live/res special/live/logs; cp special/res/*.jsonl special/live/res/` first;
components/directions with a record for the same ranks and methods in special/live/res are skipped).
Filling-matrix evaluations longer than 60 s are checkpointed in special/live/fcache (deterministic in the seed;
removed when the direction is done), so a container restart only loses the work since the last evaluation.
Never kill with a `pkill -f` pattern that also occurs in the killing command line (it kills the shell).
