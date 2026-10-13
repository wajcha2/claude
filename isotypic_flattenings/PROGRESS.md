# Progress log (C^4 (x) C^4 (x) C^4, separate general rank 6 from general rank 7)

Scripts: sweep_hwv.py (generic functional + full-U stacked flattenings, all components),
pencil.py (tensor-independent rank-drop points on a random line in P(M*), complete for g=2),
specialU.py (natural U: secant-vanishing flag U_k and swap eigenspaces; dim 1 and stacked).

| d | components (g>0) | generic sweep | pencil/line special U | natural U (flag, swaps) |
|---|---|---|---|---|
| 2 | 2  | none | g=1 only | - |
| 3 | 5  | none | g=1 only | - |
| 4 | 15 | none | g=1 only | - |
| 5 | 37 | none (53 s) | 2 comps g=2: no drop points | pending |
| 6 | 92 | none (29 min) | 23 comps g>=2: drop loci exist but rank-7 drops equally at all rational points | all 92 comps x 3 dirs: U_1..U_6 flag and swap eigenspaces, dim-1 and stacked: no separation |
| 7 | 195 | 55/195 done, none (2-2.5 min per comp) | - | - |

C^3 check (rank 4 vs 5, d=5): pencil finds special point t=2/3 on ((3,2),(3,1,1),(3,1,1)) with ranks 9 vs 15
(generic phi gives 12 vs 15); natural-U search reproduces 12 vs 15 on U_1=U_2=M*, U_3 empty there.

## Special-U intersection search (plane.py, codim-2, complete for g=3)
- C^3 d=6, lam=((4,2),(3,2,1),(3,2,1)), g=3, direction 1: rank-4 drop locus is a T-independent curve of degree 10
  in P^2; at a rational point of it ranks are 26 (rank 4) vs 27 (rank 5) -- generic functional gives 27/27.
  => special U on a curve separate where generic ones do not (validation of the method).
- C^3 d=6, other g>=3 components ((4,1,1),(3,2,1),(3,2,1)) g=4 and ((3,2,1),(3,2,1),(3,2,1)) g=5: no drop locus on a random plane.
- C^4 d=6 components with g>=3: running (plane4_d6.log).
- C^4 d=6, all 5 components with g>=3 (g=3,3,4,4,5), all 3 directions: rank-6 tensors have NO drop locus on a random
  plane in P(K).  For g=3 this is the whole P(K): no functional at all lowers the rank for rank-6 tensors.
  For g=4,5 only special loci of codimension >=3 remain unexplored.

## d=7 and d=8 complete (fast implementation from the d9 agent, hwv_fast/sweep_fast)
- d=7: 195/195 components, generic functional + full-U stacked, 3 directions: NO separator.
- d=8: 426/426 components: ONE separator, lam=((6,2),(3,2,2,1),(3,2,2,1)), g=4, dims (360,15,15), direction 1:
  stacked flattening S^{(6,2)}V^* -> U^* (x) S^{3221}V (x) S^{3221}V with U = M (dim 4): rank 304 on rank-6 vs 309 on rank-7
  (rank 5: 160, rank 8: 309).  Generic 1-dim U gives 225/225 (full); any generic U of dim >= 2 gives 304/309.
  Verified with seeds 5, 7, 11, fresh draws and prime 524269 (verify_hit.py), reference implementation agrees.
  Natural subspaces: all functionals of this component vanish on sigma_3 (U_1=U_2=U_3=M), U_4=0; swap23 acts trivially.
- d=9 (d9 agent): two separating g=1 components, see agents/d9.md.
- d=8 hit, special 1-dim U (pencil.py on a random line of P(M^*), fast evaluator): the rank-6 drop locus has degree 146
  and is entirely tensor-independent; at the rational point t=509492 (filling-basis coordinates of hit_d8_special.py,
  seed 5) the flattening has rank 220 on rank-6 tensors vs 225 (full) on rank-7 tensors -> a special 1-dimensional U
  separates too (generic 1-dim U: 225/225). Another point (t=37168) lowers all tensors to 84.
- d=7 natural-U search (specialU4_d7.log): 430 direction cases evaluated, no separation.
- d=7 natural-U search complete (430 + 155 = 585 direction cases; specialU4_d7.log + specialU4_d7_rest.log): no separation.
- d=8 hit, plane (codim-2) analysis: timed out (drop-curve degree 146 needs ~66k determinants with the slow modular det);
  not pursued further since the line method already gives a separating 1-dim U.

## C^5 (rank 9 vs 10): d=8 promising list complete (33/33, 7087 s): no separator.  Full d=8 sweep (dim<=800): 37 done, none.
- C^5 d=9 promising list complete (49/49, 42663 s): no separator.  d=10: 37/55, d=11: 43/104, d=12: 27/180 so far, none.

## New directions (2026-09-27)
- Koszul flattenings of the generic isotypic tensor of the d=8 C^4 separator: equal ranks on rank 6 and 7 (615/615, 1365/1365,
  1575/1575, 840/840) -- the separation there needs U of dim >= 2, not Koszul.
- Running: Koszul (large projections, KBUDGET 1e7) + degree-2 isotypic flattenings on all C^4 components, d=5,6,7 (koszul_fast.py, live/koszul4_d*.log).
- Running: C^5 d=15, 21 components with two-row source and targets (4,3,3,3,2) [dim 24] / (3,3,3,3,3) [det^3] (prom5_d15_tiny.txt).

## 2026-10-13: Koszul flattenings of the isotypic tensor separate rank 6 from 7 in (C^4)^{(x)3} already at d = 5 and 6
(koszul_fast.py, KBUDGET 2e6, exact mod p, reproduced with seeds 61/101/202; see koszul4_d5_done.log, koszul4_d6_done.log)
- d=5, lam=((3,1,1),(2,2,1),(2,2,1)), g=1, dims (36,20,20): Koszul flattening with wedged factor = S^{221}V (2nd or 3rd module),
  other two factors in the order (S^{311}V, S^{221}V), p=2, random quotient to dim 8: rank 996 (rank-6 tensors) vs 1008 (rank 7).
  p=1 (m=17) and the swapped order do not separate; classical flattenings 36/20/20 on both.
  (This is the same component that separates rank 4 from 5 in C^3 by a classical flattening.)
- d=6, lam=((3,1,1,1),(2,2,2),(2,2,2)), g=1, dims (10,10,10) [S^2V(x)det, Lambda^2V^*(x)det^2 ...]: wedged factor = 2nd or 3rd
  module, unswapped, no projection (full factor + 2 overcomplete coordinates): p=1: 118 vs 120, p=2: 520 vs 550.
- Koszul pass coverage: d=5 36 components, d=6 all 92, d=7 113/195 (worker died at the container restart), no other hit.
- Classical isotypic flattenings need d=8 (stacked U) / d=9 (g=1); so Koszul of the isotypic tensor is a strictly better method at d<=7.
- Message from the n x n x n scan session (agents/to-all-Vstacks.md on branch claude/trusting-bohr-hdnmbv): at C^4 d=8, 7 of 8
  separating components are V-stacks (U on the source side), which my `noV` sweeps never computed for C^5. To be redone.
