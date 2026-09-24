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
