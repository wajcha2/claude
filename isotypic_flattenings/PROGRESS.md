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
- Verification with the second prime 524269 (fresh tensors, seed 7): ((3,1,1),(2,2,1),(2,2,1)) key (wedge 2nd factor, unswapped, p=2, m=8):
  rank 5: 692, rank 6: 996, rank 7: 1008, rank 8: 1008.  ((3,1,1,1),(2,2,2),(2,2,2)) p=1 (m=12): 48 / 118 / 120 / 120; p=2 (m=11): 215 / 520 / 550 / 550.
  So the Koszul rank at the generic value 1008 (resp. 120) is reached exactly at rank 7 = generic rank; the drop at rank 6 is 12 (resp. 2).
- 2026-11-01: Koszul pass C^4 d=4 complete (15/15 components): no separation, so d=5 is the lowest degree at which Koszul
  flattenings of the isotypic tensor separate rank 6 from 7 in (C^4)^{(x)3} (d=2,3 also complete, none).
- Koszul pass C^5 (rank 9 vs 10): d=4 complete (15 components), d=5 complete (40 components incl. size-skipped ones), no separation; d=6 running, d=7 started.
- Koszul pass C^5 d=6 complete (122 components incl. size-skipped), no separation of rank 9 from 10. d=7 running (89 so far, none).
  Koszul pass C^4 d=7 resumed (113/195 done before the restart, none).
- 2026-11-01 17:10 UTC: new check started — Koszul flattenings of the *stacked* isotypic tensor (U = full multiplicity
  space M_lambda, g >= 2), script koszul_stack.py: wedge the stacked factor (W) or a plain factor with U on the source (V)
  or target (H) side, p = 1, 2, both orders of the remaining factors. The earlier Koszul passes used a generic 1-dim U only.
  No g >= 2 components exist for d <= 4; C^5 d = 5 (2 components), 6 (24), 7 (121) queued, logs live/kstack5_d*.log.
- 2026-11-01 17:35 UTC: Koszul pass C^4 (rank 6 vs 7) d=7 COMPLETE: 195/195 components, no Koszul separation at d=7
  (the Koszul separators remain the d=5 and d=6 ones). C^5 d=8 V-stack sweep: worker 0 finished (FOUND: []), worker 1 on
  its last component (151/152 done, none). Koszul C^5 d=7: 138/297 lines so far (112 of them size-skipped), none.
  Stacked-U Koszul C^5 d=5: ((3,1,1),(3,1,1),(2,2,1)) g=2 all stacked ranks equal for ranks 9/9/10 (none); the other
  g=2 component ((3,2),(3,1,1),(3,1,1)) deferred (size). Started generic Koszul C^5 d=8 (2 workers, maxprod 3e6:
  180 of 729 components fit), logs live/koszul5_d8_w{0,1}.log.
- Grid-cap experiment (GCAP: sample only GCAP orbit points per factor = quotient of Y to C^GCAP per factor): on the
  C^4 d=5 Koszul hit ((3,1,1),(2,2,1),(2,2,1)) dims (36,20,20), GCAP=12 destroys the separation (all ranks equal 144/660),
  so sub-sampled quotients are too lossy to cover the large components cheaply.
- 2026-11-01 17:35 UTC: KWEDGE mode validated — per wedged factor f the grid samples only m_f orbit points of that factor
  (m_f = the projection dimension the budget allows anyway) and keeps the other two factors full; on the C^4 d=5 hit it
  reproduces the full-grid ranks exactly (996 vs 1008 at p=2, SEPARATES [(1,0,2),(2,0,2)]). This makes the 187 large
  C^5 d=7 components (full grids 3e6..6e8 points) affordable: <= 1.1e7 points each, 6.7e8 in total per tensor.
  Started 2 KWEDGE workers on them (cost-sorted, MINPROD=3e6 so the generic pass's components are not repeated),
  logs live/koszul5_d7_kw_w{0,1}.log.
- 2026-11-01 18:03 UTC: projection-dimension sensitivity of the C^4 d=5 Koszul separator ((3,1,1),(2,2,1),(2,2,1)):
  forcing the wedged factor to m = 5, 6, 7 (KBUDGET 1e5, 2.6e5, 6.2e5) gives equal ranks for ranks 6 and 7 in all 12
  Koszul flattenings; the separation (996 vs 1008) needs m >= 8 at p = 2 (p = 1 never separates there). Consequence:
  the KWEDGE pass on the large C^5 d=7 components, which the KBUDGET=2e6 rank budget limits to m = 5, is too weak;
  it will be restarted with a larger budget (isoflat.modrank is already the blocked float64-BLAS elimination).
- 2026-11-01 18:08 UTC: KWEDGE workers restarted with KBUDGET=5e7 (rank budget; blocked modrank does a 4536 x 9912
  rank in ~60 s under load), fresh logs live/koszul5_d7_kw2_w{0,1}.log; the m=5 pass (3 components, none) discarded.
- 2026-11-01 18:13 UTC: **C^5 d=8 V-stack sweep COMPLETE**: all 152 components with g >= 2 and max dim <= 800 (list
  v5_d8.txt), generic U and full-U stacks in both orientations (H and V), ranks 9 vs 10: FOUND: [] — no separation.
  Snapshot hwv5_d8_V_done.log. The freed core goes to a third KWEDGE worker (queue re-split 3 ways, RESUME).
- 2026-11-01 19:40 UTC: scheduling fix — the kernel autogroup feature was ignoring the per-process nice levels
  (each nohup launch from a separate shell forms its own group with an equal CPU share), so the three KWEDGE workers
  were getting ~0.47 core each. Disabled autogroup for new tasks and set the d=8/stacked group's autogroup nice to 5;
  now generic d=7 ~1.0 core, KWEDGE ~0.77 core each, d=8 workers ~0.27, stacked ~0.1. Infrastructure note: when
  launching workers, prefer one shell for all, or set /proc/<pid>/autogroup nice for the whole group.
- 2026-11-02 01:10 UTC: **generic Koszul pass C^5 d=7 COMPLETE** (297 lines: 110 computed at KBUDGET=2e6,
  187 size-skipped and left to the KWEDGE pass, which is at 7/187), no separation. Caveat found today: with
  KBUDGET=2e6 the wedged factor is projected to m = 8 (p = 2) only when the two other factors have (dim+2) product
  <= 1275; larger components were tested at m = 5..7, which the C^4 d=5 separator shows can miss a separation. So the
  earlier Koszul passes (C^4 d=3,4 and C^5 d=5,6) are being REDONE with KBUDGET=5e7 (KWEDGE sampled grids), chain on
  the freed core: live/koszul4_d3_b5e7.log, koszul4_d4_b5e7.log, koszul5_d5_b5e7.log, koszul5_d6_b5e7.log.
- 2026-11-02 02:30 UTC: container restart (uptime reset) killed all workers; relaunched all seven with RESUME from the live logs
  (3 KWEDGE d=7, 2 generic d=8, stacked d=7, redo chain from C^4 d=4). Nothing lost beyond the partial components in flight.
- 2026-11-02 04:12 UTC: KBUDGET=5e7 KMAXM=12 redo of C^4 d=3 (5 components) and C^4 d=4 complete: no Koszul separation of
  rank 6 from 7 at d <= 4 even with projection dimension 12 (so d = 5 stays the lowest Koszul degree for C^4). C^5 d=5 redo running.
- 2026-11-03 01:34 UTC: container restart killed all workers again; relaunched all seven with RESUME (3 KWEDGE d=7 at 51/187,
  2 generic d=8, stacked d=7, redo chain from C^5 d=5 at 33/40). Only the components in flight were lost.
- 2026-11-03 06:16 UTC: container restart (third in 30 h) killed all workers; relaunched all seven with RESUME (KWEDGE d=7 at 60/187,
  redo chain at C^5 d=5 37/40, generic d=8 and stacked d=7 continuing). Only the components in flight were lost.

### 2026-11-07T21:41Z outage recovery
- The container was replaced several times between 2026-11-03 ~07:40 UTC and 2026-11-07 21:37 UTC; all seven workers were down for the whole
  gap (the disk, live/ logs and snapshots survived, no work lost beyond the components in progress at 07:40). No new separators anywhere.
- Relaunched with RESUME at 21:40 UTC from the Nov 3 state: KWEDGE C^5 d=7 62/187; generic C^5 d=8 662/729 (113 computed); stacked d=7
  partial; KBUDGET=5e7 KMAXM=12 redo C^5 d=5 38/40 then d=6 0/122.
- Other agents (status files pulled 21:39 UTC): d13 last update Nov 3 06:11 (no hits); d10 (C^4x5x5 rank 8 vs 9) resumed 2026-11-07 21:38,
  d=10 in progress, no hits; scan branch unchanged since Nov 3 07:21.

### 2026-11-07T23:02Z high-budget Koszul redo: C^5 d=5 complete
- KWEDGE Koszul, KBUDGET=5e7, KMAXM=12, rank 9 vs 10: all 40 components with g>0 done (koszul_b5e7_done.log), no separation at p=1,2 in
  any of the 3 wedge factors / both orders. The wedged factor was projected to m=12 in every case with dim > 12 (115 wedge settings),
  so this supersedes the KBUDGET=2e6 pass (m=5..7) for d=5. Lowest Koszul-of-isotypic degree for C^5 stays unknown (>= 6).
- The chain moved on to C^5 d=6 at 23:01 UTC: 113 components queued (costs 2.1e4 .. 4.3e6), live/koszul5_d6_b5e7.log.

### 2026-11-08T03:37Z check-in
- 7 workers running since the 21:40 relaunch, no separators. KWEDGE d=7 78/187, generic d=8 663/729 (114 computed), stacked d=7 10 computed, redo C^5 d=6 22/113.

### 2026-11-08T06:36Z check-in
- 7 workers running, no separators. KWEDGE d=7 87/187, generic d=8 665/729 (116 computed), stacked d=7 15 computed, redo C^5 d=6 30/113.

### 2026-11-08T09:37Z check-in
- 7 workers running, no separators. KWEDGE d=7 97/187, generic d=8 669/729 (120 computed), stacked d=7 19 computed, redo C^5 d=6 37/113.

### 2026-11-08T12:37Z check-in
- 7 workers running, no separators. KWEDGE d=7 105/187, generic d=8 674/729 (125 computed), stacked d=7 21 computed, redo C^5 d=6 44/113.

### 2026-11-08T15:36Z check-in
- 7 workers running, no separators. KWEDGE d=7 113/187, generic d=8 676/729 (127 computed), stacked d=7 23 computed, redo C^5 d=6 51/113.

### 2026-11-08T18:37Z check-in
- 7 workers running, no separators. KWEDGE d=7 122/187, generic d=8 680/729 (131 computed), stacked d=7 26 computed, redo C^5 d=6 55/113.

### 2026-11-08 coverage audit (what is really complete; corrections to earlier notes)
- Koszul C^4 d=7 (koszul4_d7_done.log): 170 components computed at KBUDGET=2e6, 25 size-skipped (dims >= 120x216x216), so the
  earlier "195/195 complete" meant "pass finished", not "all components computed". No separator among the 170.
- Stacked-U Koszul (koszul_stack.py, size cap 4e6): C^5 d=5 1 of 2 g>=2 components computed, d=6 6 of 24, d=7 27 of 115 so far;
  the rest are size-skipped. Earlier notes calling d=5, d=6 "complete" meant the run finished.
- Koszul-of-isotypic, C^5 rank 9 vs 10: d=4 15/15 (KBUDGET 2e6 only); d=5 40/40 at KBUDGET=5e7/KMAXM=12; d=6 high-budget redo running
  (old pass: 19 computed, 94 size-skipped); d=7: 110 generic (2e6) + KWEDGE high-budget 124/187; d=8: 132 computed of 729 (size cap 3e6).
- Classical isotypic flattenings, C^5 rank 9 vs 10 (counted from hwv5_*_done.log, live/v5_*.log and the classical ranks printed by the
  Koszul passes; g>=2 components: generic H_k/V_k for all k by the special-U agent, special/RESULTS.md, d=5,6,7,8 all 2/24/121/415):
  g=1 components (unique functional) covered: d=2 0/2, d=3 0/5, d=4 15/15, d=5 27/38, d=6 50/89, d=7 118/176, d=8 75/314, d=9 29/479,
  d=10 29/790; d=11..14 only the "promising" lists (48/104, 42/180, 114/255, 135/337). So no degree >= 5 is complete for g=1.
- Classical, C^4 rank 6 vs 7: d<=8 complete (all components; generic U of every dimension, H and V, by the n x n x n scan; generic+H by
  d7d8), d=9 782/782 (generic + H-stacks, no V-stacks; two g=1 separators), d=10 19/279 pass-1 components only.

### 2026-11-08T20:22Z C^5 rank 9 vs 10: classical isotypic flattenings now complete for d <= 7
- Gap-filler (sweep_fast.py, generic functional, p = 524287) on the 115 g=1 components that had no classical rank record
  (d=2: 2, d=3: 5, d=5: 11, d=6: 39, d=7: 58; lists gap5_d*.txt, snapshot hwv5_gap_done.log): all computed, FOUND: [] in every degree.
  Together with the special-U agent's generic H_k/V_k profiles of all g>=2 components (d=5..8) and the earlier sweeps, every
  component with g>0 of degree <= 7 has now been tested classically against rank 9 vs 10: no classical isotypic flattening of
  degree <= 7 separates rank 9 from rank 10 in (C^5)^{(x)3}. d=8 remains partial for g=1 (75 of 314 components).

### 2026-11-08T21:36Z check-in
- 7 workers running, no separators. KWEDGE d=7 128/187, generic d=8 682/729 (133 computed), stacked d=7 29 computed, redo C^5 d=6 60/113; classical gap-filler d<=7 complete (115/115, none).

### 2026-11-09T00:36Z check-in
- 7 workers running, no separators. KWEDGE d=7 134/187, generic d=8 684/729 (135 computed), stacked d=7 31 computed, redo C^5 d=6 65/113.

### 2026-11-09T00:54Z stacked-U Koszul C^5 d=7 finished
- koszul_stack.py (U = full multiplicity space, kinds W/V/H, p = 1,2, both orders, size cap 4e6), rank 9 vs 10: all 121 components
  with g >= 2 accounted for, 32 computed and 89 size-skipped, no separation (process exited 00:52 UTC after its last component).
  Stacked-U Koszul totals: d=5 1/2, d=6 6/24, d=7 32/121 computed, none; the skipped components need a KWEDGE-style sampled grid
  for the stacked tensor, which koszul_stack.py does not have.
- Freed core: high-budget redo (KWEDGE, KBUDGET=5e7, KMAXM=12) of the C^5 d=4 Koszul pass (15 components, previously only at
  KBUDGET=2e6), log live/koszul5_d4_b5e7.log.

### 2026-11-09T03:38Z check-in
- 7 processes running (6 long-running workers + d=4 redo, reniced 10 -> 5 at 03:19), no separators. KWEDGE d=7 139/187, generic d=8 691/729 (142 computed), redo C^5 d=6 70/113, redo C^5 d=4 3/15.

### 2026-11-09T06:37Z check-in
- 7 processes running, no separators. KWEDGE d=7 145/187, generic d=8 692/729 (143 computed), redo C^5 d=6 74/113, redo C^5 d=4 6/15.

### 2026-11-09T09:36Z check-in
- 7 processes running, no separators. KWEDGE d=7 150/187, generic d=8 692/729 (143 computed), redo C^5 d=6 78/113, redo C^5 d=4 7/15.

### 2026-11-09T12:37Z check-in
- 7 processes running, no separators. KWEDGE d=7 156/187, generic d=8 692/729 (143 computed), redo C^5 d=6 82/113, redo C^5 d=4 9/15.

### 2026-11-09T15:36Z check-in
- 7 processes running, no separators. KWEDGE d=7 161/187, generic d=8 693/729 (144 computed), redo C^5 d=6 85/113, redo C^5 d=4 11/15.

### 2026-11-09T18:36Z check-in
- 7 processes running, no separators. KWEDGE d=7 165/187, generic d=8 696/729 (147 computed), redo C^5 d=6 88/113, redo C^5 d=4 13/15.

### 2026-11-09 21:02 UTC — C^5 d=4 high-budget Koszul redo complete
- KBUDGET=5e7, KMAXM=12, KWEDGE sampled grids (m=12 on the wedged factor, p=1,2, all factor/swap choices): 15/15 components of S^4(C^5)^{\otimes 3} with g>0 checked for rank 9 vs 10, no separation (live/koszul5_d4_b5e7.log, merged into koszul_b5e7_done.log). Runtime 2026-11-09 00:58 to 21:02 UTC at nice 10/5.
- The high-budget redo chain is now complete and negative for C^4 d=3, C^4 d=4, C^5 d=4, C^5 d=5; C^5 d=6 is at 91/113. 6 worker processes remain (KWEDGE d=7 x3, generic d=8 x2, d=6 redo).

### 2026-11-09 21:06 UTC — classical gap-filler extended to d=8 (started)
- gap5_d8.txt: the 235 g=1 components of S^8(C^5)^{\otimes 3} that still have no classical isotypic-flattening record (314 g=1 components at d=8, 79 covered by hwv5_d8_*_done.log / Koszul passes; the earlier d=8 sweep ran with MAXDIM=800). sweep_fast.py (generic functional, noV, p = 524287, MAXFLOPS=5e12) on the freed core at nice 5, log live/gap5_d8.log, snapshot hwv5_gap8_done.log. Together with the special-U agent profiles of the 415 g>=2 components this will complete the classical test of rank 9 vs 10 at d=8.

### 2026-11-09T21:36Z check-in
- 7 processes running, no separators. KWEDGE d=7 168/187, generic d=8 698/729 (149 computed), redo C^5 d=6 91/113, classical gap-filler d=8 32/235.

### 2026-11-10T00:36Z check-in
- 7 processes running, no separators. KWEDGE d=7 172/187, generic d=8 699/729 (150 computed), redo C^5 d=6 94/113, classical gap-filler d=8 120/235.

### 2026-11-10 01:22 UTC — container replaced (uptime reset between 01:08 and 01:20 UTC); all 7 workers relaunched with RESUME
- Disk, live/ logs and snapshots persisted. Remaining after resume: KWEDGE d=7 14 components (2/6/6 per worker), generic d=8 30 (21/9), redo C^5 d=6 18, classical gap-filler d=8 103 (132 already done, half-done component resumed from its #partial line). Lost: only the components in progress at the restart (one per Koszul worker). Kernel autogroup disabled again.

### 2026-11-10T03:36Z check-in
- 7 processes running (relaunched 01:21 UTC after a container replacement), no separators. KWEDGE d=7 174/187, generic d=8 699/729 (150 computed), redo C^5 d=6 97/113, classical gap-filler d=8 180/235.

### 2026-11-10 03:44 UTC — second container replacement (uptime reset between 03:37 and 03:42 UTC); all 7 workers relaunched again with RESUME
- Nothing recorded was lost (counts unchanged since the 03:36 check-in: KWEDGE d=7 174/187, generic d=8 699/729, redo C^5 d=6 97/113, gap-filler d=8 180/235); only the components in progress are recomputed.

### 2026-11-10 06:17 UTC — classical gap-filler d=8 complete: classical isotypic flattenings for C^5 rank 9 vs 10 are complete and negative for d <= 8
- sweep_fast.py (generic functional, exact mod p = 524287, noV, MAXFLOPS=5e12) computed all 235 g=1 components of degree 8 that had no classical record: FOUND: [], no SEPARATES, no NOT CHECKED line (live/gap5_d8.log, snapshot hwv5_gap8_done.log; 2026-11-09 21:08 to 2026-11-10 06:1x UTC on one core at nice 5, resumed from the log after two container replacements).
- Together with the 79 g=1 components recorded earlier (hwv5_d8_*_done.log, Koszul passes) and the special-U agent's generic H_k/V_k profiles of all 415 g>=2 components at d=8 (special/RESULTS.md), every component with g>0 of degree <= 8 has now been tested classically: no classical isotypic flattening of degree <= 8 separates rank 9 from rank 10 in (C^5)^{(x)3}. g=1 coverage is now d<=8 complete; d=9 479 components (29 done), d=10 790 (29 done) remain partial.

### 2026-11-10 06:20 UTC — KWEDGE Koszul pass on the large C^5 d=8 components started
- koszul_fast.py 5 8 9,10 2e7 with KWEDGE=1 KBUDGET=5e7 MINPROD=3e6 (the same settings as the d=7 KWEDGE pass) on the 549 components the generic d=8 pass size-skipped: 514 to do in increasing cost order (costs 1.3e6 .. 2.0e7), 35 largest SKIPPED (size) at the 2e7 cap (dims (1155,1155,1155) and up). One worker at nice 5 on the core freed by the gap-filler, log live/koszul5_d8_kw2.log, merged into koszul5_d8_done.log by the snapshots; more workers will be added as the d=7/d=6 runs finish.

### 2026-11-10T06:37Z check-in
- 7 processes running, no separators. KWEDGE d=7 175/187, generic d=8 699/729 (150 computed), redo C^5 d=6 99/113, KWEDGE d=8 35/549 lines (0 computed).

### 2026-11-10T09:41Z check-in
- 7 processes running, no separators. KWEDGE d=7 177/187, generic d=8 703/729 (154 computed), redo C^5 d=6 102/113, KWEDGE d=8 36/549 lines (1 computed).

### 2026-11-10T12:37Z check-in
- 7 processes running, no separators. KWEDGE d=7 179/187, generic d=8 704/729 (155 computed), redo C^5 d=6 104/113, KWEDGE d=8 36/549 lines (1 computed).

### 2026-11-10T15:37Z check-in
- 7 processes running, no separators. KWEDGE d=7 181/187, generic d=8 706/729 (157 computed), redo C^5 d=6 107/113, KWEDGE d=8 36/549 lines (1 computed).

### 2026-11-10 17:27 UTC — KWEDGE d=8: dynamic claims added to koszul_fast.py, second worker started
- koszul_fast.py: optional CLAIMDIR (one file per component with the worker pid, `done` when finished; a claim whose pid is dead is taken over), so any number of workers can share a queue and be added or restarted without re-splitting; workers without CLAIMDIR behave as before. Tested on C^4 d=2 (claims, done-skip, stale takeover).
- KWEDGE d=7 worker 2 finished its share (kw2 183/187; workers 0 and 1 have 1 + 3 components left). Its core now runs a second KWEDGE d=8 worker (CLAIMDIR=claims5_kw8, log live/koszul5_d8_kw2_w1.log); the first d=8 worker (log live/koszul5_d8_kw2.log, no claims) is restarted with claims as soon as it finishes its current component.

### 2026-11-10T18:37Z check-in
- 7 processes running, no separators. KWEDGE d=7 184/187 (workers 0 and 2 finished, 3 components left on worker 1), generic d=8 710/729 (161 computed), redo C^5 d=6 109/113, KWEDGE d=8 37/549 keys (2 computed; 3 workers with claims since 18:33).

### 2026-11-10 21:14 UTC — C^5 d=6 high-budget Koszul redo complete
- KBUDGET=5e7, KMAXM=12, KWEDGE sampled grids: all 113 components of S^6(C^5)^{\otimes 3} with g>0 checked for rank 9 vs 10 (p=1,2, every factor/swap choice), no separation (live/koszul5_d6_b5e7.log, merged into koszul_b5e7_done.log; 2026-11-07 23:01 to 2026-11-10 21:1x UTC, resumed after three container replacements). The old 2e6 pass had computed only 19 of these 113.
- The high-budget redo chain is now complete and negative for C^4 d=3, C^4 d=4, C^5 d=4, C^5 d=5 and C^5 d=6. Koszul flattenings of the isotypic tensor therefore do not separate rank 9 from 10 in (C^5)^{(x)3} for d <= 6 (d=7: KWEDGE 185/187).
- The freed core runs a fourth KWEDGE d=8 worker (claims, log live/koszul5_d8_kw2_w3.log).

### 2026-11-10T21:37Z check-in
- 7 processes running, no separators. KWEDGE d=7 185/187 (last worker, 2 components left), generic d=8 712/729 (163 computed), KWEDGE d=8 39/549 keys (4 computed; 4 workers with claims).

### 2026-11-11T00:37Z check-in
- 7 processes running, no separators. KWEDGE d=7 186/187 (last worker, 1 component left), generic d=8 712/729 (163 computed), KWEDGE d=8 42/549 keys (7 computed; 4 workers with claims).

### 2026-11-11 01:33 UTC — KWEDGE Koszul pass C^5 d=7 complete
- All 187 large components of S^7(C^5)^{\otimes 3} (full grid product > 3e6) checked with KBUDGET=5e7 sampled grids (p=1,2, every factor/swap choice), rank 9 vs 10: no separation (live/koszul5_d7_kw2_w{0,1,2}.log, merged into koszul5_d7_done.log; started 2026-11-01, resumed after every container replacement). With the 110 small components of the generic 2e6 pass (live/koszul5_d7.log) every one of the 297 d=7 components with g>0 is covered.
- So Koszul flattenings of the isotypic tensor do not separate rank 9 from 10 in (C^5)^{(x)3} for any d <= 7 (d<=6 at high budget everywhere, d=7 high budget on the large components). The freed core runs a fifth KWEDGE d=8 worker (log live/koszul5_d8_kw2_w4.log).

### 2026-11-11 01:41 UTC — third container replacement (uptime reset between 01:34 and 01:39 UTC); all 7 workers relaunched
- Nothing recorded was lost (generic d=8 712/729 lines, 163 computed; KWEDGE d=8 43/549 keys, 8 computed). The five KWEDGE d=8 workers took over the claims of their dead predecessors automatically (CLAIMDIR); only the components in progress are recomputed.
