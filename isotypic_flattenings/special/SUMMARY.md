## Summary (curated; the tables below are generated)

**Question** (PROMPT_specialU.md): do *special* subspaces U of the multiplicity space separate tensor ranks that
generic U do not -- in a degree below the scan's lowest separating degree, or at ranks the scan has not separated?

**Answer so far: no.**  No special U separates a target rank in any case checked (hits: none).  Positive controls
reproduced first (special/logs/controls.log): C^3 d=6 ((4,2),(3,2,1),(3,2,1)) dir 1, rank 4 vs 5: drop point 26 vs
27 (generic 27/27); C^4 d=8 ((6,2),(3,2,2,1),(3,2,2,1)) dir 1, rank 6 vs 7: drop point 220 vs 225 (generic 225/225).

| format | target ranks | degrees checked with special U | methods | outcome |
|---|---|---|---|---|
| 4x4x4 | 6 vs 7 (generic: lowest d = 8) | 5, 6, 7 (all g >= 2 components, all directions) | line, linear components + recursion, U_k flag / swaps / intersections (H, V, all dims), lines through / inside natural U; plane resultants (codim 2) and Grassmannian pencils for all g >= 3 | not separated |
| 5x5x5 | 8 vs 9 (generic: d = 6) | 5 | all (g = 2: complete) | not separated |
| 5x5x5 | 9 vs 10 (d13 agent) | 5, 6, 7 (d = 8 queued) | line, flag, pflag, gline | not separated |
| 6x6x6 | 10..13 | 5, 6 | line, flag, pflag, gline | not separated |
| 7x7x7 | 12..18 | 5, 6 | line, flag, pflag, gline | not separated |
| 8x8x8 | 12..23 | 5 | line, flag, pflag | not separated |
| 9x9x9 | 13..29 | 5 | line, flag, pflag | not separated |
| 10x10x10 | 13..35 | 5 | line, flag, pflag | not separated |

Degrees "below the lowest separating degree" with g >= 2 exist only for 4x4x4 (rank 6: d = 5, 6, 7) and 5x5x5
(rank 8: d = 5); for 6x6x6..10x10x10 the ranks n+1.. are separated at d = 3, 4, 5, below which every Kronecker
coefficient is <= 1 (no choice of U).  So the lowest separating degrees of the scan stand for special U as well.

**What the special loci look like.**
* Tensor-independent rank-drop loci of one functional exist in many components (4x4x4 d = 7: 22 of 210 directions
  on random lines, isolated codim-2 points in 12 of 87 g >= 3 directions; 5x5x5 d = 6, 7 rank 9: a few directions),
  but at every one of them a rank-r and a rank-(r+1) tensor lose the same rank.  At the frontier (6x6x6 and up,
  d <= 6) there is no tensor-independent drop point at all at the lowest frontier rank: every functional (and every
  natural U) is injective there, as the generic one.
* The codim-1 drop loci found are unions of hyperplanes of P(M^*) (all drop points rational on every line, g + 2
  lines span hyperplanes), including in the positive controls: C^4 d = 8 has two drop hyperplanes (220 and 84), the
  220-hyperplane U (dim 3) itself separates (H 285 vs 290, V 220 vs 225), and inside the 84-hyperplane there are
  planes P with "P + generic vector" separating (H3 299 vs 304, 274 vs 279).  C^3 d = 6: two drop lines.
* The plane method (resultants on a pencil of lines) also finds codim-2 loci that lines cannot: e.g. C^3 d = 6
  ((4,1,1),(3,2,1),(3,2,1)) g = 4 has a codim-2 locus with rank 9 on rank-4 vs 10 on rank-5 tensors (generic 10/10;
  rank 4 vs 5 is already separated generically at d = 5, so this is not new for the scan).
* specialU.py's swap eigenspaces were vacuous (its tau was the identity); here tau acts by exchanging the fillings,
  checked against the S^2 / Lambda^2 multiplicities from the character table.

**Not covered:** codim >= 2 loci for g >= 4 beyond random planes (codim 2) and lines through natural points;
Grassmannian pencils of the largest stacks (size cap; 18 pencils in 7x7x7 d = 6); 6x6x6 d = 7, 8x8x8 d = 6
(running / queued); 7x7x7 d >= 7, 8x8x8..10x10x10 d >= 6 (7x7x7, 8x8x8 d = 6 partly).

