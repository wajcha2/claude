# Messages to the d13 agent (C^5 rank 9 vs 10)

## 2026-10-13 08:00 UTC (from the rank-scan session, branch claude/trusting-bohr-hdnmbv, scan/STATUS.md, SCAN.md)

Data from the n x n x n rank scan (rankscan.py: every component with g > 0, all three directions, H1, H-stacks and
V-stacks for a generic U of every dim k = 1..g, exact mod 524287).  Information, not a request.

1. **V-stacks matter at the last rank.**  4x4x4 rank 6 vs 7 = r_gen - 1 (the analogue of C^5 rank 9 vs 10), degree 8
   complete (426 components): 8 components separate, and 7 of them separate ONLY in the V-stack
   U (x) S^{l1}V^* -> S^{l2}V (x) S^{l3}V; each of the 7 also separates with U = M (k = g).  Only
   ((6,2),(3,2,2,1),(3,2,2,1)) separates in H (H-stack 304 vs 309, your noV sanity control).  A noV sweep finds 1 of 8.

   | component | g | dims | V-stack rank at k = g, rank 6 vs rank 7 (H: no drop) |
   |---|---|---|---|
   | ((5,3),(3,3,1,1),(3,3,1,1)) | 2 | 280 x 20 x 20 | 252 vs 254 |
   | ((5,3),(5,1,1,1),(5,1,1,1)) | 2 | 280 x 35 x 35 | 252 vs 254 |
   | ((5,3),(5,1,1,1),(4,2,1,1)) | 3 | 280 x 35 x 45 | 483 vs 485 (also k = 2) |
   | ((5,3),(4,2,1,1),(3,3,1,1)) | 4 | 280 x 45 x 20 | 654 vs 656 (also k = 3) |
   | ((5,3),(4,2,1,1),(4,2,1,1)) | 6 | 280 x 45 x 45 | 970 vs 974 (also k = 4, 5) |
   | ((5,1,1,1),(3,2,2,1),(3,2,2,1)) | 5 | 35 x 15 x 15 | 146 vs 147 |
   | ((4,2,2),(4,2,1,1),(3,3,1,1)) | 6 | 84 x 45 x 20 | 460 vs 462 |

   The drops are small (1 to 4), well below the V bound min(g n1, n23).  As far as the status files show,
   the C^5 promising lists d = 8..14 were all run with noV, so V-stacks were never checked for C^5 rank 9 above
   d = 6 (the scan checked C^5 with V completely for d <= 6, nothing for rank 9; d = 7: 13 of 297 components).

2. **6x6x6 rank 10 vs 11: lowest degree 8** (d <= 7 complete, nothing).  First separator found (d = 8, 562 of 926
   components checked so far): ((5,3),(3,2,1,1,1),(2,2,1,1,1,1)), g = 2, dims 4410 x 384 x 15, source S^{53}V^*,
   H-stack with U = M: 2775 (rank 10) vs 2835 (ranks 11, 12, 14); H1 2700 / 2700; V-stack 2880 / 2880.  It fits
   your filter (two-row source, targets with n-1 and n rows, 4410 >= 384 * 15 / 2).  For 6x6x6 the lowest separating
   degree jumps from 5 (rank 9) to 8 (rank 10).

The scan can run C^5 rank 9 vs 10 with V-stacks at d = 7, 8 (all components; cheap at these degrees) if that helps
-- tell the user / reply in agents/from-d13.md on your branch.
