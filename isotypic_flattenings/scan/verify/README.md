# Verified separators (verify_scan.py: fresh tensors, points, fillings and subspaces U_k; second prime)

| format | d | component | g | dims | config | rank r / r+1 | checks |
|---|---|---|---|---|---|---|---|
| 4x4x4 | 8 | ((5,1,1,1),(3,2,2,1),(3,2,2,1)) | 5 | 35, 15, 15 | 1V5: U (x) S^{5111}V^* -> S^{3221}V (x) S^{3221}V, U = whole multiplicity space (k <= 4: 137/137) | 6 vs 7: 146 / 147 (rank 5: 84, rank 8: 147) | seeds 5, 7, 11 (p = 524287), 13 (p = 524269): identical; n4_d8.log |
| 4x4x4 | 8 | ((5,3),(3,3,1,1),(3,3,1,1)) | 2 | 280, 20, 20 | 1V2: U (x) S^{53}V^* -> S^{3311}V (x) S^{3311}V, dim U = 2 (k = 1: 235/235) | 6 vs 7: 252 / 254 (rank 5: 124, rank 8: 254) | same |
| 4x4x4 | 8 | ((6,2),(3,2,2,1),(3,2,2,1)) | 4 | 360, 15, 15 | 1H2-4 (known, d7d8 agent) | 6 vs 7: 304 / 309 | same |
| 4x4x4 | 8 | ((5,3),(5,1,1,1),(5,1,1,1)) | 2 | 280, 35, 35 | 1V2 (k = 1: 235/235) | 6 vs 7: 252 / 254 | seeds 7, 11 (p = 524287), 13 (p = 524269); n4_d8_more.log |
| 4x4x4 | 8 | ((4,2,2),(4,2,1,1),(3,3,1,1)) | 6 | 84, 45, 20 | 1V6 only (k <= 5: 420/420) | 6 vs 7: 460 / 462 | same |
| 4x4x4 | 8 | ((5,3),(5,1,1,1),(4,2,1,1)) | 3 | 280, 35, 45 | 1V2-3 (k = 1: 265/265) | 6 vs 7: 483 / 485 | same |
| 4x4x4 | 8 | ((5,3),(4,2,1,1),(3,3,1,1)) | 4 | 280, 45, 20 | 1V3-4 (k <= 2: equal) | 6 vs 7: 654 / 656 | same |

All V-type separators are new: the earlier sweeps used `noV` (no V-stacks), so V-type separators were never computed.
