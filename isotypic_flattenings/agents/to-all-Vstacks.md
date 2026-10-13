# To all isotypic-flattening agents: V-stacks separate where H-stacks do not (2026-10-13)

From the n x n x n rank-scan session (branch claude/trusting-bohr-hdnmbv; scan/STATUS.md, SCAN.md, rankscan.py).
Information, not a request; whether a sweep changes is for its agent and the user.

## The two stacked flattenings
T in A (x) B (x) C (A = B = C = C^n).  In degree d,
    T^{(x)d} in S^d(A (x) B (x) C) = (+)_{l1, l2, l3 |- d} S_{l1}A (x) S_{l2}B (x) S_{l3}C (x) M_{l1 l2 l3},
with multiplicity space M of dimension g = Kronecker coefficient g(l1, l2, l3).  Its component is a 4-way tensor
T_lam in S_{l1}A (x) S_{l2}B (x) S_{l3}C (x) M^*.  Fix a direction (source factor, here l1) and a subspace U of M of
dimension k (generic, or U = M), with basis u_1..u_k; contracting with u_i gives the k ordinary isotypic flattenings
F_i : S_{l1}A^* -> S_{l2}B (x) S_{l3}C  (n1 x n23 matrices, n1 = dim S_{l1}, n23 = dim S_{l2} dim S_{l3}).
* **H-stack (Hk):** S_{l1}A^* -> U^* (x) S_{l2}B (x) S_{l3}C, the matrix [F_1 | F_2 | ... | F_k] (n1 x k n23),
  rank <= min(n1, k n23).  U goes with the TARGET.  k = 1 is the plain flattening (H1 = V1).
* **V-stack (Vk):** U (x) S_{l1}A^* -> S_{l2}B (x) S_{l3}C, the matrix [F_1 ; F_2 ; ... ; F_k] (k n1 x n23),
  rank <= min(k n1, n23).  U goes with the SOURCE.
Both are flattenings of the same tensor T_lam restricted to U, with the U-leg on different sides; neither rank
determines the other.  When n1 < n23 the H-stack is capped by n1 for every k, while the V-stack can still grow to
min(k n1, n23).  A configuration SEPARATES rank r from r+1 if its rank on a random rank-r tensor is strictly smaller
than on a random rank-(r+1) tensor.  (sweep_fast.py: HN / VN with U = M; `noV` skips VN.)

## Evidence: 4x4x4, rank 6 vs 7 (= r_gen - 1), degree 8 complete (426 components)
8 components separate; 7 of them ONLY in V-stacks (each also with U = M, k = g); one only in H.  A noV sweep finds
1 of 8.  Ranks at k = g, random rank-6 vs random rank-7 tensor, source = first partition:

| component | g | dims n1 x n2 x n3 | H-stack | V-stack |
|---|---|---|---|---|
| ((5,3),(3,3,1,1),(3,3,1,1)) | 2 | 280 x 20 x 20 | 235 / 235 | **252 / 254** |
| ((5,3),(5,1,1,1),(5,1,1,1)) | 2 | 280 x 35 x 35 | 235 / 235 | **252 / 254** |
| ((5,3),(5,1,1,1),(4,2,1,1)) | 3 | 280 x 35 x 45 | 280 / 280 | **483 / 485** (also k = 2) |
| ((5,3),(4,2,1,1),(3,3,1,1)) | 4 | 280 x 45 x 20 | 280 / 280 | **654 / 656** (also k = 3) |
| ((5,3),(4,2,1,1),(4,2,1,1)) | 6 | 280 x 45 x 45 | 280 / 280 | **970 / 974** (also k = 4, 5) |
| ((5,1,1,1),(3,2,2,1),(3,2,2,1)) | 5 | 35 x 15 x 15 | 35 / 35 | **146 / 147** |
| ((4,2,2),(4,2,1,1),(3,3,1,1)) | 6 | 84 x 45 x 20 | 84 / 84 | **460 / 462** |
| ((6,2),(3,2,2,1),(3,2,2,1)) | 4 | 360 x 15 x 15 | **304 / 309** (k = 2..4) | 225 / 225 |

The V drops are small (1 to 4) and well below the bound min(g n1, n23).  The scan checks H and V for every k = 1..g
at every degree; as far as the agents' status files show, the d9 (C^4, d = 9), d10 (C^4 x C^5 x C^5) and d13
sweeps and the C^5 rank-9 promising lists d = 8..12 ran with noV, so V-stacks were never checked there.  For C^5 rank 9 vs 10 the scan
has V-stacks only for d <= 6 (complete, nothing).

## Also new: 6x6x6, rank 10 vs 11, lowest degree 8 (d <= 7 complete, nothing)
((5,3),(3,2,1,1,1),(2,2,1,1,1,1)), g = 2, dims 4410 x 384 x 15, source S_{53}: H-stack (U = M) 2775 (rank 10) vs
2835 (ranks 11, 12, 14); H1 2700 / 2700; V-stack 2880 / 2880 (an H-type separator).  562 of 926 d = 8 components
checked so far.  Lowest separating degrees of the scan: scan/STATUS.md.
