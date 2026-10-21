# Combined isotypic flattenings

Flattenings that use **several** isotypic components of T^{⊗d} at once instead of one.  Code: `combflat.py`
(library), `comb_search.py` (search driver), `test_comb.py` (validation), `brute.py` (independent brute force).

## Construction

T ∈ A⊗B⊗C, T^{⊗d} ∈ S^d(A⊗B⊗C) = ⊕ S_λA ⊗ S_μB ⊗ S_νC ⊗ M_{λμν} (dim M = g = Kronecker coefficient).
A flattening is a block matrix

| | column block j: S_{μ_j}B ⊗ S_{ν_j}C ⊗ Y_j (Y_j = C^{l_j}) |
|---|---|
| **row block i:** S_{λ_i}A^* ⊗ X_i (X_i = C^{k_i}) | Σ_m Ψ_ij[m, x, y] · F_{ij,m} |

where F_{ij,m} is the isotypic flattening of the component (λ_i, μ_j, ν_j) with the m-th basis functional of M_ij^*,
and Ψ_ij ∈ M_ij^* ⊗ X_i^* ⊗ Y_j says where the Kronecker space goes (zero block if g_ij = 0).  This is the
flattening of the image of T^{⊗d} under a GL(A)×GL(B)×GL(C)-equivariant linear map, so its rank is a
lower-semicontinuous GL-invariant: a drop on general rank-r tensors gives equations of σ_r.

Special cases:
* one block: `gN` (k = l = 1), `HN` (k = 1, l = g), `VN` (k = g, l = 1), and the new **reshaped** case k, l ≥ 2
  (family E: Ψ a generic tensor in M^*⊗X^*⊗Y; for g = 2 it reduces to two gN blocks, nontrivial from g = 3);
* **family A**: fixed source λ, a sum over a set S of targets (μ, ν).  aux = 1, level l_j = g_j: Kronecker spaces on the
  target side (the rank is dim of the sum of the H-stack column spaces); level 1: one generic functional each;
  aux = k ≥ 2: Kronecker spaces on the source side through a shared X = C^k ("family C");
* **family B**: fixed target (μ, ν), a sum over a set S of sources λ.  aux = 1, level k_i = g_i: Kronecker spaces on the
  source side (the rank is dim of the sum of the V-stack row spaces); aux = l ≥ 2: on the target side through a shared
  Y = C^l ("family D").

Two facts that frame the search:
* family A over **all** targets with full Kronecker spaces is S_λ(T_A): S_λA^* → S_λ(B⊗C), of rank dim S_λ(C^{rank T_A})
  (checked in `test_comb.py`); it never separates σ_r for r ≥ n.  Only partial sums can.  Equivalently, rank of the
  sum over S = n1 − dim(S_λ(E) ∩ ⊕_{j ∉ S} I_j), with E = T_A(A^*) ⊂ B⊗C and I_j the isotypic components of S_λ(B⊗C);
* family B over all sources (full Kronecker spaces) is the (μ, ν)-isotypic part of E^{⊗d} ⊂ B^{⊗d}⊗C^{⊗d}, which is
  NOT trivial.

## Evaluation

All components are evaluated by `hwv_fast` (exact mod p = 524287) on **shared** sample points: one set of N1 points of
S_λA^* per source and one set of K point pairs per target (μ, ν), used by every block in that row (column).  The
sampled matrix is P M Q with block-diagonal P, Q, and has the exact rank when
N1_i ≥ min(n1_i, Σ_j l_j n23_j) and K_j ≥ min(n23_j, Σ_i k_i n1_i) (+8); `Context.exact()` checks this.  For the
lattices every block is stored once, compressed by a random matrix to a square matrix with the same column (row)
space, so the rank of a sub-sum costs one small rank computation.  Tensors: the same random rank-r tensors as
`sweep_fast.py` for the same seed and rank list.  Flattening matrices are cached on disk in `live/cache/` (untracked).

## Validation (`python3 test_comb.py full`, log `logs/test_full.log`: 0 failures)
* families A and B (full Kronecker spaces) equal an independent brute force (`brute.py`: T^{⊗d} as an explicit array,
  isotypic projectors and Young symmetrizers on tensor positions, no highest weight vectors, no sampling) on every
  singleton, the full set and random subsets: n = 2 (d = 3, 4, 5), n = 3 (d = 3; family A at d = 4);
* family A over all targets = dim S_λ(C^{min(r,n)}) for every λ, r = 1..n+1 (n = 2, 3, 4; d = 4, 5);
* assembled block matrices with generic Ψ equal the lattice dimensions (families A and B, aux 1 and 2);
* single components reproduce the known isotypic ranks: C^3 d = 5 (3/6, 12/15, 12/15, V2 15/21), C^4 d = 8
  ((6,2),(3,2,2,1),(3,2,2,1)) H4 304/309 and ((5,3),(3,3,1,1),(3,3,1,1)) V2 252/254.

## Results

### C^3, rank 4 vs 5: separated at d = 4 (isotypic flattenings: d = 5)
Family B, target S^{211}B ⊗ S^{211}C (≅ B⊗C ⊗ det_B ⊗ det_C, dimension 9), sources λ ∈ {22, 31} (all g = 1):

| sources | rank-1 | rank-2 | rank-3 | rank-4 | rank-5 | rank-6 |
|---|---|---|---|---|---|---|
| 22 alone | 0 | 0 | 3 | 6 | 6 | 6 |
| 31 alone | 0 | 0 | 3 | 3 | 3 | 3 |
| **22 + 31** | 0 | 0 | 3 | **6** | **9** | 9 |
| 22 + 4, 22 + 31 + 4 | 0 | 0 | 3 | 6 | 9 | 9 |
| all four (4, 31, 22, 211) | 0 | 0 | 3 | 9 | 9 | 9 |

So the 7×7 minors of the (6 + 15) × 9 matrix S^{22}A^* ⊕ S^{31}A^* → S^{211}B ⊗ S^{211}C (entries of degree 4 in T)
vanish on σ_4 and not on a general tensor.  Verified with two seeds and by the brute force (ranks 3 / 6 / 9 on random
rank-3 / 4 / 5 tensors).  Also with a shared Y = C^2 on the target side (family D): all four sources give 12 vs 15.
d = 3: nothing.  (Log `logs/c3_d4_r45.log`; at d = 5 many more combined hits besides the three known components,
`logs/c3_d5_r45.log`, e.g. target (221, 221), sources {221, 5}: 6 vs 9 while the single blocks give 3/3 and 6/6.)

### C^4, rank 6 vs 7
* d = 4: nothing (families A, B with aux 1, 2, 3 and E; `logs/c4_d4_r67.log`).
* d = 5, 6: see the logs `logs/c4_d5_r67.log`, `logs/c4_d6_r67_{A,B,E}.log` (running at the time of writing).

## Usage
```
pip install numpy sympy opt_einsum
python3 test_comb.py quick            # ~2 min;  'full' ~13 min (adds C^4 d = 8 controls)
python3 comb_search.py 4 6 6,7 --fam A,B,E --aux 1,2      # sums over targets / sources, reshaped single components
python3 comb_search.py 5 5 8,9,10 --fam A,B                # every consecutive pair of the rank list is checked
```
Lines `*** SEPARATES` mark hits (`NEW`: no summand separates the same rank pair on its own); a summary line per lattice
lists the singleton ranks, named subsets (all, by μ, by ν, by number of rows, ...) and the largest drop found.
Subsets tried per lattice: singles (levels 1 and g), all, all-but-one, natural groups, pairs, triples, random subsets,
greedy growth.  Not yet implemented: tensoring with identities (Koszul/Young-type), tangency flattenings.
