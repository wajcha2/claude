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
vanish on σ_4 and not on a general tensor.

**Matrix form.** With E = T_A(A^*) = ⟨X_1, X_2, X_3⟩ ⊂ Mat_3 the slices, S^{211}B ⊗ S^{211}C ≅ Mat_3 (up to det twists) and
the degree-4 covariant (X, Y) ↦ X·adj(Y)·X has A-type S²⊗S² = S⁴ ⊕ S³¹ ⊕ S²² (no S²¹¹).  Numerically (4 seeds, ranks 1–6):

    dim span{ X adj(Y) X : X, Y ∈ E } = 0, 0, 3, 6, 9, 9      (rank of T = 1, 2, 3, 4, 5, 6)

exactly the profile of the combined flattening; for comparison span{X adj(Y) Z} = 9 already on σ_4 (it also contains the
S²¹¹ part), and span{X adj(Y) Z − Z adj(Y) X} = 3 on σ_4 and in general (Strassen's commutator, whose determinant gives
the degree-9 equation).  So: the linear map S²A^* ⊗ S²A^* → Mat_3, (α, β) ↦ T(α) adj(T(β)) T(α) (polarized) has
rank ≤ 6 on σ_4 and 9 on a general tensor.  Verified with two seeds and by the brute force (ranks 3 / 6 / 9 on random
rank-3 / 4 / 5 tensors).  Also with a shared Y = C^2 on the target side (family D): all four sources give 12 vs 15.
d = 3: nothing.  (Log `logs/c3_d4_r45.log`; at d = 5 many more combined hits besides the three known components,
`logs/c3_d5_r45.log`, e.g. target (221, 221), sources {221, 5}: 6 vs 9 while the single blocks give 3/3 and 6/6.)

### C^4 (rank 6 vs 7: isotypic flattenings first at d = 8, Koszul of the isotypic tensor at d = 5; combined: d = 6)
* d = 2, 3 (ranks 4..7): no new separation; the lowest degrees of 4 vs 5 (d = 2) and 5 vs 6 (d = 3) are not lowered
  (`logs/c4_d2_r4567.log`, `logs/c4_d3_r4567.log`).
* d = 4: nothing for 6 vs 7 (families A, B with aux 1, 2, 3 and E; `logs/c4_d4_r67.log`).
* d = 6, family E (all reshaped (k, l), k, l >= 2, of the 99 components with g >= 2): nothing (`logs/c4_d6_r67_E.log`).
* d = 5: nothing (families A, B with aux 1, 2, 3 and E; greedy 4 runs per lattice; 1522 s; `logs/c4_d5_r67.log`).
  So at d = 5 the Koszul flattening of the isotypic tensor (koszul4_d5_done.log) separates and these do not.
* **d = 6: rank 6 vs 7 SEPARATED** (isotypic flattenings: first at d = 8), family B (`logs/c4_d6_r67_B.log`, still running over
  the remaining targets; family A complete with no separation, `logs/c4_d6_r67_A.log`):
  target S^{321}B ⊗ S^{222}C (dim 64 · 10 = 640; S^{222}C^4 = S^2C^* ⊗ det^2), sources λ ∈ {51, 42, 411} (all g = 1,
  dims 140, 126, 70) with the Kronecker spaces on the source side, i.e. the (140 + 126 + 70) × 640 matrix
  S^{51}A^* ⊕ S^{42}A^* ⊕ S^{411}A^* → S^{321}B ⊗ S^{222}C (entries of degree 6 in T):

  | sources | rank 5 | rank 6 | rank 7 | rank 8 |
  |---|---|---|---|---|
  | 51 | 110 | 140 | 140 | 140 |
  | 42 | 116 | 126 | 126 | 126 |
  | 411 | 70 | 70 | 70 | 70 |
  | 42 + 51 | 176 | 256 | 256 | 256 |
  | 411 + 51 | 150 | 204 | 204 | 204 |
  | 411 + 42 | 181 | 196 | 196 | 196 |
  | **411 + 42 + 51** | 196 | **316** | **320** | 320 |
  | all six sources (321 with g = 2 at full level) | 220 | 400 | 400 | 400 |
  | all six, generic functional on M_321 | 220 | 396 | 400 | 400 |

  The drop is 4 = codim σ_6, and no proper sub-sum of {51, 42, 411} separates.  So the 317 × 317 minors (degree 1902 in T)
  vanish on σ_6 and not on a general tensor.  Verified: seeds 5, 11, 23 (p = 524287) and 31, 47 (p = 524269), lattice
  dimensions and directly assembled block matrix agree every time; sampling exact by the bounds of `Context.exact`.
  Supersets that add 3111, 2211 or 321 (generic functional) also separate (e.g. all with 321 at level 1: 396 vs 400).
  The mirror target S^{222}B ⊗ S^{321}C gives the same numbers (B <-> C symmetry), as it must.

### C^5 (ranks 7..10: isotypic 7 vs 8 at d = 5, 8 vs 9 at d = 6, 9 vs 10 not below d = 13 on the promising lists)
* d = 4: nothing for 7 vs 8, 8 vs 9, 9 vs 10 (A, B with aux 1, 2, 3 and E; `logs/c5_d4_r78910.log`).
* d = 5: running (`logs/c5_d5_r78910.log`).  First NEW combined hit, rank 7 vs 8 (the same degree where isotypic
  flattenings first separate 7 vs 8, via ((4,1),(2,1,1,1),(2,1,1,1))): family A, source S^{32}A^* (dim 175), targets
  Λ^5B ⊗ S^{221}C and S^{221}B ⊗ Λ^5C (dim 75 each, all g = 1):

  | | rank 5 | 6 | 7 | 8 | 9 |
  |---|---|---|---|---|---|
  | (1^5, 221) alone | 5 | 30 | 75 | 75 | 75 |
  | (221, 1^5) alone | 5 | 30 | 75 | 75 | 75 |
  | **sum** | 5 | 30 | **105** | **150** | 150 |

  Each single target is already of full rank 75 on rank-7 tensors; their column spaces in S^{32}A meet in 45 dimensions
  on rank 7 and in 0 on rank 8.  Seeds 5, 11, 23, lattice and directly assembled block matrix agree.

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
