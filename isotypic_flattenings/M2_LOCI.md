# M2 at the rank-6 drop loci of isotypic flattenings (C^4 (x) C^4 (x) C^4, components with g >= 2)

Goal: a subspace U of the multiplicity space M^* (dim M = g = Kronecker coefficient >= 2) such that the isotypic
flattening of a general rank-6 tensor has SMALLER rank than that of M2 (2x2 matrix multiplication).  That would show
M2 not in sigma_6, i.e. a new proof of border rank(M2) = 7.

Status: **no such U found** (d <= 9 analysed; d = 10, 11 candidate screen running, see below).
The reason is structural (GL2^3 symmetry of M2, Section 1), and the computations (Sections 2-4) confirm it.

## 0. Flattening types and notation
For a tensor T, Phi(T) in S^{l1}V (x) S^{l2}V (x) S^{l3}V (x) M is the isotypic component; for U in M^* of dim k:
* `g1`  (k = 1): F_phi(T): S^{l1}V^* -> S^{l2}V (x) S^{l3}V;
* `H_k` : S^{l1}V^* -> U^* (x) S^{l2}V (x) S^{l3}V  (rank = n1 - dim common kernel);
* `V_k` : U (x) S^{l1}V^* -> S^{l2}V (x) S^{l3}V      (rank = dim of the sum of the images).
"Direction N" = source S^{l_N}V^*.  Values `a/b/M2=c` = rank on a random rank-6 tensor / random rank-7 tensor / M2.

Two facts used throughout:
* rank_U(M2) <= rank_U(general tensor) for every U (M2 is a limit of rank-7 tensors).  Hence a U with
  rank_U(R6) < rank_U(M2) **must separate rank 6 from rank 7**: only the separating loci can work.
* All ranks of T at all U and all types are determined by the subspace K(T) = ker(V_g(T)) in M^* (x) S^{l1}V^*,
  because F_phi(T) x = V_g(T)(phi (x) x): rank F_phi = n1 - dim{x : phi (x) x in K(T)}, H(U) = n1 - dim{x : U (x) x in K(T)},
  V(U) = k n1 - dim(K(T) cap U (x) S^{l1}V^*).  The same holds for K'(T) = ker(H_g(T)^t).

## 1. The GL2^3 bound for M2 (`m2_bound.py`, `m2_bound_stacks.py`)
A = U (x) V^*, B = V (x) W^*, C = W (x) U^* (dim U = dim V = dim W = 2); M2 is fixed by G = GL(U) x GL(V) x GL(W), so for every
phi the tensor Phi_phi(M2) is G-invariant and every flattening of it is G-equivariant.  With a_{mu nu} = g(l1, mu, nu) and
b_{mu nu} = sum_xi g(l2, nu, xi) g(l3, xi, mu) (mu, nu, xi partitions of d with <= 2 rows, D_mu = mu1 - mu2 + 1):
* g1:  rank <= sum_{mu,nu} D_mu D_nu min(a, b);
* H_k: rank <= sum D_mu D_nu min(a, k b);   V_k: rank <= sum D_mu D_nu min(k a, b).
Checks: reproduces 19 (d = 8 hit), 20 and 36 (d = 9 hits) exactly; over 2244 computed M2 ranks the bound is never
violated and is attained in 95% of the cases.  Since sum_{mu nu} D D b = dim (S^{l2}B (x) S^{l3}C)^{GL(W)} is a small
fraction of n23 = dim S^{l2}V (x) S^{l3}V, **M2 can never beat rank 6 at a separation of "cokernel type"** (rank-6 images
failing to fill the target): all known separators (d = 8, 9) are of that type.  M2 can only compete where the source is
small and b >= k a, i.e. where a rank-6 deficiency would have to be a kernel.

## 2. Exclusion tests (`m2cmp2.py`, `m2classify2.py`)
For each component (g >= 2) and direction: ranks of R6, R7, M2 for a nested generic flag U_1 < ... < U_g (all k, both
H and V), and
* **EXCL**: K(R6) <= K(M2) or K'(R6) <= K'(M2) (tested as column/row space containment of the sampled stacks).  Then
  rank_U(M2) <= rank_U(R6) for EVERY U and type.  (Includes all tall components where V_g(R6) is injective.)
* **DROP**: not EXCL, but rho6 = generic g1 rank of R6 >= max over all U and types of rank_U(M2).  Then a winning U must
  lie inside the common rank-6 drop locus D6 = {phi : rank F_phi(T) < rho6 for all rank-6 T} (since H(U), V(U) >=
  rank F_phi for phi in U); D6 is analysed with `m2lines.py` (pencils / random lines, exact drop polynomials, roots over
  F_p and extensions), `m2rank1.py`, `m2lambda.py` (linear components of D6 of higher codimension), `m2kappa.py`.

## 3. Results
### d <= 7 (no rank-6/7 separator exists at generic U, rank-scan agent)
| d | comp-dirs | EXCL | DROP / OPEN | SEP | M2 wins |
|---|---|---|---|---|---|
| 5 | 6 | 6 | 0 | 0 | 0 |
| 6 | 69 | 58 | 11 | 0 | 0 |
| 7 | 255 | 214 | 35 / 6 | 0 | 0 |

The non-excluded cases at d <= 7 have only tensor-independent drop loci, where rank 7 drops equally (hence M2 <= rank 6),
e.g. d = 6 ((4,2),(3,1,1,1),(3,1,1,1)) dir1: one point, ranks 10/10/10, M2 10; d = 7 ((4,1,1,1),(3,2,1,1),(3,2,1,1)) dir1
(the one case where M2 is injective, rank 20 = n1): the rank-6 drop locus is a linear plane Lambda in P^4 (codim 2, found
with `m2rank1.py`: K(R6) cap P (x) S^{l1} = phi_0 (x) W, all rank one, for random 3-dim P), the SAME plane for R6a, R6b and
R7; on Lambda all tensors have rank 16 and M2 has rank 4.

### d = 8: the 8 separating loci of the rank-scan agent (branch claude/trusting-bohr-hdnmbv), all direction 1
| component | g | separating U | rank 6 / rank 7 | M2 | GL2^3 bound |
|---|---|---|---|---|---|
| ((5,1,1,1),(3,2,2,1),(3,2,2,1)) | 5 | V5 (U = M) | 146 / 147 | 19 | 19 |
| ((5,3),(3,3,1,1),(3,3,1,1)) | 2 | V2 | 252 / 254 | 34 | 34 |
| ((5,3),(5,1,1,1),(5,1,1,1)) | 2 | V2 | 252 / 254 | 34 | 34 |
| ((6,2),(3,2,2,1),(3,2,2,1)) | 4 | H2, H3, H4 | 304 / 309 | 19 | 19 |
| ((4,2,2),(4,2,1,1),(3,3,1,1)) | 6 | V6 | 460 / 462 | 39 | 39 |
| ((5,3),(5,1,1,1),(4,2,1,1)) | 3 | V2, V3 | 483 / 485 | 45 | 45 |
| ((5,3),(4,2,1,1),(3,3,1,1)) | 4 | V3, V4 | 654 / 656 | 45 | 48 |
| ((5,3),(4,2,1,1),(4,2,1,1)) | 6 | V4, V5, V6 | 953-970 / 955-974 | 79 | 79-88 |
Plus the special 1-dim U of the d=8 hit (d9 agent): the separating plane Pi_sep (220/225, M2 = 19 or 0 at phi_M2) and the
rank-84 plane (84/84, M2 = 19), reproduced with `m2lines.py`.  Since rank_U(M2) <= GL2^3 bound for EVERY U of the given
type, no special U inside these components can work either unless rank 6 drops by a factor 3-15.
The six d = 8 cases where rank 7 is deficient and the M2 bound reaches the rank-7 rank (e.g. ((7,1),(4,2,1,1),(4,2,1,1))
dir1 V2 79/79, M2 79; ((5,1,1,1),(4,3,1),(4,3,1)) dir1 V5 174/174, M2 148) are all structural: the kernel K(T) is
spanned by phi_0 (x) x(T) with the SAME phi_0 for all rank-6 and rank-7 tensors (`m2kappa.py`), so no separation.

### d = 9 (components with g >= 2; new: rank-6/7 profiles for all k, both stack types)
Full analysis (R6, R7, M2, all k, containment) for the 717 cheapest of the 1560 component-directions
(`m2loci/all_d9_w*.log`): **no separation at any generic U, no M2 win**; 627 EXCL, 87 DROP, 3 OPEN.  The 3 OPEN cases
(M2 injective at generic phi, rank-6 V-stack with a kernel) are structural: K(T) = phi_0 (x) W(T) with the SAME phi_0 for
all rank-6 and rank-7 tensors (`m2kappa.py`, `m2rank1.py`):
  ((5,2,1,1),(4,3,2),(3,3,3)) dir1 (dim K = 4), ((6,1,1,1),(5,2,1,1),(5,2,1,1)) dir1 (dim K = 20),
  ((6,1,1,1),(5,2,1,1),(4,3,2)) dir2 (dim K = 4).
The 87 DROP + 3 OPEN cases: exact pencils / 1-2 random lines each (`m2loci/lines_d9a.log`, 157 lines): 31 lines meet common
rank-6 drop points, all tensor-independent (rank 6 = rank 7 there, M2 <= rank 6), no separation, no win.
The remaining 843 (larger) component-directions were screened (`SCREEN=1`: rank-6 tensor only, full V- and H-stack;
injective V_g resp. surjective H_g excludes every U rigorously; `m2loci/screen_d9_w*.log`): **530 EXCL**, 313 need the
structural analysis `m2deep.py` (K(T) for R6a, R6b, R7: dimension, M^*-support S, exact pencils inside P(S);
`m2loci/deep_d9_w*.log`, running).  In every case analysed so far the three kernels have the same dimension and the same
support S, and all common drop points in P(S) are tensor-independent (equal ranks for R6a, R6b, R7; M2 below), e.g.
((6,1,1,1),(5,3,1),(4,3,2)) dir2: S of dim 2, drop points with ranks 300/300/300 (M2 48, 68);
((5,2,1,1),(5,2,1,1),(4,2,2,1)) dir1: S of dim 11, drop points 80/80/80 (M2 20).

### d = 10 and d = 11 (user request: skip the rest of d = 8; d = 9 structural follow-up paused at 20 of 313)
Candidates = the component-directions where the GL2^3 bound lets M2 reach full rank, for a single phi or for a source-limited
V_k (k n1 <= n23): d = 10: 1424 (all), d = 11: the cheapest 2658 of 2958 (the 300 most expensive, ~35 h, run last;
`m2loci/jobs_d1011_main.txt`, `m2loci/jobs_d11_tail.txt`).  Everywhere else M2 is capped below the generic rank and cannot beat
rank 6 at a separating locus.  Screen (`SCREEN=1`, injective full V-stack of a rank-6 tensor => every U excluded), then
`m2deep2.py` on the failures (kernels of R6a and R7; R6b and M2 only at points where rank 6 < rank 7).
Screen snapshot 2026-10-05 22:20 UTC (logs `m2loci/snap/`, live in `live/`; chunks of <= 2 h, resumable):
| d | screened | EXCL (all U) | to follow-up |
|---|---|---|---|
| 10 | 1307 / 1424 | 1175 | 132 |
| 11 | 2404 / 2658 | 2200 | 204 |
Follow-up (`m2deep2.py`, kernels of R6a and R7; R6b and M2 only where rank 6 < rank 7): **all 273 screen failures known on
2026-10-05 13:50 UTC are done, none separating, no M2 win**:
| d | STRUCT (same phi_0 for all tensors) | common support S of dim >= 2, exact pencils in P(S) |
|---|---|---|
| 10 | 48 | 54 |
| 11 | 55 | 116 |
In the S cases, every drop point common to both rank-6 tensors has rank 6 = rank 7 (e.g. ((8,1,1,1),(5,4,1,1),(5,4,1,1)) dir1:
points with 100/100 and 20/20; ((5,4,1),(5,3,1,1),(4,4,1,1)) dir2: 90/90; ((5,2,2,1),(5,2,2,1),(4,3,3)) dir1: 64/64); the points
where only R6a drops are not shared by R6b (gcd of the two drop polynomials = 1).  The largest case,
((6,2,1,1),(6,2,1,1),(6,2,1,1)) dir3 (g = 18, dim K = 146 for R6a and R7, support of dim 3), has no rank-6 drop points in P(S).
Not yet done: follow-ups of the 63 screen failures found since then, 117 (d = 10) + 254 (d = 11) candidates to screen, the
d = 11 tail (300).

### Recurring pattern
Every rank-6 deficiency found in a flattening where M2 could compete is tensor-independent: a fixed phi_0 (or a fixed
linear subspace Lambda of P(M^*)) where F_phi drops for EVERY tensor, rank 7 included (d = 7: plane Lambda, ranks 16;
d = 8: phi_0 with rank 34 of 35; d = 9: phi_0 with kernels of dim 4 and 20).  Genuine rank-6/7 separations (d = 8: the 8
components above, d = 9: the two g = 1 components) are of cokernel type, where M2 is capped far below by its GL2^3 bound.

## 4. Reproduce
```
pip install numpy sympy opt_einsum
python3 m2_bound_stacks.py 9 > bounds_d9.txt                       # GL2^3 bounds, seconds
ALLK=1 python3 m2cmp2.py "((5,3),(3,3,1,1),(3,3,1,1))" 0           # one component, direction 1
ALLK=1 NOR6B=1 python3 m2cmp2.py LIST m2loci/jobs_d9_sorted.txt 3000 <w> 4 > m2loci/all_d9_w<w>.log   # 4 workers
python3 m2classify2.py m2loci/all_d9_w*.log
python3 m2lines.py "((6,2),(3,2,2,1),(3,2,2,1))" 0 2                # drop points on 2 random lines + M2 there
```
