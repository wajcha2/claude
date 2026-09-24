# Isotypic flattenings separating sigma_4 in (C^3)^{⊗3}

Setting: V = C^3, T in V⊗V⊗V, sigma_4 = 4th secant variety of the Segre variety (Strassen's
degree 9 hypersurface). For d = 2,3,4,5, all triples lam = (lam1,lam2,lam3) of partitions of d
with at most 3 rows and nonzero Kronecker coefficient g_lam, we computed the isotypic tensor
phi(iso_lam(T^{⊗d})) in S^{lam1}V ⊗ S^{lam2}V ⊗ S^{lam3}V (phi a functional on the multiplicity
space, realised by Young symmetrizers c_{t1} ⊗ c_{t2}s2 ⊗ c_{t3}s3) and the ranks of its three
flattenings S^{lam_i}V^* -> ⊗_{j≠i} S^{lam_j}V, for random general tensors and random rank-4
tensors. All arithmetic is exact (mod a prime, and one instance verified over Q with sympy).

## Result

* d = 2, 3, 4: no isotypic flattening separates. (All Kronecker coefficients are <= 1 here,
  so the isotypic tensor is unique up to scale and there is no choice of functional.)
* d = 5: three components separate, all via the flattening from the first factor.

| lam                          | g | flattening (source -> target)                                   | size   | rank general | rank on sigma_4 |
|------------------------------|---|-----------------------------------------------------------------|--------|--------------|-----------------|
| ((3,1,1),(2,2,1),(2,2,1))    | 1 | S^{311}V^* -> S^{221}V ⊗ S^{221}V  (= S^2V^* -> V^*⊗V^* up to det) | 6 x 9  | 6            | 3               |
| ((3,2),(3,1,1),(2,2,1))      | 1 | S^{32}V^* -> S^{311}V ⊗ S^{221}V                                 | 15 x 18| 15           | 12              |
| ((3,2),(3,1,1),(3,1,1))      | 2 | S^{32}V^* -> S^{311}V ⊗ S^{311}V (generic phi, and every sampled Young functional) | 15 x 36| 15 | 12     |
| ((3,2),(3,1,1),(3,1,1))      | 2 | M^* ⊗ S^{32}V^* -> S^{311}V ⊗ S^{311}V (full multiplicity space) | 30 x 36| 21           | 15              |

Here S^{(3,1,1)}C^3 = S^2V ⊗ det, S^{(2,2,1)}C^3 = V^* ⊗ det^2, dim S^{(3,2)}C^3 = 15.
The other two flattening directions of these tensors have the same rank on both classes.
The "rank on sigma_4" values were observed on 6 independent random rank-4 tensors (two primes);
a small-integer rank-4 witness in verify_exact.py gives 3 / 10 / 11 over Q (rank is lower
semicontinuous, so a special point of sigma_4 may drop further), and the general witnesses
attain full rank 6 / 15 / 15 over Q, which proves the generic ranks.

## Files
* isoflat.py       library (partitions, Murnaghan–Nakayama, Kronecker coefficients, Young
                   symmetrizers on V^{⊗d}, isotypic tensors, modular rank)
* sanity.py        sanity checks (rank-1 / rank-2 tensors, span dim = Kronecker coefficient)
* sweep.py         the search:  python3 sweep.py 2 5
* sweep5.log       output of the d = 5 sweep
* verify.py        re-run of the three hits with a second prime and fresh tensors
* verify_exact.py  exact verification over Q with sympy
