I am looking for equations of the 6th secant variety σ₆ of the Segre variety P³×P³×P³ ⊂ P(C⁴⊗C⁴⊗C⁴). σ₆ has codimension 4, and a general tensor has rank 7. I found isotypic (Hauenstein–Ikenmeyer–Landsberg style) flattenings whose rank drops exactly on σ₆. The drop is verified exactly by computer, but I would like a structural reason and, ideally, a computer-free proof.

**Setup.** Let V = C⁴ and A = B = C = V, with T ∈ A⊗B⊗C.

- Take the degree-8 isotypic component of S⁸(A⊗B⊗C) of type λ = ((6,2), (3,2,2,1), (3,2,2,1)).
- Its Kronecker coefficient is 4. So there is a 4-dimensional space M* of degree-8 GL(A)×GL(B)×GL(C)-covariants T ↦ Φ(T) ∈ S^{(6,2)}A ⊗ S^{(3,2,2,1)}B ⊗ S^{(3,2,2,1)}C.
- For φ ∈ M*, flatten Φ_φ(T) to a linear map F_φ(T): S^{(6,2)}A* → S^{3221}B ⊗ S^{3221}C, which is 360 → 225.
- Note that S^{3221}V ≅ sl(V) ⊗ det², so the target is sl(B)⊗sl(C), twisted by determinants.

**Matrix-language description.** Write X = T(α) and Y = T(β) for two A-slices; these are 4×4 matrices.

- A covariant of this type is the same thing as a polynomial G(X,Y) ∈ sl(B)⊗sl(C) such that:
  - G has bidegree (6,2) in (X,Y);
  - G is invariant under Y ↦ Y + tX;
  - G is equivariant under (X,Y) ↦ (gXhᵀ, gYhᵀ).
- The image of F_φ(T) is the span of the values G(T(α), T(β)) over all α, β.

**Facts.** Each is proved exactly over Q or checked mod p on many random tensors.

1. **Generic φ does not separate.** For generic φ ∈ M*, rank F_φ = 225 on general tensors of rank 6 and of rank 7.
2. **The separating hyperplane.** There is a hyperplane Π ⊂ M*, defined over Q, such that for every φ ∈ Π:
   - rank F_φ(T) = 220 for a general tensor of rank 6;
   - rank F_φ(T) = 225 for a general tensor of rank 7;
   - for one φ in Π, the ranks on random tensors of rank 5/6/7/8 are 95/220/225/225;
   - for T in σ₆, all φ ∈ Π have their images in one common 220-dimensional subspace, i.e. a common 5-dimensional cokernel.
3. **The product covariant is not in Π.** G₁(X,Y) = (Y·adj X)₀ ⊗ (adj X·Y)₀, where ₀ denotes the traceless part, lies in M* but not in Π.
   - It has rank 225 on general tensors of rank 6 and of rank 7.
   - It has rank 6 on general rank-4 tensors and 110 on general rank-5 tensors.
4. **A-freed version.**
   - Reduction: T = Σᵢ₌₁⁶ aᵢ⊗bᵢ⊗cᵢ is the image of T′ = Σ eᵢ⊗bᵢ⊗cᵢ ∈ C⁶⊗B⊗C, and im F(T) ⊆ im F(T′).
   - Equivalently, im F(T′) = Π_φ(S^{(6,2)}E), where E = span(bᵢ⊗cᵢ) ⊂ B⊗C is spanned by six rank-one matrices.
   - Rank with six rank-one generators: for φ ∈ Π, rank F_φ(T′) = 222, a 3-dimensional cokernel.
   - Rank with seven rank-one generators: 225.
   - Rank when one of the six generators has rank 2: also 225.
5. **Polynomial cokernel vectors.** Fix b₁…b₅ and c₁…c₅ as projective frames and let b₆, c₆ vary.
   - The 3-dimensional cokernel of F(T′) is spanned by polynomial vectors ψ(b₆, c₆) of bidegree (2,2).
   - There is a 5-dimensional space of such sections.
   - There are no sections of degree 0 or 1 in b₆ alone, or in c₆ alone.
   - By symmetry this suggests cokernel vectors of degree 2 in each bᵢ and each cᵢ.
6. **Degree 9.** Similar drops occur in degree 9, both for components with Kronecker coefficient 1:
   - ((8,1),(3,3,3),(3,3,2,1)), S^{81}A* → S^{333}B⊗S^{3321}C: rank 396 on rank 6, 400 on rank 7.
   - ((7,2),(4,2,2,1),(3,3,3)): rank 500 on rank 6, 504 on rank 7.
   - In all cases the drop on σ₆ is at least 4, the codimension of σ₆.
   - All these equations vanish at M₂, the 2×2 matrix multiplication tensor.

**Question.** Is there a structural reason for the rank drop on σ₆? I am looking for something that gives a (nearly) computer-free proof that rank F_φ(T) < 225 for all T ∈ σ₆ (and < 400, < 504 in degree 9). Angles I would like you to consider:

- **Known equations.** Is the drop explained by a Koszul–Young flattening, or by known equations of σ₆, such as the degree-19 HIL module or Strassen-type equations on subspaces?
- **Twisted cubics.** Six general points of P³ lie on a unique twisted cubic (Gale dual to 6 points in P¹); seven points do not. Could the cokernel come from the twisted cubics through b₁…b₆ and through c₁…c₆? Degree 2 in each point would fit quadrics through the points, or products of brackets [ijkl] in which every index appears twice.
- **Linear relations.** Could it come from the 2-dimensional spaces of linear relations among b₁…b₆ and among c₁…c₆ (the kernels of C⁶ → C⁴)?
- **Dimension count.** Can dim Π_φ(S^{(6,2)}E), for E spanned by six rank-one matrices, be computed through the weight (content) decomposition under the torus of E?

Please propose a concrete mechanism, or an explicit equivariant formula for the cokernel vectors ψ in terms of the bᵢ and cᵢ, together with a proof strategy that avoids heavy computation. If it helps, also give a basis of the 4-dimensional space M* in matrix language (polynomials in X, Y, adj X and mixed adjugates) and identify the hyperplane Π.
