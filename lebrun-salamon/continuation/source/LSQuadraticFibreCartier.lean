import LSEffectiveCartierIso
import LSQuadraticPrimitive
import LSPlaneQuadraticPublished

/-! A specified nonzero quadratic closed fibre supplies the actual
Cartier ideal and O(2) comparison for its chosen plane embedding.
The scheme isomorphism is required to commute with that embedding. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.QuadraticFibreCartier

theorem nonzero_section (K : Type) [Field K]
    (q : PlaneQuadratic.Coefficients K) (hq : q ≠ 0) :
    PlaneQuadratic.sectionOf K q ≠ 0 := by
  intro h
  apply hq
  apply (PublishedInputs.ProjectiveSpace.quadraticSections_bijective K).injective
  rw [h, QuadraticPrimitive.sectionOf_zero]

theorem of_quadratic_iso (K : Type) [Field K]
    {X : Scheme.{0}} (i : X ⟶ PlaneQuadratic.Plane K)
    (q : PlaneQuadratic.Coefficients K) (hq : q ≠ 0)
    (e : X ≅ PlaneQuadratic.ZeroScheme K q)
    (he : e.hom ≫ PlaneQuadratic.inclusion K q = i) :
    ∃ h : IsLocallyFreeOfRank (EffectiveCartier.ideal i) 1,
      Nonempty ((EffectiveCartier.line i h).sheaf ≅ (PlaneQuadratic.quadraticLine K).sheaf) := by
  letI : Mono (PlaneQuadratic.sectionOf K q) :=
    PublishedInputs.ProjectiveSpace.nonzero_quadratic_section_regular K 2 (by omega)
      (PlaneQuadratic.sectionOf K q) (nonzero_section K q hq)
  obtain ⟨h0, d, _⟩ := PublishedInputs.EffectiveCartier.regular_zero_locus
    (PlaneQuadratic.quadraticLine K) (PlaneQuadratic.total K)
    (PlaneQuadratic.sectionOf K q)
  obtain ⟨h, ⟨c⟩⟩ := EffectiveCartier.cartier_of_overIso
    i (PlaneQuadratic.inclusion K q) e he h0
  exact ⟨h, ⟨c ≪≫ d⟩⟩

end LeBrunSalamon.QuadraticFibreCartier
end
