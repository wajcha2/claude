import RecompileBasePart04

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne

namespace LeBrunSalamon.PublishedInputs.Picard

/-- Stacks Project, Lemma 31.29.4, Tag 0BDA, part (1).
Triviality of Pic(Spec R) says precisely that every invertible sheaf is
isomorphic to the unit sheaf. The base ring is an arbitrary UFD; the leaf
does not mention projective space, a marked point, or a chosen twist.
-/
theorem affineUFD_trivial (R : Type) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R]
    (L : (Spec (CommRingCat.of R)).Modules) (hL : IsLocallyFreeOfRank L 1) :
    Nonempty (PhaseTwentyFive.structureModule (Spec (CommRingCat.of R)) ≅ L) := by
  sorry

end LeBrunSalamon.PublishedInputs.Picard

end
