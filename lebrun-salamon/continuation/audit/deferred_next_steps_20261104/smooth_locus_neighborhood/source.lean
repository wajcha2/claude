import Mathlib

/-! The pointwise-to-open step for the relative Hom smoothness argument.
Only the existing Mathlib smooth locus is used. No tangent criterion,
infinitesimal lifting theorem, or new published input is introduced. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry

universe u

namespace LeBrunSalamon.Next3i.SmoothLocusNeighborhood

/-- The actual morphism restricted to its smooth locus is smooth. -/
theorem smooth_restriction {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] : Smooth (f.smoothLocus.ι ≫ f) := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  apply top_unique
  intro x hx
  change x.1 ∈ f.smoothLocus
  exact x.2

/-- A field-valued point in the smooth locus supplies an open containing
its whole image, with the exact restricted structural map smooth. -/
theorem exists_open_of_point_mem {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (K : Type u) [Field K]
    (p : Spec (CommRingCat.of K) ⟶ X)
    (hp : p (IsLocalRing.closedPoint K) ∈ f.smoothLocus) :
    ∃ U : X.Opens, Set.range p ⊆ (U : Set X) ∧ Smooth (U.ι ≫ f) := by
  refine ⟨f.smoothLocus, ?_, smooth_restriction f⟩
  rintro x ⟨z, rfl⟩
  rw [show z = IsLocalRing.closedPoint K from Subsingleton.elim _ _]
  exact hp

/-- The same conclusion from the formal smoothness of the actual stalk map. -/
theorem exists_open_of_formallySmooth_stalk {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (K : Type u) [Field K]
    (p : Spec (CommRingCat.of K) ⟶ X)
    (hp : (f.stalkMap (p (IsLocalRing.closedPoint K))).hom.FormallySmooth) :
    ∃ U : X.Opens, Set.range p ⊆ (U : Set X) ∧ Smooth (U.ι ≫ f) :=
  exists_open_of_point_mem f K p (Scheme.Hom.mem_smoothLocus.mpr hp)

end LeBrunSalamon.Next3i.SmoothLocusNeighborhood

#print axioms LeBrunSalamon.Next3i.SmoothLocusNeighborhood.smooth_restriction
#print axioms LeBrunSalamon.Next3i.SmoothLocusNeighborhood.exists_open_of_point_mem
#print axioms LeBrunSalamon.Next3i.SmoothLocusNeighborhood.exists_open_of_formallySmooth_stalk

end
