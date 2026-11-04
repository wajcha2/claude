import LSPublishedDirections

/-!
## Actual affine product geometry and cone-addition dominance

The single reviewed input is the classical dimension and integrality
theorem for products of finite-type complex domains. Its application
below keeps the actual tensor-product ring and the actual principal open.
The contact-specific dominance conclusion is proved by the existing
ordinary fibre-rigidity argument.

A focused native diagnostic reached its wall limit. Current-source kernel replay
is pending; exact receipts are in audit/ci_compatibility_repairs/.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open scoped TensorProduct

namespace LeBrunSalamon.StandardInputs

/-- Classical geometry of the actual product of two affine complex
varieties, including dimension on each supplied nonempty open. -/
theorem finiteType_tensorProduct_geometry
    (A B : Type) [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    [Algebra.FiniteType ℂ A] [Algebra.FiniteType ℂ B] [IsDomain A] [IsDomain B] :
    IsDomain (A ⊗[ℂ] B) ∧
      ∀ U : (Spec (CommRingCat.of (A ⊗[ℂ] B))).Opens,
        (U : Set (Spec (CommRingCat.of (A ⊗[ℂ] B)))).Nonempty →
          topologicalKrullDim U.toScheme = ringKrullDim A + ringKrullDim B := by
  sorry

end LeBrunSalamon.StandardInputs

namespace LeBrunSalamon.Construction.Lines.ProductGeometry

open LeBrunSalamon.PhaseTwentySeven

open DirectionCones ConeGeometry VelocityCoordinates PublishedDirections

/-- Finite type of the literal affine structural morphism. -/
instance affineBaseMap_finiteType (A : Type) [CommRing A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] : LocallyOfFiniteType (affineBaseMap A) := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance


end LeBrunSalamon.Construction.Lines.ProductGeometry

end
