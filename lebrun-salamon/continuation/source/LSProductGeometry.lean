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

variable {n : ℕ} (X : ContactFanoManifold n) (x : ComplexPoint X.variety)
variable (C : GlobalVelocity.TargetChart X.variety x)
variable (D : LegendrianDirections X x C)

set_option maxHeartbeats 6000000 in
/-- Published component geometry supplies the actual hypotheses of the
ordinary cone-addition theorem. A witnessed nonzero Levi value makes the
principal open nonempty; there is no component-spanning hypothesis. -/
theorem componentAddition_denseRange
    (K E : D.directions.Component)
    (a b : Fin (dimension (n := n) + 1) → ℂ)
    (ha : a ∈ D.directions.componentConePoints (contactFrame X x C) K)
    (hb : b ∈ D.directions.componentConePoints (contactFrame X x C) E)
    (hab : ConePairing.pairing (omega X x C) a b ≠ 0) :
    DenseRange (nonorthogonalAddition
      (D.directions.componentConePoints (contactFrame X x C) K)
      (D.directions.componentConePoints (contactFrame X x C) E) (omega X x C)).base := by
  let S := D.directions.componentConePoints (contactFrame X x C) K
  let T := D.directions.componentConePoints (contactFrame X x C) E
  let U := nonorthogonalOpen S T (omega X x C)
  letI : IsDomain (CoordinateRing S) := D.cone_integral K
  letI : IsDomain (CoordinateRing T) := D.cone_integral E
  obtain ⟨hdom, hdim⟩ := LeBrunSalamon.StandardInputs.finiteType_tensorProduct_geometry
    (CoordinateRing S) (CoordinateRing T)
  letI : IsDomain (ProductRing S T) := hdom
  have hbaseChange : Algebra.FiniteType (CoordinateRing S) (ProductRing S T) :=
    Algebra.FiniteType.baseChange (R := ℂ) (A := CoordinateRing T) (CoordinateRing S)
  letI : Algebra.FiniteType ℂ (ProductRing S T) :=
    Algebra.FiniteType.trans (R := ℂ) (S := CoordinateRing S) (A := ProductRing S T)
      (inferInstance : Algebra.FiniteType ℂ (CoordinateRing S)) hbaseChange
  letI : LocallyOfFiniteType (affineBaseMap (ProductRing S T)) :=
    affineBaseMap_finiteType (ProductRing S T)
  have hU : (U : Set (productScheme S T)).Nonempty :=
    nonorthogonalOpen_nonempty S T (omega X x C) a b ha hb hab
  letI : Nonempty U.toScheme := ⟨⟨hU.choose, hU.choose_spec⟩⟩
  letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  letI : LocallyOfFiniteType (U.ι ≫ affineBaseMap (ProductRing S T)) :=
    locallyOfFiniteType_comp U.ι (affineBaseMap (ProductRing S T))
  letI : IsAffine U.toScheme :=
    IsAffineOpen.Spec_basicOpen (pairingFunction S T (omega X x C))
  letI : QuasiCompact (U.ι ≫ affineBaseMap (ProductRing S T)) :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance
  have hdimension : (dimension (n := n) + 1 : WithBot ℕ∞) ≤
      topologicalKrullDim U.toScheme := by
    rw [hdim U hU, D.cone_dimension K, D.cone_dimension E]
    have hcount : (dimension (n := n) + 1 : WithBot ℕ∞) =
        (n : WithBot ℕ∞) + n := by
      exact_mod_cast (dimension_succ X).trans (two_mul n)
    exact hcount.le
  exact ConeDominance.component_nonorthogonalAddition_denseRange D.directions
    (contactFrame X x C) D.disjoint D.cone_closed (omega X x C)
    (omega_skew X x C) D.cone_charts K E hdimension

end LeBrunSalamon.Construction.Lines.ProductGeometry

end
