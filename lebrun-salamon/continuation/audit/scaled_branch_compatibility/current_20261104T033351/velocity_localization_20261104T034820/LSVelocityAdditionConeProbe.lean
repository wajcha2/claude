import LSScaledVelocities

/-!
## The actual nonorthogonal Hom-velocity addition family

The source is a product of the actual bounded scalar line families,
restricted by the actual Levi polynomial. Its complex points cover the
nonorthogonal component-cone pairs, so the proved cone-addition dominance
transfers to this source. All maps and their coordinate functions are
fixed before generic smoothness is used.

Source preparation only; no compiler has been invoked.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxErrors 1
set_option diagnostics true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open scoped TensorProduct

namespace LeBrunSalamon.Construction.Lines.VelocityAdditionFamily

open DirectionCones ConeGeometry SectionAlgebra VelocityCoordinates GlobalCoordinates

section ConePoints
variable {I : Type} [Fintype I]

/-- Every actual complex point of the nonorthogonal cone product is an
actual nonorthogonal pair of its equation-closed coordinate sets. -/
theorem conePoint_coordinates (S T : Set (I → ℂ))
    (hS : EquationClosed S) (hT : EquationClosed T) (omega : I → I → ℂ)
    (p : PointsOver ComplexBase (𝟙 ComplexBase) (nonorthogonalOpen S T omega).toScheme
      ((nonorthogonalOpen S T omega).ι ≫ affineBaseMap (ProductRing S T))) :
    ∃ (a b : I → ℂ) (ha : a ∈ S) (hb : b ∈ T),
      ConePairing.pairing omega a b ≠ 0 ∧
        p.val ≫ nonorthogonalAddition S T omega = coordinatePoint (a + b) := by
  let q : ProductRing S T →ₐ[ℂ] ℂ := GlobalVelocity.specPoint
    (p.val ≫ (nonorthogonalOpen S T omega).ι) (by simpa only [Category.assoc] using p.property)
  let q₁ : CoordinateRing S →ₐ[ℂ] ℂ := q.comp Algebra.TensorProduct.includeLeft
  let q₂ : CoordinateRing T →ₐ[ℂ] ℂ := q.comp Algebra.TensorProduct.includeRight
  let a : I → ℂ := fun i => q₁ (coordinate S i)
  let b : I → ℂ := fun i => q₂ (coordinate T i)
  have ha : a ∈ S := quotientPoint_mem S hS q₁
  have hb : b ∈ T := quotientPoint_mem T hT q₂
  have hq : q = productEvaluation S T a b ha hb := by
    apply Algebra.TensorProduct.ext
    · apply quotientPoint_ext S
      intro i
      exact (productEvaluation_first S T a b ha hb i).symm
    · apply quotientPoint_ext T
      intro i
      exact (productEvaluation_second S T a b ha hb i).symm
  have hpoint : affineMap q = p.val ≫ (nonorthogonalOpen S T omega).ι :=
    GlobalVelocity.affineMap_specPoint _ _
  have hmem : affineMap q (IsLocalRing.closedPoint ℂ) ∈ nonorthogonalOpen S T omega := by
    rw [hpoint]
    exact (p.val (IsLocalRing.closedPoint ℂ)).property
  have hab : ConePairing.pairing omega a b ≠ 0 := by
    rw [hq] at hmem
    exact (pairPoint_mem_nonorthogonalOpen S T omega a b ha hb (IsLocalRing.closedPoint ℂ)).mp hmem
  refine ⟨a, b, ha, hb, hab, ?_⟩
  rw [nonorthogonalAddition, ← Category.assoc, ← hpoint, hq]
  exact pairPoint_addition S T a b ha hb

end ConePoints

end LeBrunSalamon.Construction.Lines.VelocityAdditionFamily
end
