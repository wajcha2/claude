import LSConicMappedMixedProbe

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTen
open LeBrunSalamon.PhaseFourteen LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton
open LeBrunSalamon.Refinement LeBrunSalamon.Refinement.Jets
open LeBrunSalamon.Construction LeBrunSalamon.Construction.Lines

-- These are existing type aliases. Expose their projections to rewrite
-- matching, so the actual chart rings and projective-line scheme agree.
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety PointFrame.ChartRing
  identityCurveContact intrinsicTangentBundle

set_option maxHeartbeats 250000
set_option diagnostics true
namespace LeBrunSalamon.Refinement

namespace SourceReparamProof

open ConicJetProof

theorem normalized_point_quadratic {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    {C : IntrinsicContactStructure X} (K : NormalizedContactKernel X C)
    {x : ComplexPoint X} (F : PointFrame X C.sequence.line x) (A : ContactAtPoint C F)
    (w : TangentFiber X x) :
    (∑ i, (F.fiberEquiv w).val (F.coefficient (K.expansion.left i)) *
      (F.fiberEquiv w).val (F.coefficient (K.expansion.right i))) +
      2 * (A.theta (F.fiberEquiv w)) ^ 2 = 0 := by
  obtain ⟨v, hv⟩ := F.evaluateVector_surjective (F.fiberEquiv w)
  have hm := congrArg F.evaluation
    (K.expansion.mixedSecond_eq_neg_of_orderTwo K.orderTwo F.frame v v)
  rw [K.expansion_normalized F.frame v v] at hm
  have hsum : (∑ i, (F.evaluateVector v).val (F.coefficient (K.expansion.left i)) *
      (F.evaluateVector v).val (F.coefficient (K.expansion.right i))) =
      F.evaluation (K.expansion.mixedSecond F.frame v v) := by
    simp only [ExternalExpansion.mixedSecond, map_sum, map_mul]
    rfl
  rw [← hv, A.theta_normalized, hsum]
  simp only [map_neg, map_mul, map_ofNat] at hm
  linear_combination hm


end SourceReparamProof
end LeBrunSalamon.Refinement
end
