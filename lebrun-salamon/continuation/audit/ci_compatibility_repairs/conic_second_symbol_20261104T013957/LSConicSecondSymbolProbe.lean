import LSConicHessianPrefix

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

/-- SOURCE jet:second-symbol. Lower symbols vanish first, so the
curve acceleration contributes zero. The undivided Hessian equals 2 theta^2. -/
theorem fullFamily_secondSymbol (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X)
    (D : FamilyKernel P p X g) (h1 : FamilyKernel.HasZeroFirstSymbol P p D) :
    HasNormalizedContactSymbol X.contact D.kernel := by
  classical
  obtain ⟨E⟩ := externalExpansion_exists X.variety X.contact.sequence.line D.kernel
  refine ⟨E, ?_⟩
  intro F u v
  apply sub_eq_zero.mp
  apply ConicJetProof.function_zero_on_full_family P p X g D.family F.openSet
  intro t r q hq
  let x : ComplexPoint X.variety := ⟨q ≫ F.openSet.ι, by
    rw [hq, Category.assoc, (D.family.curveAt t).overC, r.overC]⟩
  let Fp : PointFrame X.variety X.contact.sequence.line x := ⟨F, q, rfl⟩
  obtain ⟨A⟩ := contactAtPoint_exists X.contact Fp
  obtain ⟨G, hG⟩ := GlobalVelocity.targetChart_exists_inside X.variety x F.openSet (by
    rintro _ ⟨z, rfl⟩
    exact Fp.pointSupport trivial)
  have hdef := ConicJetProof.frameDefect_zero_on_curve P p X g D E t r x
    hq.symm Fp A G hG
  have hh := ConicJetProof.pointHessian_of_defect_zero E h1 Fp A G hG hdef u v
  change Fp.evaluation (E.secondSlotSecond F u v -
    2 * localContactValue X.contact F u * localContactValue X.contact F v) = 0
  rw [map_sub, map_mul, map_mul, map_ofNat, hh]
  ring


end LeBrunSalamon.Refinement
end
