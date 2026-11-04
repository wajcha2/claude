import LSTwoPointDeformationInterpolationProbe
import LSHomMarkedEvaluationDeformationProfile

/-! Actual two-marked evaluation on Hom parameter lifts. This isolated
composition retains the original central curve and both marked points.
Its imported interpolation uses the existing published-input boundary;
this file adds no admission and makes no original-obligation claim. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirty
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.Construction.Lines
open LeBrunSalamon.Next3i.HomPointDeformations
open LeBrunSalamon.Next3i.HomMarkedEvaluation
open LeBrunSalamon.Next3i.TwoPointDeformations

namespace LeBrunSalamon.Next3i.TwoMarkedHomLifts

theorem pointDeformation_injective {Y : Scheme} {sY : Y ⟶ ComplexBase}
    {y : PointsOver ComplexBase (𝟙 ComplexBase) Y sY} :
    Function.Injective (SourceTangent.pointDeformation (y := y)) := by
  intro v w h
  apply pointLift_ext
  have hm := congrArg (fun E : FamilyVariation.Deformation (𝟙 ComplexBase) sY y.val =>
    LocalVelocityComparison.dualBaseInclusion ≫ E.map) h
  simpa only [SourceTangent.pointDeformation_onDual] using hm

/-- Arbitrary first-order motions at two distinct marked target points
are obtained from one actual infinitesimal Hom parameter. -/
theorem twoMarkedEvaluatedLifts_surjective (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H : HomSpacePresentation P X)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)
    (hgen : IsTwoPointGloballyGenerated P
      (pullbackModule (H.mapAt P t) (tangentSheaf X.structureMap)))
    (p q : ProjectiveLinePoint P) (hpq : p.map ≠ q.map) :
    Function.Surjective (fun v : Infinitesimal.PointLift H.parameter H.toC t =>
      (evaluatedLift P p H t v, evaluatedLift P q H t v)) := by
  rintro ⟨τp, τq⟩
  have hf : H.mapAt P t ≫ X.structureMap = P.structureMap := by
    change (HomDeformation.sourceAtPoint P t ≫ H.evaluation) ≫ X.structureMap = _
    rw [Category.assoc, H.overC, ← Category.assoc,
      HomDeformation.sourceAtPoint_fst, Category.id_comp]
  obtain ⟨D, hD⟩ := twoPointDeformations_surjective P X (H.mapAt P t) hf hgen p q hpq
    (SourceTangent.pointDeformation τp, SourceTangent.pointDeformation τq)
  obtain ⟨v, hv⟩ := deformationOfLift_surjective P H t D
  refine ⟨v, Prod.ext ?_ ?_⟩
  · apply pointDeformation_injective
    rw [← deformationOfLift_marked P p H t v, hv]
    exact congrArg Prod.fst hD
  · apply pointDeformation_injective
    rw [← deformationOfLift_marked P q H t v, hv]
    exact congrArg Prod.snd hD

end LeBrunSalamon.Next3i.TwoMarkedHomLifts

#print axioms LeBrunSalamon.Next3i.TwoMarkedHomLifts.pointDeformation_injective
#print axioms LeBrunSalamon.Next3i.TwoMarkedHomLifts.twoMarkedEvaluatedLifts_surjective

end
