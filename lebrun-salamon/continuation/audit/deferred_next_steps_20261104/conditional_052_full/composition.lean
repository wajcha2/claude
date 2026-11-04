import LSTwoPointProductLiftProbe
import LSFixedMarkingsTwoPointEvaluation
import LSSmoothRestrictionDensity
import LSConnectedSmoothIntegralCompositionV4

/-! Conditional composition of the original two-point dominance conclusion.
Only four generic published criteria remain explicit parameters. This is an
isolated local prototype, not a production replacement or accepted unit. -/

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
open LeBrunSalamon.Next3i.TwoPointProductLifts
open LeBrunSalamon.Next3i.IntegralityComposition

namespace LeBrunSalamon.Next3i.TwoPointDominance

/-- The complex specialization of the generic rational-point tangent-lift
criterion reviewed in3h, expressed using the project's identical dual ring.
It mentions no Hom space, rational curve, contact geometry, or dominance. -/
def ComplexTangentLiftCriterion : Prop :=
  ∀ (A B : Scheme) (sA : A ⟶ ComplexBase) (sB : B ⟶ ComplexBase)
    (F : A ⟶ B), F ≫ sB = sA →
    ∀ (a : ComplexBase ⟶ A), a ≫ sA = 𝟙 ComplexBase →
    Smooth sA → Smooth sB →
    (∀ b : Infinitesimal.DualScheme ⟶ B,
      b ≫ sB = Infinitesimal.dualToC → Infinitesimal.origin ≫ b = a ≫ F →
      ∃ l : Infinitesimal.DualScheme ⟶ A,
        l ≫ sA = Infinitesimal.dualToC ∧ Infinitesimal.origin ≫ l = a ∧ l ≫ F = b) →
    ∃ V : A.Opens, Set.range a ⊆ V ∧ Smooth (V.ι ≫ F)

/-- Preserve every original geometric hypothesis and the actual evaluation.
The generic criteria are explicit; the original052/054/057 admissions are not
used. Fixed source markings avoid needing smoothness of the full source. -/
theorem homOpen_twoPointEvaluation_dominant_from_generic_criteria
    (hconnected : ConnectedFieldCriterion.{0})
    (hnormal : SmoothNormalCriterion.{0})
    (hintegral : NormalConnectedCriterion.{0})
    (hcriterion : ComplexTangentLiftCriterion)
    (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) (H : HomSpacePresentation P X)
    (U : H.parameter.Opens) (hU : Smooth (U.ι ≫ H.toC))
    (t : PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ H.toC))
    (f : RationalCurve P X)
    (hf : f.map = H.mapAt P
      ⟨t.val ≫ U.ι, by simpa only [Category.assoc] using t.property⟩)
    (hfree : IsVeryFreeRationalCurve P X (intrinsicTangentBundle X) f) :
    DenseRange (Refinement.HomTwoPointEvaluation.evaluation P H U).base := by
  let u := Refinement.HomTwoPointEvaluation.parameterPoint P H U t
  have hgen : IsTwoPointGloballyGenerated P
      (pullbackModule (H.mapAt P u) (tangentSheaf X.structureMap)) := by
    change IsTwoPointGloballyGenerated P
      (pullbackModule f.map (tangentSheaf X.structureMap)) at hfree
    rw [hf] at hfree
    exact hfree
  obtain ⟨p, q, hpq⟩ := hgen.1
  let F := FixedMarkings.pairedEvaluation P p q H
  let sZ := firstProjection X.structureMap ≫ X.structureMap
  have hF : F ≫ sZ = H.toC := FixedMarkings.pairedEvaluation_overC P p q H
  have hopen : (U.ι ≫ F) ≫ sZ = U.ι ≫ H.toC := by rw [Category.assoc, hF]
  let z : PointsOver ComplexBase (𝟙 ComplexBase) (SelfProduct X.structureMap) sZ :=
    ⟨t.val ≫ (U.ι ≫ F), by rw [Category.assoc, hopen, t.property]⟩
  have hz : u.val ≫ F = z.val := by
    change (t.val ≫ U.ι) ≫ F = t.val ≫ (U.ι ≫ F)
    exact Category.assoc _ _ _
  have hlifts : ∀ b : Infinitesimal.DualScheme ⟶ SelfProduct X.structureMap,
      b ≫ sZ = Infinitesimal.dualToC →
      Infinitesimal.origin ≫ b = t.val ≫ (U.ι ≫ F) →
      ∃ a : Infinitesimal.DualScheme ⟶ U.toScheme,
        a ≫ (U.ι ≫ H.toC) = Infinitesimal.dualToC ∧
        Infinitesimal.origin ≫ a = t.val ∧ a ≫ (U.ι ≫ F) = b := by
    intro b hb hc
    let τ : Infinitesimal.PointLift (SelfProduct X.structureMap) sZ z := ⟨b, hb, hc⟩
    obtain ⟨v, hv⟩ := product_evaluation_lifts P H u hgen p q hpq F
      (FixedMarkings.pairedEvaluation_first P p q H)
      (FixedMarkings.pairedEvaluation_second P p q H) z hz τ
    obtain ⟨w, hw⟩ := lift_in_open_with_composite H.toC U t F b v hv
    exact ⟨w.map, w.overC, w.reduces, hw⟩
  have hsmooth : ∃ V : U.toScheme.Opens,
      Set.range t.val ⊆ V ∧ Smooth (V.ι ≫ (U.ι ≫ F)) :=
    hcriterion U.toScheme (SelfProduct X.structureMap) (U.ι ≫ H.toC) sZ
      (U.ι ≫ F) hopen t.val t.property hU inferInstance hlifts
  letI : IrreducibleSpace (SelfProduct X.structureMap : Scheme) :=
    complex_selfProduct_irreducible hconnected hnormal hintegral X.structureMap
  have hdense : DenseRange (U.ι ≫ F).base :=
    SmoothRestrictionDensity.denseRange_of_smooth_pointMap_neighborhood
      (U.ι ≫ F) t.val hsmooth
  exact FixedMarkings.denseRange_of_markedPair P p q H U hdense

end LeBrunSalamon.Next3i.TwoPointDominance

#print axioms LeBrunSalamon.Next3i.TwoPointDominance.homOpen_twoPointEvaluation_dominant_from_generic_criteria

end
