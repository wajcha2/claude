import LSFamilyDescentReparametrization
import LSOpenSectionTransport
import LSFamilySmoothCoordinates

/-!
# Open-section comparison and smooth-family descent of the actual tensors.

This namespace block is extracted verbatim from the candidate descent
source. Public names, statements and proof bodies are retained. The preceding
transport blocks are imported so each completed native output can be reused.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.PhaseTwentyEight.ExternalExchangeCoherenceProof

namespace LeBrunSalamon.Construction.FamilyBivectors


-- Normalize the existing P1/contact carrier aliases for the same actual maps.
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety identityCurveContact intrinsicTangentBundle

namespace SmoothFamily

variable {P : ProjectiveLineOverC} {p : ProjectiveLinePoint P}
variable {n : ℕ} {X : ContactFanoManifold n} {g : VeryFreeContactConic P p X}
variable {N : FullConicNeighborhood P p X g}
variable {F : StableMaps.ProjectiveNodalFamily P p X.variety X.contact.sequence.line 2}
variable (Q : StableMaps.FullHomComparison P p X.variety N.homSpace N.neighborhood
  X.contact.sequence.line 2 F)

/-- The two values on an actual double fibre agree after the canonical
identification of their target fibres. -/
theorem left_point_values (t₀ t₁ : Point Q)
    (h : t₀.val ≫ Q.parametrizedSquareToSmooth =
      t₁.val ≫ Q.parametrizedSquareToSmooth) :
    pullSection t₀.val (left Q) ≫
      (compositionPullback t₀.val (parametrizedEvaluation Q)
        (t₁.val ≫ parametrizedEvaluation Q) (same_evaluation Q t₀ t₁ h)
        (movingPairBundleLeft X.variety X.contact)).hom =
    pullSection t₁.val (left Q) ≫
      (compositionPullback t₁.val (parametrizedEvaluation Q)
        (t₁.val ≫ parametrizedEvaluation Q) rfl
        (movingPairBundleLeft X.variety X.contact)).hom := by
  let e := Q.complexTransition (coverPoint Q t₀) (coverPoint Q t₁) (same_base Q t₀ t₁ h)
  have he : e.hom ≫ P.structureMap = P.structureMap := Q.complexTransition_overC _ _ _
  have hz₀ := (coordinatePair_evaluation Q t₀).trans (same_evaluation Q t₀ t₁ h)
  have hz₁ := coordinatePair_evaluation Q t₁
  rw [point_left Q t₀ _ (same_evaluation Q t₀ t₁ h) hz₀,
    point_left Q t₁ _ rfl hz₁]
  exact (SectionTransport.pull_specialization (coordinatePair Q t₀)
    (curveSquareMap P (Reparametrization.curve P e he))
    (curveSquareMap P (curve Q (coverPoint Q t₁))) (coordinatePair Q t₁)
    (curveSquareMap P (curve Q (coverPoint Q t₀))) (t₁.val ≫ parametrizedEvaluation Q)
    (transition_coordinates Q t₀ t₁ h)
    (Reparametrization.square_comp P e he X (curve Q (coverPoint Q t₁))
      (curve Q (coverPoint Q t₀)) (transition_curves Q t₀ t₁ h)) hz₀ hz₁
    (Curve.leftSection P X (curve Q (coverPoint Q t₁)))
    (Curve.leftSection P X (curve Q (coverPoint Q t₀)))
    (Reparametrization.leftSection P e he X (curve Q (coverPoint Q t₁))
      (curve Q (coverPoint Q t₀)) (transition_curves Q t₀ t₁ h))).symm

theorem right_point_values (t₀ t₁ : Point Q)
    (h : t₀.val ≫ Q.parametrizedSquareToSmooth =
      t₁.val ≫ Q.parametrizedSquareToSmooth) :
    pullSection t₀.val (right Q) ≫
      (compositionPullback t₀.val (parametrizedEvaluation Q)
        (t₁.val ≫ parametrizedEvaluation Q) (same_evaluation Q t₀ t₁ h)
        (movingPairBundleRight X.variety X.contact)).hom =
    pullSection t₁.val (right Q) ≫
      (compositionPullback t₁.val (parametrizedEvaluation Q)
        (t₁.val ≫ parametrizedEvaluation Q) rfl
        (movingPairBundleRight X.variety X.contact)).hom := by
  let e := Q.complexTransition (coverPoint Q t₀) (coverPoint Q t₁) (same_base Q t₀ t₁ h)
  have he : e.hom ≫ P.structureMap = P.structureMap := Q.complexTransition_overC _ _ _
  have hz₀ := (coordinatePair_evaluation Q t₀).trans (same_evaluation Q t₀ t₁ h)
  have hz₁ := coordinatePair_evaluation Q t₁
  rw [point_right Q t₀ _ (same_evaluation Q t₀ t₁ h) hz₀,
    point_right Q t₁ _ rfl hz₁]
  exact (SectionTransport.pull_specialization (coordinatePair Q t₀)
    (curveSquareMap P (Reparametrization.curve P e he))
    (curveSquareMap P (curve Q (coverPoint Q t₁))) (coordinatePair Q t₁)
    (curveSquareMap P (curve Q (coverPoint Q t₀))) (t₁.val ≫ parametrizedEvaluation Q)
    (transition_coordinates Q t₀ t₁ h)
    (Reparametrization.square_comp P e he X (curve Q (coverPoint Q t₁))
      (curve Q (coverPoint Q t₀)) (transition_curves Q t₀ t₁ h)) hz₀ hz₁
    (Curve.rightSection P X (curve Q (coverPoint Q t₁)))
    (Curve.rightSection P X (curve Q (coverPoint Q t₀)))
    (Reparametrization.rightSection P e he X (curve Q (coverPoint Q t₁))
      (curve Q (coverPoint Q t₀)) (transition_curves Q t₀ t₁ h))).symm


end SmoothFamily

end LeBrunSalamon.Construction.FamilyBivectors

end
