import LSGenericFamilyComparison
import LSArcParametrization
import LSRationalOpenTransport
import LSFormalArcModelTransport

/-!
# Regularity of the descended moving pair on every actual formal arc

Both complete source normal forms carry regular model sections.  Their
whole generic squares agree with the original parametrized tensors.
The arbitrary-field comparison identifies those tensors with the
descended smooth-family sections; the actual two marked points then
identify their generic values.  Finally the actual-open transport
theorem gives regularity in the original `FormalArcs.Regular` sense.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction.FormalArcComparison

local notation "Model" => LeBrunSalamon.Construction.StableMaps.FormalArcs.Model

open StableMaps StableMaps.FormalArcs StableMaps.TraitPullback
open FamilyBivectors FormalArcSections TraitContact

variable {n : ℕ} {X : ContactFanoManifold n}

section FamilyComparison

variable {g : VeryFreeContactConic Lines.P Lines.marking X}
variable {N : FullConicNeighborhood Lines.P Lines.marking X g}
variable {F : ProjectiveNodalFamily Lines.P Lines.marking
  X.variety X.contact.sequence.line 2}
variable (Q : FullHomComparison Lines.P Lines.marking X.variety N.homSpace N.neighborhood
  X.contact.sequence.line 2 F)
variable (gamma : PointsOver Trait toC F.Square (F.squareToBase ≫ F.toC))
variable {M : Scheme} (piM : M ⟶ Trait)
variable (u : Source F (baseArc F gamma) ≅ M)
variable (hu : u.hom ≫ piM = parameter F (baseArc F gamma))
variable (k : Generic.P1 ⟶ M)
variable (hk : IsPullback k Generic.projection piM genericPoint)
variable (b : GenericPoint ⟶ F.smoothOpen.toScheme)
variable (hb : b ≫ F.smoothOpen.ι = genericPoint ≫ (baseArc F gamma).val)

theorem smoothLeft_normalization :
    pullSection (Generic.toSmoothSquare F gamma piM u hu k hk b hb)
      (SmoothFamily.smoothLeft Q) ≫
      (compositionPullback (Generic.toSmoothSquare F gamma piM u hu k hk b hb)
        (SmoothFamily.smoothEvaluation (F := F))
        (genericEvaluationSquare F gamma piM u hu k hk)
        (toSmoothSquare_evaluation F gamma piM u hu k hk b hb)
        (movingPairBundleLeft X.variety X.contact)).hom =
      ParametrizedContact.leftSection Lines.P (genericPoint ≫ toC) X
        (genericEvaluation F gamma u k) (genericEvaluation_overC F gamma piM u hu k hk) := by
  letI : Fact (IsField (CommRingCat.of (FractionRing Coefficients))) :=
    ⟨Field.toIsField (FractionRing Coefficients)⟩
  have h := FieldComparison.smoothLeft Q (CommRingCat.of (FractionRing Coefficients))
    (genericPoint ≫ toC) b (smoothBase_overC F gamma b hb)
    (Generic.toFamily F gamma u k) (family_isPullback F gamma piM u hu k hk b hb)
    (Generic.toSmoothSquare F gamma piM u hu k hk b hb)
    (toSmoothSquare_family F gamma piM u hu k hk b hb)
  simpa only [genericEvaluationSquare, genericEvaluation, Generic.toFamily,
    Generic.inverseSource, Transport.evaluation, TraitPullback.evaluation, Category.assoc] using h

theorem smoothRight_normalization :
    pullSection (Generic.toSmoothSquare F gamma piM u hu k hk b hb)
      (SmoothFamily.smoothRight Q) ≫
      (compositionPullback (Generic.toSmoothSquare F gamma piM u hu k hk b hb)
        (SmoothFamily.smoothEvaluation (F := F))
        (genericEvaluationSquare F gamma piM u hu k hk)
        (toSmoothSquare_evaluation F gamma piM u hu k hk b hb)
        (movingPairBundleRight X.variety X.contact)).hom =
      ParametrizedContact.rightSection Lines.P (genericPoint ≫ toC) X
        (genericEvaluation F gamma u k) (genericEvaluation_overC F gamma piM u hu k hk) := by
  letI : Fact (IsField (CommRingCat.of (FractionRing Coefficients))) :=
    ⟨Field.toIsField (FractionRing Coefficients)⟩
  have h := FieldComparison.smoothRight Q (CommRingCat.of (FractionRing Coefficients))
    (genericPoint ≫ toC) b (smoothBase_overC F gamma b hb)
    (Generic.toFamily F gamma u k) (family_isPullback F gamma piM u hu k hk b hb)
    (Generic.toSmoothSquare F gamma piM u hu k hk b hb)
    (toSmoothSquare_family F gamma piM u hu k hk b hb)
  simpa only [genericEvaluationSquare, genericEvaluation, Generic.toFamily,
    Generic.inverseSource, Transport.evaluation, TraitPullback.evaluation, Category.assoc] using h

theorem left_regular_of_model
    (hU : Dense (gamma.val ⁻¹ᵁ F.smoothSquareOpen : Set Trait))
    (v : AlgebraicSection (pullbackModule (Transport.evaluationSquare F gamma piM u hu)
      (movingPairBundleLeft X.variety X.contact)))
    (hv : pullSection (Generic.toModelSquare piM k hk) v ≫
      (compositionPullback (Generic.toModelSquare piM k hk)
        (Transport.evaluationSquare F gamma piM u hu)
        (genericEvaluationSquare F gamma piM u hu k hk)
        (toModelSquare_evaluation F gamma piM u hu k hk)
        (movingPairBundleLeft X.variety X.contact)).hom =
      ParametrizedContact.leftSection Lines.P (genericPoint ≫ toC) X
        (genericEvaluation F gamma u k) (genericEvaluation_overC F gamma piM u hu k hk)) :
    Regular (SmoothFamily.rationalPair Q).leftRational gamma.val := by
  obtain ⟨b, hb⟩ := generic_factor_of_dense F (baseArc F gamma) (baseArc_dense F gamma hU)
  apply regular_of_normalized_generic_comparison (MovingPair.leftBundle F.squareEvaluation)
    (SmoothFamily.rationalPair Q).leftRational gamma.val hU
    (Transport.section F gamma piM u hu v)
    (genericToSmooth F gamma piM u hu k hk b hb)
    (genericToSmooth_inclusion F gamma piM u hu k hk b hb)
  simpa only [MovingPair.RationalVectorPair.leftRational,
    SmoothFamily.rationalPair_left_open, SmoothFamily.restrictedLeft] using
    model_normalization F gamma piM u hu k hk b hb v (SmoothFamily.smoothLeft Q)
      (ParametrizedContact.leftSection Lines.P (genericPoint ≫ toC) X
        (genericEvaluation F gamma u k) (genericEvaluation_overC F gamma piM u hu k hk))
      hv (smoothLeft_normalization Q gamma piM u hu k hk b hb)

theorem right_regular_of_model
    (hU : Dense (gamma.val ⁻¹ᵁ F.smoothSquareOpen : Set Trait))
    (v : AlgebraicSection (pullbackModule (Transport.evaluationSquare F gamma piM u hu)
      (movingPairBundleRight X.variety X.contact)))
    (hv : pullSection (Generic.toModelSquare piM k hk) v ≫
      (compositionPullback (Generic.toModelSquare piM k hk)
        (Transport.evaluationSquare F gamma piM u hu)
        (genericEvaluationSquare F gamma piM u hu k hk)
        (toModelSquare_evaluation F gamma piM u hu k hk)
        (movingPairBundleRight X.variety X.contact)).hom =
      ParametrizedContact.rightSection Lines.P (genericPoint ≫ toC) X
        (genericEvaluation F gamma u k) (genericEvaluation_overC F gamma piM u hu k hk)) :
    Regular (SmoothFamily.rationalPair Q).rightRational gamma.val := by
  obtain ⟨b, hb⟩ := generic_factor_of_dense F (baseArc F gamma) (baseArc_dense F gamma hU)
  apply regular_of_normalized_generic_comparison (MovingPair.rightBundle F.squareEvaluation)
    (SmoothFamily.rationalPair Q).rightRational gamma.val hU
    (Transport.section F gamma piM u hu v)
    (genericToSmooth F gamma piM u hu k hk b hb)
    (genericToSmooth_inclusion F gamma piM u hu k hk b hb)
  simpa only [MovingPair.RationalVectorPair.rightRational,
    SmoothFamily.rationalPair_right_open, SmoothFamily.restrictedRight] using
    model_normalization F gamma piM u hu k hk b hb v (SmoothFamily.smoothRight Q)
      (ParametrizedContact.rightSection Lines.P (genericPoint ≫ toC) X
        (genericEvaluation F gamma u k) (genericEvaluation_overC F gamma piM u hu k hk))
      hv (smoothRight_normalization Q gamma piM u hu k hk b hb)

end FamilyComparison

end LeBrunSalamon.Construction.FormalArcComparison

end
