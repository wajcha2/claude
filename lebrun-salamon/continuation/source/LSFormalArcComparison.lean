import LSGenericFamilyComparison
import LSArcParametrization
import LSModelGenericComparison
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

section Regularity

variable {g : VeryFreeContactConic Lines.P Lines.marking X}
variable {N : FullConicNeighborhood Lines.P Lines.marking X g}
variable {F : ProjectiveNodalFamily Lines.P Lines.marking
  X.variety X.contact.sequence.line 2}
variable (Q : FullHomComparison Lines.P Lines.marking X.variety N.homSpace N.neighborhood
  X.contact.sequence.line 2 F)
variable (gamma : PointsOver Trait toC F.Square (F.squareToBase ≫ F.toC))

theorem smooth_regular
    (u : Source F (baseArc F gamma) ≅ SmoothModel)
    (hu : u.hom ≫ smoothProjection = parameter F (baseArc F gamma))
    (hU : Dense (gamma.val ⁻¹ᵁ F.smoothSquareOpen : Set Trait)) :
    Regular (SmoothFamily.rationalPair Q).leftRational gamma.val ∧
      Regular (SmoothFamily.rationalPair Q).rightRational gamma.val := by
  constructor
  · exact left_regular_of_model Q gamma smoothProjection u hu smoothGenericParametrization
      smoothGenericParametrization_isPullback hU _ (smooth_model_left F gamma u hu)
  · exact right_regular_of_model Q gamma smoothProjection u hu smoothGenericParametrization
      smoothGenericParametrization_isPullback hU _ (smooth_model_right F gamma u hu)

theorem nodal_regular (S : Smoothing.StandardSource) (a : Coefficients) (ha : a ≠ 0)
    (u : Source F (baseArc F gamma) ≅ Model S a)
    (hu : u.hom ≫ modelProjection S a = parameter F (baseArc F gamma))
    (ell : (TraitPullback.line F (baseArc F gamma)).sheaf ≅
      pullbackModule u.hom (modelLine S a).sheaf)
    (hU : Dense (gamma.val ⁻¹ᵁ F.smoothSquareOpen : Set Trait)) :
    Regular (SmoothFamily.rationalPair Q).leftRational gamma.val ∧
      Regular (SmoothFamily.rationalPair Q).rightRational gamma.val := by
  obtain ⟨c, hc, _⟩ := Nodal.common_exists F gamma S a u hu ell ha
  let k := ModelGenericComparison.genericParametrization S a ha
  let hk := ModelGenericComparison.genericParametrization_isPullback S a ha
  constructor
  · apply left_regular_of_model Q gamma (modelProjection S a) u hu k hk hU
      (RegularModel.leftSection X S a (Transport.evaluation F gamma u)
        (Transport.evaluation_overC F gamma (modelProjection S a) u hu)
        (Transport.line F gamma u ell) c)
    simpa only [Generic.toModelSquare, ModelGenericComparison.parametrizedToModelSquare,
      genericEvaluationSquare, genericEvaluation, ModelGenericComparison.genericEvaluation,
      ModelGenericComparison.genericBase, k] using
      ModelGenericComparison.leftSection_generic S a X (Transport.evaluation F gamma u)
        (Transport.evaluation_overC F gamma (modelProjection S a) u hu)
        (Transport.line F gamma u ell) c hc ha
  · apply right_regular_of_model Q gamma (modelProjection S a) u hu k hk hU
      (RegularModel.rightSection X S a (Transport.evaluation F gamma u)
        (Transport.evaluation_overC F gamma (modelProjection S a) u hu)
        (Transport.line F gamma u ell) c)
    simpa only [Generic.toModelSquare, ModelGenericComparison.parametrizedToModelSquare,
      genericEvaluationSquare, genericEvaluation, ModelGenericComparison.genericEvaluation,
      ModelGenericComparison.genericBase, k] using
      ModelGenericComparison.rightSection_generic S a X (Transport.evaluation F gamma u)
        (Transport.evaluation_overC F gamma (modelProjection S a) u hu)
        (Transport.line F gamma u ell) c hc ha

/-- Both original rational sections are regular on every actual arc
meeting their original smooth domain densely.  The degree-two source
classification supplies exactly the two complete model alternatives. -/
theorem regular (S : Smoothing.StandardSource)
    (hU : Dense (gamma.val ⁻¹ᵁ F.smoothSquareOpen : Set Trait)) :
    Regular (SmoothFamily.rationalPair Q).leftRational gamma.val ∧
      Regular (SmoothFamily.rationalPair Q).rightRational gamma.val := by
  rcases degreeTwo_lineNormalForm S F (baseArc F gamma) (baseArc_dense F gamma hU) with h | h
  · obtain ⟨u, hu, _⟩ := h
    exact smooth_regular Q gamma u hu hU
  · obtain ⟨a, ha, _, u, hu, ⟨ell⟩⟩ := h
    exact nodal_regular Q gamma S a ha u hu ell hU

end Regularity

variable {g : VeryFreeContactConic Lines.P Lines.marking X}
variable {N : FullConicNeighborhood Lines.P Lines.marking X g}
variable {F : ProjectiveNodalFamily Lines.P Lines.marking
  X.variety X.contact.sequence.line 2}
variable (Q : FullHomComparison Lines.P Lines.marking X.variety N.homSpace N.neighborhood
  X.contact.sequence.line 2 F)

/-- The actual left moving-pair section has no pole on a formal arc. -/
theorem left_regular (S : Smoothing.StandardSource)
    (gamma : PointsOver Trait toC F.Square (F.squareToBase ≫ F.toC))
    (hU : Dense (gamma.val ⁻¹ᵁ F.smoothSquareOpen : Set Trait)) :
    Regular (SmoothFamily.rationalPair Q).leftRational gamma.val :=
  (regular Q gamma S hU).1

/-- The actual right moving-pair section has no pole on a formal arc. -/
theorem right_regular (S : Smoothing.StandardSource)
    (gamma : PointsOver Trait toC F.Square (F.squareToBase ≫ F.toC))
    (hU : Dense (gamma.val ⁻¹ᵁ F.smoothSquareOpen : Set Trait)) :
    Regular (SmoothFamily.rationalPair Q).rightRational gamma.val :=
  (regular Q gamma S hU).2

end LeBrunSalamon.Construction.FormalArcComparison

end
