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

private theorem family_section_equation_transport
    (P : ProjectiveLineOverC) {B : Scheme} (sB : B ⟶ ComplexBase)
    {m : ℕ} (V : ContactFanoManifold m)
    (E : OModule (SelfProduct V.variety.structureMap))
    (sigma : (e : Parametrized.Source P sB ⟶ V.variety.scheme) →
      (he : e ≫ V.variety.structureMap = Parametrized.parameter P sB ≫ sB) →
      AlgebraicSection (pullbackModule
        (ParametrizedContact.evaluationSquare P sB V e he) E))
    {T Y : Scheme} (hT : Parametrized.Square P sB = T)
    (q : Parametrized.Square P sB ⟶ Y) (q' : T ⟶ Y) (hq : HEq q q')
    (f : Y ⟶ SelfProduct V.variety.structureMap)
    (e e' : Parametrized.Source P sB ⟶ V.variety.scheme)
    (he : e ≫ V.variety.structureMap = Parametrized.parameter P sB ≫ sB)
    (he' : e' ≫ V.variety.structureMap = Parametrized.parameter P sB ≫ sB)
    (hee : e = e')
    (r : T ⟶ SelfProduct V.variety.structureMap)
    (hr : HEq (ParametrizedContact.evaluationSquare P sB V e' he') r)
    (h : q ≫ f = ParametrizedContact.evaluationSquare P sB V e he)
    (h' : q' ≫ f = r)
    (s : AlgebraicSection (pullbackModule f E))
    (t : AlgebraicSection (pullbackModule r E))
    (ht : HEq (sigma e' he') t) :
    (pullSection q s ≫
      (compositionPullback q f
        (ParametrizedContact.evaluationSquare P sB V e he) h E).hom = sigma e he) ↔
    (pullSection q' s ≫ (compositionPullback q' f r h' E).hom = t) := by
  cases hT
  have hq' : q = q' := eq_of_heq hq
  cases hq'
  cases hee
  have hr' : ParametrizedContact.evaluationSquare P sB V e he = r := eq_of_heq hr
  cases hr'
  have ht' : sigma e he = t := eq_of_heq ht
  cases ht'
  rfl

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

private theorem family_left_pull_input {T Y : Scheme} (q : T ⟶ Y)
    (f : Y ⟶ SelfProduct X.variety.structureMap)
    (r : T ⟶ SelfProduct X.variety.structureMap) (h : q ≫ f = r)
    (s : AlgebraicSection (MovingPair.leftBundle f).sheaf) :
    (@pullSection T Y q (MovingPair.leftBundle f).sheaf s ≫
      (compositionPullback q f r h (movingPairBundleLeft X.variety X.contact)).hom) =
    (@pullSection T Y q (pullbackModule f (movingPairBundleLeft X.variety X.contact)) s ≫
      (compositionPullback q f r h (movingPairBundleLeft X.variety X.contact)).hom) := by
  rfl

private def arcLeftStoredIff :=
  let heK := (FieldComparison.evaluation_overC (P := Lines.P) (X := X) (F := F)
    (T := Spec (CommRingCat.of (FractionRing Coefficients)))
    (genericPoint ≫ toC) b
    (smoothBase_overC F gamma b hb) (Generic.toFamily F gamma u k)
    (family_isPullback F gamma piM u hu k hk b hb))
  let hqK := (FieldComparison.square_evaluation (P := Lines.P) (X := X) (F := F)
    (T := Spec (CommRingCat.of (FractionRing Coefficients)))
    (genericPoint ≫ toC) b
    (smoothBase_overC F gamma b hb) (Generic.toFamily F gamma u k)
    (family_isPullback F gamma piM u hu k hk b hb)
    (Generic.toSmoothSquare F gamma piM u hu k hk b hb)
    (toSmoothSquare_family F gamma piM u hu k hk b hb))
  (family_section_equation_transport Lines.P (B := (Spec (CommRingCat.of (FractionRing Coefficients)))) (genericPoint ≫ toC) X
    (movingPairBundleLeft X.variety X.contact)
    (fun e he => ParametrizedContact.leftSection Lines.P (B := (Spec (CommRingCat.of (FractionRing Coefficients)))) (genericPoint ≫ toC) X e he)
    (T := RelativeSquare.Space Generic.projection) (Y := F.smoothSquareOpen.toScheme) rfl
    (Generic.toSmoothSquare F gamma piM u hu k hk b hb)
    (Generic.toSmoothSquare F gamma piM u hu k hk b hb) (by rfl)
    (SmoothFamily.smoothEvaluation (F := F))
    (Generic.toFamily F gamma u k ≫ F.evaluation) (genericEvaluation F gamma u k)
    heK
    (genericEvaluation_overC F gamma piM u hu k hk)
    (family_evaluation F gamma u k)
    (genericEvaluationSquare F gamma piM u hu k hk) (by rfl)
    hqK
    (toSmoothSquare_evaluation F gamma piM u hu k hk b hb)
    (SmoothFamily.smoothLeft Q)
    (ParametrizedContact.leftSection Lines.P (genericPoint ≫ toC) X
      (genericEvaluation F gamma u k) (genericEvaluation_overC F gamma piM u hu k hk))
    (by rfl))

private def arcLeftStoredInput :=
  let heK := (FieldComparison.evaluation_overC (P := Lines.P) (X := X) (F := F)
    (T := Spec (CommRingCat.of (FractionRing Coefficients)))
    (genericPoint ≫ toC) b
    (smoothBase_overC F gamma b hb) (Generic.toFamily F gamma u k)
    (family_isPullback F gamma piM u hu k hk b hb))
  let hqK := (FieldComparison.square_evaluation (P := Lines.P) (X := X) (F := F)
    (T := Spec (CommRingCat.of (FractionRing Coefficients)))
    (genericPoint ≫ toC) b
    (smoothBase_overC F gamma b hb) (Generic.toFamily F gamma u k)
    (family_isPullback F gamma piM u hu k hk b hb)
    (Generic.toSmoothSquare F gamma piM u hu k hk b hb)
    (toSmoothSquare_family F gamma piM u hu k hk b hb))
  family_left_pull_input (X := X)
    (T := Parametrized.Square Lines.P (B := (Spec (CommRingCat.of (FractionRing Coefficients)))) (genericPoint ≫ toC))
    (Generic.toSmoothSquare F gamma piM u hu k hk b hb)
    (SmoothFamily.smoothEvaluation (F := F))
    (ParametrizedContact.evaluationSquare Lines.P (B := (Spec (CommRingCat.of (FractionRing Coefficients))))
      (genericPoint ≫ toC) X (Generic.toFamily F gamma u k ≫ F.evaluation) heK)
    hqK (SmoothFamily.smoothLeft Q)

private def arcLeftFieldClosed :=
  letI : Fact (IsField (CommRingCat.of (FractionRing Coefficients))) :=
    ⟨Field.toIsField (FractionRing Coefficients)⟩
  FieldComparison.smoothLeft Q (CommRingCat.of (FractionRing Coefficients))
    (genericPoint ≫ toC) b (smoothBase_overC F gamma b hb)
    (Generic.toFamily F gamma u k) (family_isPullback F gamma piM u hu k hk b hb)
    (Generic.toSmoothSquare F gamma piM u hu k hk b hb)
    (toSmoothSquare_family F gamma piM u hu k hk b hb)

private def arcLeftIncomingClosed :=
  (arcLeftStoredInput (Q := Q) (gamma := gamma) (piM := piM) (u := u) (hu := hu)
    (k := k) (hk := hk) (b := b) (hb := hb)).symm.trans
    (arcLeftFieldClosed (Q := Q) (gamma := gamma) (piM := piM) (u := u) (hu := hu)
    (k := k) (hk := hk) (b := b) (hb := hb))

private def arcLeftTransportedClosed :=
  (arcLeftStoredIff (Q := Q) (gamma := gamma) (piM := piM) (u := u) (hu := hu)
    (k := k) (hk := hk) (b := b) (hb := hb)).mp
    (arcLeftIncomingClosed (Q := Q) (gamma := gamma) (piM := piM) (u := u) (hu := hu)
    (k := k) (hk := hk) (b := b) (hb := hb))

private def arcLeftOutgoingClosed :=
  family_left_pull_input (X := X)
    (Generic.toSmoothSquare F gamma piM u hu k hk b hb)
    (SmoothFamily.smoothEvaluation (F := F))
    (genericEvaluationSquare F gamma piM u hu k hk)
    (toSmoothSquare_evaluation F gamma piM u hu k hk b hb)
    (SmoothFamily.smoothLeft Q)

private def arcLeftFinalClosed :=
  (arcLeftOutgoingClosed (Q := Q) (gamma := gamma) (piM := piM) (u := u) (hu := hu)
    (k := k) (hk := hk) (b := b) (hb := hb)).trans
    (arcLeftTransportedClosed (Q := Q) (gamma := gamma) (piM := piM) (u := u) (hu := hu)
    (k := k) (hk := hk) (b := b) (hb := hb))

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
  exact arcLeftFinalClosed (Q := Q) (gamma := gamma) (piM := piM) (u := u) (hu := hu)
    (k := k) (hk := hk) (b := b) (hb := hb)

private theorem family_right_pull_input {T Y : Scheme} (q : T ⟶ Y)
    (f : Y ⟶ SelfProduct X.variety.structureMap)
    (r : T ⟶ SelfProduct X.variety.structureMap) (h : q ≫ f = r)
    (s : AlgebraicSection (MovingPair.rightBundle f).sheaf) :
    (@pullSection T Y q (MovingPair.rightBundle f).sheaf s ≫
      (compositionPullback q f r h (movingPairBundleRight X.variety X.contact)).hom) =
    (@pullSection T Y q (pullbackModule f (movingPairBundleRight X.variety X.contact)) s ≫
      (compositionPullback q f r h (movingPairBundleRight X.variety X.contact)).hom) := by
  rfl

private def arcRightStoredIff :=
  let heK := (FieldComparison.evaluation_overC (P := Lines.P) (X := X) (F := F)
    (T := Spec (CommRingCat.of (FractionRing Coefficients)))
    (genericPoint ≫ toC) b
    (smoothBase_overC F gamma b hb) (Generic.toFamily F gamma u k)
    (family_isPullback F gamma piM u hu k hk b hb))
  let hqK := (FieldComparison.square_evaluation (P := Lines.P) (X := X) (F := F)
    (T := Spec (CommRingCat.of (FractionRing Coefficients)))
    (genericPoint ≫ toC) b
    (smoothBase_overC F gamma b hb) (Generic.toFamily F gamma u k)
    (family_isPullback F gamma piM u hu k hk b hb)
    (Generic.toSmoothSquare F gamma piM u hu k hk b hb)
    (toSmoothSquare_family F gamma piM u hu k hk b hb))
  (family_section_equation_transport Lines.P (B := (Spec (CommRingCat.of (FractionRing Coefficients)))) (genericPoint ≫ toC) X
    (movingPairBundleRight X.variety X.contact)
    (fun e he => ParametrizedContact.rightSection Lines.P (B := (Spec (CommRingCat.of (FractionRing Coefficients)))) (genericPoint ≫ toC) X e he)
    (T := RelativeSquare.Space Generic.projection) (Y := F.smoothSquareOpen.toScheme) rfl
    (Generic.toSmoothSquare F gamma piM u hu k hk b hb)
    (Generic.toSmoothSquare F gamma piM u hu k hk b hb) (by rfl)
    (SmoothFamily.smoothEvaluation (F := F))
    (Generic.toFamily F gamma u k ≫ F.evaluation) (genericEvaluation F gamma u k)
    heK
    (genericEvaluation_overC F gamma piM u hu k hk)
    (family_evaluation F gamma u k)
    (genericEvaluationSquare F gamma piM u hu k hk) (by rfl)
    hqK
    (toSmoothSquare_evaluation F gamma piM u hu k hk b hb)
    (SmoothFamily.smoothRight Q)
    (ParametrizedContact.rightSection Lines.P (genericPoint ≫ toC) X
      (genericEvaluation F gamma u k) (genericEvaluation_overC F gamma piM u hu k hk))
    (by rfl))

private def arcRightStoredInput :=
  let heK := (FieldComparison.evaluation_overC (P := Lines.P) (X := X) (F := F)
    (T := Spec (CommRingCat.of (FractionRing Coefficients)))
    (genericPoint ≫ toC) b
    (smoothBase_overC F gamma b hb) (Generic.toFamily F gamma u k)
    (family_isPullback F gamma piM u hu k hk b hb))
  let hqK := (FieldComparison.square_evaluation (P := Lines.P) (X := X) (F := F)
    (T := Spec (CommRingCat.of (FractionRing Coefficients)))
    (genericPoint ≫ toC) b
    (smoothBase_overC F gamma b hb) (Generic.toFamily F gamma u k)
    (family_isPullback F gamma piM u hu k hk b hb)
    (Generic.toSmoothSquare F gamma piM u hu k hk b hb)
    (toSmoothSquare_family F gamma piM u hu k hk b hb))
  family_right_pull_input (X := X)
    (T := Parametrized.Square Lines.P (B := (Spec (CommRingCat.of (FractionRing Coefficients)))) (genericPoint ≫ toC))
    (Generic.toSmoothSquare F gamma piM u hu k hk b hb)
    (SmoothFamily.smoothEvaluation (F := F))
    (ParametrizedContact.evaluationSquare Lines.P (B := (Spec (CommRingCat.of (FractionRing Coefficients))))
      (genericPoint ≫ toC) X (Generic.toFamily F gamma u k ≫ F.evaluation) heK)
    hqK (SmoothFamily.smoothRight Q)

private def arcRightFieldClosed :=
  letI : Fact (IsField (CommRingCat.of (FractionRing Coefficients))) :=
    ⟨Field.toIsField (FractionRing Coefficients)⟩
  FieldComparison.smoothRight Q (CommRingCat.of (FractionRing Coefficients))
    (genericPoint ≫ toC) b (smoothBase_overC F gamma b hb)
    (Generic.toFamily F gamma u k) (family_isPullback F gamma piM u hu k hk b hb)
    (Generic.toSmoothSquare F gamma piM u hu k hk b hb)
    (toSmoothSquare_family F gamma piM u hu k hk b hb)

private def arcRightIncomingClosed :=
  (arcRightStoredInput (Q := Q) (gamma := gamma) (piM := piM) (u := u) (hu := hu)
    (k := k) (hk := hk) (b := b) (hb := hb)).symm.trans
    (arcRightFieldClosed (Q := Q) (gamma := gamma) (piM := piM) (u := u) (hu := hu)
    (k := k) (hk := hk) (b := b) (hb := hb))

private def arcRightTransportedClosed :=
  (arcRightStoredIff (Q := Q) (gamma := gamma) (piM := piM) (u := u) (hu := hu)
    (k := k) (hk := hk) (b := b) (hb := hb)).mp
    (arcRightIncomingClosed (Q := Q) (gamma := gamma) (piM := piM) (u := u) (hu := hu)
    (k := k) (hk := hk) (b := b) (hb := hb))

private def arcRightOutgoingClosed :=
  family_right_pull_input (X := X)
    (Generic.toSmoothSquare F gamma piM u hu k hk b hb)
    (SmoothFamily.smoothEvaluation (F := F))
    (genericEvaluationSquare F gamma piM u hu k hk)
    (toSmoothSquare_evaluation F gamma piM u hu k hk b hb)
    (SmoothFamily.smoothRight Q)

private def arcRightFinalClosed :=
  (arcRightOutgoingClosed (Q := Q) (gamma := gamma) (piM := piM) (u := u) (hu := hu)
    (k := k) (hk := hk) (b := b) (hb := hb)).trans
    (arcRightTransportedClosed (Q := Q) (gamma := gamma) (piM := piM) (u := u) (hu := hu)
    (k := k) (hk := hk) (b := b) (hb := hb))

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
  exact arcRightFinalClosed (Q := Q) (gamma := gamma) (piM := piM) (u := u) (hu := hu)
    (k := k) (hk := hk) (b := b) (hb := hb)

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
  change pullSection genericPoint (Transport.section F gamma piM u hu v) ≫
      (compositionPullback genericPoint gamma.val (genericPoint ≫ gamma.val) rfl
        (pullbackModule F.squareEvaluation (movingPairBundleLeft X.variety X.contact))).hom =
    pullSection (genericToSmooth F gamma piM u hu k hk b hb)
      (OpenSection.fromValue F.smoothSquareOpen (SmoothFamily.rationalPair Q).leftSection) ≫
      (compositionPullback (genericToSmooth F gamma piM u hu k hk b hb)
        F.smoothSquareOpen.ι (genericPoint ≫ gamma.val)
        (genericToSmooth_inclusion F gamma piM u hu k hk b hb)
        (pullbackModule F.squareEvaluation (movingPairBundleLeft X.variety X.contact))).hom
  simpa only [SmoothFamily.rationalPair_left_open, SmoothFamily.restrictedLeft] using
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
  change pullSection genericPoint (Transport.section F gamma piM u hu v) ≫
      (compositionPullback genericPoint gamma.val (genericPoint ≫ gamma.val) rfl
        (pullbackModule F.squareEvaluation (movingPairBundleRight X.variety X.contact))).hom =
    pullSection (genericToSmooth F gamma piM u hu k hk b hb)
      (OpenSection.fromValue F.smoothSquareOpen (SmoothFamily.rationalPair Q).rightSection) ≫
      (compositionPullback (genericToSmooth F gamma piM u hu k hk b hb)
        F.smoothSquareOpen.ι (genericPoint ≫ gamma.val)
        (genericToSmooth_inclusion F gamma piM u hu k hk b hb)
        (pullbackModule F.squareEvaluation (movingPairBundleRight X.variety X.contact))).hom
  simpa only [SmoothFamily.rationalPair_right_open, SmoothFamily.restrictedRight] using
    model_normalization F gamma piM u hu k hk b hb v (SmoothFamily.smoothRight Q)
      (ParametrizedContact.rightSection Lines.P (genericPoint ≫ toC) X
        (genericEvaluation F gamma u k) (genericEvaluation_overC F gamma piM u hu k hk))
      hv (smoothRight_normalization Q gamma piM u hu k hk b hb)

end FamilyComparison

end LeBrunSalamon.Construction.FormalArcComparison

end
