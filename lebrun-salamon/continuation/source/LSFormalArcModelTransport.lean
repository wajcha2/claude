import LSFormalArcModelNormalization
import LSParametrizedBaseChange

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

abbrev smoothGenericParametrization : Generic.P1 ⟶ SmoothModel :=
  Parametrized.baseChangeSource Lines.P (genericPoint ≫ toC) toC genericPoint rfl

theorem smoothGenericParametrization_isPullback :
    IsPullback smoothGenericParametrization Generic.projection smoothProjection genericPoint :=
  Parametrized.baseChangeSource_isPullback Lines.P (genericPoint ≫ toC) toC genericPoint rfl

section SmoothModel

variable (F : ProjectiveNodalFamily Lines.P Lines.marking
  X.variety X.contact.sequence.line 2)
variable (gamma : PointsOver Trait toC F.Square (F.squareToBase ≫ F.toC))
variable (u : Source F (baseArc F gamma) ≅ SmoothModel)
variable (hu : u.hom ≫ smoothProjection = parameter F (baseArc F gamma))

private theorem smooth_equation_transport {T T' Y Y' Z : Scheme}
    (hT : T = T') (hY : Y = Y')
    (k : T ⟶ Y) (k' : T' ⟶ Y') (hk : HEq k k')
    (f : Y ⟶ Z) (f' : Y' ⟶ Z) (hf : HEq f f')
    (r : T ⟶ Z) (r' : T' ⟶ Z) (hr : HEq r r')
    (h : k ≫ f = r) (h' : k' ≫ f' = r') (E : OModule Z)
    (s : AlgebraicSection (pullbackModule f E))
    (s' : AlgebraicSection (pullbackModule f' E)) (hs : HEq s s')
    (t : AlgebraicSection (pullbackModule r E))
    (t' : AlgebraicSection (pullbackModule r' E)) (ht : HEq t t') :
    (pullSection k s ≫ (compositionPullback k f r h E).hom = t) ↔
      (pullSection k' s' ≫ (compositionPullback k' f' r' h' E).hom = t') := by
  cases hT
  cases hY
  have hk' : k = k' := eq_of_heq hk
  cases hk'
  have hf' : f = f' := eq_of_heq hf
  cases hf'
  have hr' : r = r' := eq_of_heq hr
  cases hr'
  have hs' : s = s' := eq_of_heq hs
  cases hs'
  have ht' : t = t' := eq_of_heq ht
  cases ht'
  rfl

private theorem smooth_source_square_eq : (Parametrized.Square Lines.P (genericPoint ≫ toC)) = (RelativeSquare.Space Generic.projection) := by rfl

private theorem smooth_middle_square_eq : (Parametrized.Square Lines.P toC) = (RelativeSquare.Space smoothProjection) := by rfl

private theorem smooth_square_map_heq :
    @HEq ((Parametrized.Square Lines.P (genericPoint ≫ toC)) ⟶ (Parametrized.Square Lines.P toC)) (Generic.toModelSquare smoothProjection smoothGenericParametrization smoothGenericParametrization_isPullback) ((RelativeSquare.Space Generic.projection) ⟶ (RelativeSquare.Space smoothProjection)) (Generic.toModelSquare smoothProjection smoothGenericParametrization smoothGenericParametrization_isPullback) := by rfl

private theorem smooth_model_evaluation_heq :
    @HEq ((Parametrized.Square Lines.P toC) ⟶ (SelfProduct X.variety.structureMap)) (ParametrizedContact.evaluationSquare Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) ((RelativeSquare.Space smoothProjection) ⟶ (SelfProduct X.variety.structureMap)) (Transport.evaluationSquare F gamma smoothProjection u hu) := by rfl

private theorem smooth_generic_evaluation_heq :
    @HEq ((Parametrized.Square Lines.P (genericPoint ≫ toC)) ⟶ (SelfProduct X.variety.structureMap)) (ParametrizedContact.evaluationSquare Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u smoothGenericParametrization) (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback)) ((RelativeSquare.Space Generic.projection) ⟶ (SelfProduct X.variety.structureMap)) (genericEvaluationSquare F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback) := by rfl

private theorem smooth_left_section_heq :
    @HEq (AlgebraicSection (@pullbackModule (Parametrized.Square Lines.P toC) (SelfProduct X.variety.structureMap) (ParametrizedContact.evaluationSquare Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) (movingPairBundleLeft X.variety X.contact)))
      (ParametrizedContact.leftSection Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu))
      (AlgebraicSection (@pullbackModule (RelativeSquare.Space smoothProjection) (SelfProduct X.variety.structureMap) (Transport.evaluationSquare F gamma smoothProjection u hu) (movingPairBundleLeft X.variety X.contact)))
      (ParametrizedContact.leftSection Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) := by rfl

private theorem smooth_left_result_heq :
    @HEq (AlgebraicSection (@pullbackModule (Parametrized.Square Lines.P (genericPoint ≫ toC)) (SelfProduct X.variety.structureMap) (ParametrizedContact.evaluationSquare Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u smoothGenericParametrization) (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback)) (movingPairBundleLeft X.variety X.contact)))
      (ParametrizedContact.leftSection Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u smoothGenericParametrization) (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback))
      (AlgebraicSection (@pullbackModule (RelativeSquare.Space Generic.projection) (SelfProduct X.variety.structureMap) (genericEvaluationSquare F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback) (movingPairBundleLeft X.variety X.contact)))
      (ParametrizedContact.leftSection Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u smoothGenericParametrization) (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback)) := by rfl

private theorem smooth_left_canonical :
    @pullSection (Parametrized.Square Lines.P (genericPoint ≫ toC)) (Parametrized.Square Lines.P toC) (Generic.toModelSquare smoothProjection smoothGenericParametrization smoothGenericParametrization_isPullback)
      (@pullbackModule (Parametrized.Square Lines.P toC) (SelfProduct X.variety.structureMap) (ParametrizedContact.evaluationSquare Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) (movingPairBundleLeft X.variety X.contact)) (ParametrizedContact.leftSection Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) ≫
      (@compositionPullback (Parametrized.Square Lines.P (genericPoint ≫ toC)) (Parametrized.Square Lines.P toC) (SelfProduct X.variety.structureMap)
        (Generic.toModelSquare smoothProjection smoothGenericParametrization smoothGenericParametrization_isPullback) (ParametrizedContact.evaluationSquare Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) (ParametrizedContact.evaluationSquare Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u smoothGenericParametrization) (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback)) (toModelSquare_evaluation F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback) (movingPairBundleLeft X.variety X.contact)).hom = (ParametrizedContact.leftSection Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u smoothGenericParametrization) (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback)) :=
  ParametrizedContact.leftSection_baseChange Lines.P (genericPoint ≫ toC) toC genericPoint rfl
    smoothGenericParametrization
    (Parametrized.baseChangeSource_first Lines.P (genericPoint ≫ toC) toC genericPoint rfl)
    (Parametrized.baseChangeSource_parameter Lines.P (genericPoint ≫ toC) toC genericPoint rfl)
    X (Transport.evaluation F gamma u)
    (Transport.evaluation_overC F gamma smoothProjection u hu)
    (genericEvaluation F gamma u smoothGenericParametrization)
    (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization
      smoothGenericParametrization_isPullback) rfl
    (Generic.toModelSquare smoothProjection smoothGenericParametrization
      smoothGenericParametrization_isPullback)
    (RelativeSquare.map_left _ _ _ _ _) (RelativeSquare.map_right _ _ _ _ _)
    (toModelSquare_evaluation F gamma smoothProjection u hu smoothGenericParametrization
      smoothGenericParametrization_isPullback)

private theorem smooth_left_equation_iff :
    (@pullSection (Parametrized.Square Lines.P (genericPoint ≫ toC)) (Parametrized.Square Lines.P toC) (Generic.toModelSquare smoothProjection smoothGenericParametrization smoothGenericParametrization_isPullback)
      (@pullbackModule (Parametrized.Square Lines.P toC) (SelfProduct X.variety.structureMap) (ParametrizedContact.evaluationSquare Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) (movingPairBundleLeft X.variety X.contact)) (ParametrizedContact.leftSection Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) ≫
      (@compositionPullback (Parametrized.Square Lines.P (genericPoint ≫ toC)) (Parametrized.Square Lines.P toC) (SelfProduct X.variety.structureMap)
        (Generic.toModelSquare smoothProjection smoothGenericParametrization smoothGenericParametrization_isPullback) (ParametrizedContact.evaluationSquare Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) (ParametrizedContact.evaluationSquare Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u smoothGenericParametrization) (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback)) (toModelSquare_evaluation F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback) (movingPairBundleLeft X.variety X.contact)).hom = (ParametrizedContact.leftSection Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u smoothGenericParametrization) (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback))) ↔
    (pullSection (Generic.toModelSquare smoothProjection smoothGenericParametrization
      smoothGenericParametrization_isPullback)
      (ParametrizedContact.leftSection Lines.P toC X (Transport.evaluation F gamma u)
        (Transport.evaluation_overC F gamma smoothProjection u hu)) ≫
      (compositionPullback
        (Generic.toModelSquare smoothProjection smoothGenericParametrization
          smoothGenericParametrization_isPullback)
        (Transport.evaluationSquare F gamma smoothProjection u hu)
        (genericEvaluationSquare F gamma smoothProjection u hu smoothGenericParametrization
          smoothGenericParametrization_isPullback)
        (toModelSquare_evaluation F gamma smoothProjection u hu smoothGenericParametrization
          smoothGenericParametrization_isPullback)
        (movingPairBundleLeft X.variety X.contact)).hom =
      ParametrizedContact.leftSection Lines.P (genericPoint ≫ toC) X
        (genericEvaluation F gamma u smoothGenericParametrization)
        (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization
          smoothGenericParametrization_isPullback)) := by
  exact @smooth_equation_transport (Parametrized.Square Lines.P (genericPoint ≫ toC)) (RelativeSquare.Space Generic.projection) (Parametrized.Square Lines.P toC) (RelativeSquare.Space smoothProjection) (SelfProduct X.variety.structureMap)
    smooth_source_square_eq smooth_middle_square_eq
    (Generic.toModelSquare smoothProjection smoothGenericParametrization smoothGenericParametrization_isPullback) (Generic.toModelSquare smoothProjection smoothGenericParametrization smoothGenericParametrization_isPullback) smooth_square_map_heq
    (ParametrizedContact.evaluationSquare Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) (Transport.evaluationSquare F gamma smoothProjection u hu) (smooth_model_evaluation_heq F gamma u hu)
    (ParametrizedContact.evaluationSquare Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u smoothGenericParametrization) (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback)) (genericEvaluationSquare F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback) (smooth_generic_evaluation_heq F gamma u hu)
    (toModelSquare_evaluation F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback) (toModelSquare_evaluation F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback) (movingPairBundleLeft X.variety X.contact)
    (ParametrizedContact.leftSection Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) (ParametrizedContact.leftSection Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) (smooth_left_section_heq F gamma u hu)
    (ParametrizedContact.leftSection Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u smoothGenericParametrization) (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback)) (ParametrizedContact.leftSection Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u smoothGenericParametrization) (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback)) (smooth_left_result_heq F gamma u hu)

theorem smooth_model_left :
    pullSection (Generic.toModelSquare smoothProjection smoothGenericParametrization
      smoothGenericParametrization_isPullback)
      (ParametrizedContact.leftSection Lines.P toC X (Transport.evaluation F gamma u)
        (Transport.evaluation_overC F gamma smoothProjection u hu)) ≫
      (compositionPullback
        (Generic.toModelSquare smoothProjection smoothGenericParametrization
          smoothGenericParametrization_isPullback)
        (Transport.evaluationSquare F gamma smoothProjection u hu)
        (genericEvaluationSquare F gamma smoothProjection u hu smoothGenericParametrization
          smoothGenericParametrization_isPullback)
        (toModelSquare_evaluation F gamma smoothProjection u hu smoothGenericParametrization
          smoothGenericParametrization_isPullback)
        (movingPairBundleLeft X.variety X.contact)).hom =
      ParametrizedContact.leftSection Lines.P (genericPoint ≫ toC) X
        (genericEvaluation F gamma u smoothGenericParametrization)
        (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization
          smoothGenericParametrization_isPullback) :=
  (smooth_left_equation_iff F gamma u hu).mp (smooth_left_canonical F gamma u hu)

private theorem smooth_right_section_heq :
    @HEq (AlgebraicSection (@pullbackModule (Parametrized.Square Lines.P toC) (SelfProduct X.variety.structureMap) (ParametrizedContact.evaluationSquare Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) (movingPairBundleRight X.variety X.contact)))
      (ParametrizedContact.rightSection Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu))
      (AlgebraicSection (@pullbackModule (RelativeSquare.Space smoothProjection) (SelfProduct X.variety.structureMap) (Transport.evaluationSquare F gamma smoothProjection u hu) (movingPairBundleRight X.variety X.contact)))
      (ParametrizedContact.rightSection Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) := by rfl

private theorem smooth_right_result_heq :
    @HEq (AlgebraicSection (@pullbackModule (Parametrized.Square Lines.P (genericPoint ≫ toC)) (SelfProduct X.variety.structureMap) (ParametrizedContact.evaluationSquare Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u smoothGenericParametrization) (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback)) (movingPairBundleRight X.variety X.contact)))
      (ParametrizedContact.rightSection Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u smoothGenericParametrization) (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback))
      (AlgebraicSection (@pullbackModule (RelativeSquare.Space Generic.projection) (SelfProduct X.variety.structureMap) (genericEvaluationSquare F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback) (movingPairBundleRight X.variety X.contact)))
      (ParametrizedContact.rightSection Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u smoothGenericParametrization) (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback)) := by rfl

private theorem smooth_right_canonical :
    @pullSection (Parametrized.Square Lines.P (genericPoint ≫ toC)) (Parametrized.Square Lines.P toC) (Generic.toModelSquare smoothProjection smoothGenericParametrization smoothGenericParametrization_isPullback)
      (@pullbackModule (Parametrized.Square Lines.P toC) (SelfProduct X.variety.structureMap) (ParametrizedContact.evaluationSquare Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) (movingPairBundleRight X.variety X.contact)) (ParametrizedContact.rightSection Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) ≫
      (@compositionPullback (Parametrized.Square Lines.P (genericPoint ≫ toC)) (Parametrized.Square Lines.P toC) (SelfProduct X.variety.structureMap)
        (Generic.toModelSquare smoothProjection smoothGenericParametrization smoothGenericParametrization_isPullback) (ParametrizedContact.evaluationSquare Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) (ParametrizedContact.evaluationSquare Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u smoothGenericParametrization) (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback)) (toModelSquare_evaluation F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback) (movingPairBundleRight X.variety X.contact)).hom = (ParametrizedContact.rightSection Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u smoothGenericParametrization) (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback)) :=
  ParametrizedContact.rightSection_baseChange Lines.P (genericPoint ≫ toC) toC genericPoint rfl
    smoothGenericParametrization
    (Parametrized.baseChangeSource_first Lines.P (genericPoint ≫ toC) toC genericPoint rfl)
    (Parametrized.baseChangeSource_parameter Lines.P (genericPoint ≫ toC) toC genericPoint rfl)
    X (Transport.evaluation F gamma u)
    (Transport.evaluation_overC F gamma smoothProjection u hu)
    (genericEvaluation F gamma u smoothGenericParametrization)
    (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization
      smoothGenericParametrization_isPullback) rfl
    (Generic.toModelSquare smoothProjection smoothGenericParametrization
      smoothGenericParametrization_isPullback)
    (RelativeSquare.map_left _ _ _ _ _) (RelativeSquare.map_right _ _ _ _ _)
    (toModelSquare_evaluation F gamma smoothProjection u hu smoothGenericParametrization
      smoothGenericParametrization_isPullback)

private theorem smooth_right_equation_iff :
    (@pullSection (Parametrized.Square Lines.P (genericPoint ≫ toC)) (Parametrized.Square Lines.P toC) (Generic.toModelSquare smoothProjection smoothGenericParametrization smoothGenericParametrization_isPullback)
      (@pullbackModule (Parametrized.Square Lines.P toC) (SelfProduct X.variety.structureMap) (ParametrizedContact.evaluationSquare Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) (movingPairBundleRight X.variety X.contact)) (ParametrizedContact.rightSection Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) ≫
      (@compositionPullback (Parametrized.Square Lines.P (genericPoint ≫ toC)) (Parametrized.Square Lines.P toC) (SelfProduct X.variety.structureMap)
        (Generic.toModelSquare smoothProjection smoothGenericParametrization smoothGenericParametrization_isPullback) (ParametrizedContact.evaluationSquare Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) (ParametrizedContact.evaluationSquare Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u smoothGenericParametrization) (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback)) (toModelSquare_evaluation F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback) (movingPairBundleRight X.variety X.contact)).hom = (ParametrizedContact.rightSection Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u smoothGenericParametrization) (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback))) ↔
    (pullSection (Generic.toModelSquare smoothProjection smoothGenericParametrization
      smoothGenericParametrization_isPullback)
      (ParametrizedContact.rightSection Lines.P toC X (Transport.evaluation F gamma u)
        (Transport.evaluation_overC F gamma smoothProjection u hu)) ≫
      (compositionPullback
        (Generic.toModelSquare smoothProjection smoothGenericParametrization
          smoothGenericParametrization_isPullback)
        (Transport.evaluationSquare F gamma smoothProjection u hu)
        (genericEvaluationSquare F gamma smoothProjection u hu smoothGenericParametrization
          smoothGenericParametrization_isPullback)
        (toModelSquare_evaluation F gamma smoothProjection u hu smoothGenericParametrization
          smoothGenericParametrization_isPullback)
        (movingPairBundleRight X.variety X.contact)).hom =
      ParametrizedContact.rightSection Lines.P (genericPoint ≫ toC) X
        (genericEvaluation F gamma u smoothGenericParametrization)
        (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization
          smoothGenericParametrization_isPullback)) := by
  exact @smooth_equation_transport (Parametrized.Square Lines.P (genericPoint ≫ toC)) (RelativeSquare.Space Generic.projection) (Parametrized.Square Lines.P toC) (RelativeSquare.Space smoothProjection) (SelfProduct X.variety.structureMap)
    smooth_source_square_eq smooth_middle_square_eq
    (Generic.toModelSquare smoothProjection smoothGenericParametrization smoothGenericParametrization_isPullback) (Generic.toModelSquare smoothProjection smoothGenericParametrization smoothGenericParametrization_isPullback) smooth_square_map_heq
    (ParametrizedContact.evaluationSquare Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) (Transport.evaluationSquare F gamma smoothProjection u hu) (smooth_model_evaluation_heq F gamma u hu)
    (ParametrizedContact.evaluationSquare Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u smoothGenericParametrization) (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback)) (genericEvaluationSquare F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback) (smooth_generic_evaluation_heq F gamma u hu)
    (toModelSquare_evaluation F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback) (toModelSquare_evaluation F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback) (movingPairBundleRight X.variety X.contact)
    (ParametrizedContact.rightSection Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) (ParametrizedContact.rightSection Lines.P toC X (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma smoothProjection u hu)) (smooth_right_section_heq F gamma u hu)
    (ParametrizedContact.rightSection Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u smoothGenericParametrization) (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback)) (ParametrizedContact.rightSection Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u smoothGenericParametrization) (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization smoothGenericParametrization_isPullback)) (smooth_right_result_heq F gamma u hu)

theorem smooth_model_right :
    pullSection (Generic.toModelSquare smoothProjection smoothGenericParametrization
      smoothGenericParametrization_isPullback)
      (ParametrizedContact.rightSection Lines.P toC X (Transport.evaluation F gamma u)
        (Transport.evaluation_overC F gamma smoothProjection u hu)) ≫
      (compositionPullback
        (Generic.toModelSquare smoothProjection smoothGenericParametrization
          smoothGenericParametrization_isPullback)
        (Transport.evaluationSquare F gamma smoothProjection u hu)
        (genericEvaluationSquare F gamma smoothProjection u hu smoothGenericParametrization
          smoothGenericParametrization_isPullback)
        (toModelSquare_evaluation F gamma smoothProjection u hu smoothGenericParametrization
          smoothGenericParametrization_isPullback)
        (movingPairBundleRight X.variety X.contact)).hom =
      ParametrizedContact.rightSection Lines.P (genericPoint ≫ toC) X
        (genericEvaluation F gamma u smoothGenericParametrization)
        (genericEvaluation_overC F gamma smoothProjection u hu smoothGenericParametrization
          smoothGenericParametrization_isPullback) :=
  (smooth_right_equation_iff F gamma u hu).mp (smooth_right_canonical F gamma u hu)

end SmoothModel

end LeBrunSalamon.Construction.FormalArcComparison

end

