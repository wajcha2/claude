import LSFormalArcModelNormalization

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

end SmoothModel

end LeBrunSalamon.Construction.FormalArcComparison

end
