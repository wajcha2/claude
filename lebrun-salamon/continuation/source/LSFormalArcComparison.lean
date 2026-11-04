import LSGenericFamilyComparison
import LSFormalArcFamilyComparison
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

private theorem nodal_equation_transport {T T' Y Y' Z : Scheme}
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

section NodalNormalization

variable (F : ProjectiveNodalFamily Lines.P Lines.marking
  X.variety X.contact.sequence.line 2)
variable (gamma : PointsOver Trait toC F.Square (F.squareToBase ≫ F.toC))
variable (S : Smoothing.StandardSource) (a : Coefficients) (ha : a ≠ 0)
variable (u : Source F (baseArc F gamma) ≅ Model S a)
variable (hu : u.hom ≫ modelProjection S a = parameter F (baseArc F gamma))
variable (ell : (TraitPullback.line F (baseArc F gamma)).sheaf ≅
  pullbackModule u.hom (modelLine S a).sheaf)
variable (c : Coefficients)

private theorem nodal_source_square_eq : (Parametrized.Square Lines.P ModelGenericComparison.genericBase) = (RelativeSquare.Space Generic.projection) := by rfl

private theorem nodal_middle_square_eq : (ModelNumerator.Square S a) = (RelativeSquare.Space (modelProjection S a)) := by rfl

private theorem nodal_square_map_heq :
    @HEq ((Parametrized.Square Lines.P ModelGenericComparison.genericBase) ⟶ (ModelNumerator.Square S a)) (ModelGenericComparison.parametrizedToModelSquare S a ha)
      ((RelativeSquare.Space Generic.projection) ⟶ (RelativeSquare.Space (modelProjection S a))) (Generic.toModelSquare (modelProjection S a) (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) := by rfl

private theorem nodal_model_evaluation_heq :
    @HEq ((ModelNumerator.Square S a) ⟶ (SelfProduct X.variety.structureMap)) (RegularModel.evaluationSquare X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu))
      ((RelativeSquare.Space (modelProjection S a)) ⟶ (SelfProduct X.variety.structureMap)) (Transport.evaluationSquare F gamma (modelProjection S a) u hu) := by rfl

private theorem nodal_generic_evaluation_heq :
    @HEq ((Parametrized.Square Lines.P ModelGenericComparison.genericBase) ⟶ (SelfProduct X.variety.structureMap)) (ParametrizedContact.evaluationSquare Lines.P ModelGenericComparison.genericBase X (ModelGenericComparison.genericEvaluation S a X.variety (Transport.evaluation F gamma u) ha) (ModelGenericComparison.genericEvaluation_over S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha))
      ((RelativeSquare.Space Generic.projection) ⟶ (SelfProduct X.variety.structureMap)) (genericEvaluationSquare F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) := by rfl

private theorem nodal_left_input_heq :
    @HEq (AlgebraicSection (@pullbackModule (ModelNumerator.Square S a) (SelfProduct X.variety.structureMap) (RegularModel.evaluationSquare X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu)) (movingPairBundleLeft X.variety X.contact)))
      (RegularModel.leftSection X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) (Transport.line F gamma u ell) c)
      (AlgebraicSection (@pullbackModule (RelativeSquare.Space (modelProjection S a)) (SelfProduct X.variety.structureMap) (Transport.evaluationSquare F gamma (modelProjection S a) u hu) (movingPairBundleLeft X.variety X.contact)))
      (RegularModel.leftSection X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) (Transport.line F gamma u ell) c) := by rfl

private theorem nodal_left_output_heq :
    @HEq (AlgebraicSection (@pullbackModule (Parametrized.Square Lines.P ModelGenericComparison.genericBase) (SelfProduct X.variety.structureMap) (ParametrizedContact.evaluationSquare Lines.P ModelGenericComparison.genericBase X (ModelGenericComparison.genericEvaluation S a X.variety (Transport.evaluation F gamma u) ha) (ModelGenericComparison.genericEvaluation_over S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha)) (movingPairBundleLeft X.variety X.contact)))
      (ParametrizedContact.leftSection Lines.P ModelGenericComparison.genericBase X (ModelGenericComparison.genericEvaluation S a X.variety (Transport.evaluation F gamma u) ha) (ModelGenericComparison.genericEvaluation_over S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha))
      (AlgebraicSection (@pullbackModule (RelativeSquare.Space Generic.projection) (SelfProduct X.variety.structureMap) (genericEvaluationSquare F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (movingPairBundleLeft X.variety X.contact)))
      (ParametrizedContact.leftSection Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u (ModelGenericComparison.genericParametrization S a ha)) (genericEvaluation_overC F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha))) := by rfl

private theorem nodal_left_equation_iff :
    (@pullSection (Parametrized.Square Lines.P ModelGenericComparison.genericBase) (ModelNumerator.Square S a) (ModelGenericComparison.parametrizedToModelSquare S a ha) (@pullbackModule (ModelNumerator.Square S a) (SelfProduct X.variety.structureMap) (RegularModel.evaluationSquare X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu)) (movingPairBundleLeft X.variety X.contact)) (RegularModel.leftSection X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) (Transport.line F gamma u ell) c) ≫
      (@compositionPullback (Parametrized.Square Lines.P ModelGenericComparison.genericBase) (ModelNumerator.Square S a) (SelfProduct X.variety.structureMap) (ModelGenericComparison.parametrizedToModelSquare S a ha) (RegularModel.evaluationSquare X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu)) (ParametrizedContact.evaluationSquare Lines.P ModelGenericComparison.genericBase X (ModelGenericComparison.genericEvaluation S a X.variety (Transport.evaluation F gamma u) ha) (ModelGenericComparison.genericEvaluation_over S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha)) (ModelGenericComparison.parametrizedToModelSquare_evaluation S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha) (movingPairBundleLeft X.variety X.contact)).hom = (ParametrizedContact.leftSection Lines.P ModelGenericComparison.genericBase X (ModelGenericComparison.genericEvaluation S a X.variety (Transport.evaluation F gamma u) ha) (ModelGenericComparison.genericEvaluation_over S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha))) ↔
    (@pullSection (RelativeSquare.Space Generic.projection) (RelativeSquare.Space (modelProjection S a)) (Generic.toModelSquare (modelProjection S a) (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (@pullbackModule (RelativeSquare.Space (modelProjection S a)) (SelfProduct X.variety.structureMap) (Transport.evaluationSquare F gamma (modelProjection S a) u hu) (movingPairBundleLeft X.variety X.contact)) (RegularModel.leftSection X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) (Transport.line F gamma u ell) c) ≫
      (@compositionPullback (RelativeSquare.Space Generic.projection) (RelativeSquare.Space (modelProjection S a)) (SelfProduct X.variety.structureMap) (Generic.toModelSquare (modelProjection S a) (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (Transport.evaluationSquare F gamma (modelProjection S a) u hu) (genericEvaluationSquare F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (toModelSquare_evaluation F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (movingPairBundleLeft X.variety X.contact)).hom = (ParametrizedContact.leftSection Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u (ModelGenericComparison.genericParametrization S a ha)) (genericEvaluation_overC F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)))) := by
  exact nodal_equation_transport nodal_source_square_eq (nodal_middle_square_eq S a)
    (ModelGenericComparison.parametrizedToModelSquare S a ha) (Generic.toModelSquare (modelProjection S a) (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (nodal_square_map_heq S a ha)
    (RegularModel.evaluationSquare X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu)) (Transport.evaluationSquare F gamma (modelProjection S a) u hu) (nodal_model_evaluation_heq F gamma S a u hu)
    (ParametrizedContact.evaluationSquare Lines.P ModelGenericComparison.genericBase X (ModelGenericComparison.genericEvaluation S a X.variety (Transport.evaluation F gamma u) ha) (ModelGenericComparison.genericEvaluation_over S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha)) (genericEvaluationSquare F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (nodal_generic_evaluation_heq F gamma S a ha u hu)
    (ModelGenericComparison.parametrizedToModelSquare_evaluation S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha) (toModelSquare_evaluation F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (movingPairBundleLeft X.variety X.contact)
    (RegularModel.leftSection X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) (Transport.line F gamma u ell) c) (RegularModel.leftSection X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) (Transport.line F gamma u ell) c) (nodal_left_input_heq F gamma S a u hu ell c)
    (ParametrizedContact.leftSection Lines.P ModelGenericComparison.genericBase X (ModelGenericComparison.genericEvaluation S a X.variety (Transport.evaluation F gamma u) ha) (ModelGenericComparison.genericEvaluation_over S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha)) (ParametrizedContact.leftSection Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u (ModelGenericComparison.genericParametrization S a ha)) (genericEvaluation_overC F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha))) (nodal_left_output_heq F gamma S a ha u hu)

private theorem nodal_right_input_heq :
    @HEq (AlgebraicSection (@pullbackModule (ModelNumerator.Square S a) (SelfProduct X.variety.structureMap) (RegularModel.evaluationSquare X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu)) (movingPairBundleRight X.variety X.contact)))
      (RegularModel.rightSection X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) (Transport.line F gamma u ell) c)
      (AlgebraicSection (@pullbackModule (RelativeSquare.Space (modelProjection S a)) (SelfProduct X.variety.structureMap) (Transport.evaluationSquare F gamma (modelProjection S a) u hu) (movingPairBundleRight X.variety X.contact)))
      (RegularModel.rightSection X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) (Transport.line F gamma u ell) c) := by rfl

private theorem nodal_right_output_heq :
    @HEq (AlgebraicSection (@pullbackModule (Parametrized.Square Lines.P ModelGenericComparison.genericBase) (SelfProduct X.variety.structureMap) (ParametrizedContact.evaluationSquare Lines.P ModelGenericComparison.genericBase X (ModelGenericComparison.genericEvaluation S a X.variety (Transport.evaluation F gamma u) ha) (ModelGenericComparison.genericEvaluation_over S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha)) (movingPairBundleRight X.variety X.contact)))
      (ParametrizedContact.rightSection Lines.P ModelGenericComparison.genericBase X (ModelGenericComparison.genericEvaluation S a X.variety (Transport.evaluation F gamma u) ha) (ModelGenericComparison.genericEvaluation_over S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha))
      (AlgebraicSection (@pullbackModule (RelativeSquare.Space Generic.projection) (SelfProduct X.variety.structureMap) (genericEvaluationSquare F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (movingPairBundleRight X.variety X.contact)))
      (ParametrizedContact.rightSection Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u (ModelGenericComparison.genericParametrization S a ha)) (genericEvaluation_overC F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha))) := by rfl

private theorem nodal_right_equation_iff :
    (@pullSection (Parametrized.Square Lines.P ModelGenericComparison.genericBase) (ModelNumerator.Square S a) (ModelGenericComparison.parametrizedToModelSquare S a ha) (@pullbackModule (ModelNumerator.Square S a) (SelfProduct X.variety.structureMap) (RegularModel.evaluationSquare X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu)) (movingPairBundleRight X.variety X.contact)) (RegularModel.rightSection X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) (Transport.line F gamma u ell) c) ≫
      (@compositionPullback (Parametrized.Square Lines.P ModelGenericComparison.genericBase) (ModelNumerator.Square S a) (SelfProduct X.variety.structureMap) (ModelGenericComparison.parametrizedToModelSquare S a ha) (RegularModel.evaluationSquare X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu)) (ParametrizedContact.evaluationSquare Lines.P ModelGenericComparison.genericBase X (ModelGenericComparison.genericEvaluation S a X.variety (Transport.evaluation F gamma u) ha) (ModelGenericComparison.genericEvaluation_over S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha)) (ModelGenericComparison.parametrizedToModelSquare_evaluation S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha) (movingPairBundleRight X.variety X.contact)).hom = (ParametrizedContact.rightSection Lines.P ModelGenericComparison.genericBase X (ModelGenericComparison.genericEvaluation S a X.variety (Transport.evaluation F gamma u) ha) (ModelGenericComparison.genericEvaluation_over S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha))) ↔
    (@pullSection (RelativeSquare.Space Generic.projection) (RelativeSquare.Space (modelProjection S a)) (Generic.toModelSquare (modelProjection S a) (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (@pullbackModule (RelativeSquare.Space (modelProjection S a)) (SelfProduct X.variety.structureMap) (Transport.evaluationSquare F gamma (modelProjection S a) u hu) (movingPairBundleRight X.variety X.contact)) (RegularModel.rightSection X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) (Transport.line F gamma u ell) c) ≫
      (@compositionPullback (RelativeSquare.Space Generic.projection) (RelativeSquare.Space (modelProjection S a)) (SelfProduct X.variety.structureMap) (Generic.toModelSquare (modelProjection S a) (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (Transport.evaluationSquare F gamma (modelProjection S a) u hu) (genericEvaluationSquare F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (toModelSquare_evaluation F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (movingPairBundleRight X.variety X.contact)).hom = (ParametrizedContact.rightSection Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u (ModelGenericComparison.genericParametrization S a ha)) (genericEvaluation_overC F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)))) := by
  exact nodal_equation_transport nodal_source_square_eq (nodal_middle_square_eq S a)
    (ModelGenericComparison.parametrizedToModelSquare S a ha) (Generic.toModelSquare (modelProjection S a) (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (nodal_square_map_heq S a ha)
    (RegularModel.evaluationSquare X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu)) (Transport.evaluationSquare F gamma (modelProjection S a) u hu) (nodal_model_evaluation_heq F gamma S a u hu)
    (ParametrizedContact.evaluationSquare Lines.P ModelGenericComparison.genericBase X (ModelGenericComparison.genericEvaluation S a X.variety (Transport.evaluation F gamma u) ha) (ModelGenericComparison.genericEvaluation_over S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha)) (genericEvaluationSquare F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (nodal_generic_evaluation_heq F gamma S a ha u hu)
    (ModelGenericComparison.parametrizedToModelSquare_evaluation S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha) (toModelSquare_evaluation F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (movingPairBundleRight X.variety X.contact)
    (RegularModel.rightSection X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) (Transport.line F gamma u ell) c) (RegularModel.rightSection X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) (Transport.line F gamma u ell) c) (nodal_right_input_heq F gamma S a u hu ell c)
    (ParametrizedContact.rightSection Lines.P ModelGenericComparison.genericBase X (ModelGenericComparison.genericEvaluation S a X.variety (Transport.evaluation F gamma u) ha) (ModelGenericComparison.genericEvaluation_over S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha)) (ParametrizedContact.rightSection Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u (ModelGenericComparison.genericParametrization S a ha)) (genericEvaluation_overC F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha))) (nodal_right_output_heq F gamma S a ha u hu)

private theorem nodal_left_native
    (hc : ContactScalar.morphism X S a (Transport.evaluation F gamma u)
      (Transport.evaluation_overC F gamma (modelProjection S a) u hu) =
    GlobalScalars.scalarEnd (modelLine S a).sheaf
      ((modelProjection S a).appTop (coefficientSection a)) ≫
        RegularModel.dividedContact X S a (Transport.evaluation F gamma u)
          (Transport.line F gamma u ell) c) :
    (@pullSection (Parametrized.Square Lines.P ModelGenericComparison.genericBase) (ModelNumerator.Square S a) (ModelGenericComparison.parametrizedToModelSquare S a ha) (@pullbackModule (ModelNumerator.Square S a) (SelfProduct X.variety.structureMap) (RegularModel.evaluationSquare X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu)) (movingPairBundleLeft X.variety X.contact)) (RegularModel.leftSection X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) (Transport.line F gamma u ell) c) ≫
      (@compositionPullback (Parametrized.Square Lines.P ModelGenericComparison.genericBase) (ModelNumerator.Square S a) (SelfProduct X.variety.structureMap) (ModelGenericComparison.parametrizedToModelSquare S a ha) (RegularModel.evaluationSquare X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu)) (ParametrizedContact.evaluationSquare Lines.P ModelGenericComparison.genericBase X (ModelGenericComparison.genericEvaluation S a X.variety (Transport.evaluation F gamma u) ha) (ModelGenericComparison.genericEvaluation_over S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha)) (ModelGenericComparison.parametrizedToModelSquare_evaluation S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha) (movingPairBundleLeft X.variety X.contact)).hom = (ParametrizedContact.leftSection Lines.P ModelGenericComparison.genericBase X (ModelGenericComparison.genericEvaluation S a X.variety (Transport.evaluation F gamma u) ha) (ModelGenericComparison.genericEvaluation_over S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha))) := by
  exact ModelGenericComparison.leftSection_generic S a X (Transport.evaluation F gamma u)
      (Transport.evaluation_overC F gamma (modelProjection S a) u hu)
      (Transport.line F gamma u ell) c hc ha

private theorem nodal_left_normalized
    (hc : ContactScalar.morphism X S a (Transport.evaluation F gamma u)
      (Transport.evaluation_overC F gamma (modelProjection S a) u hu) =
    GlobalScalars.scalarEnd (modelLine S a).sheaf
      ((modelProjection S a).appTop (coefficientSection a)) ≫
        RegularModel.dividedContact X S a (Transport.evaluation F gamma u)
          (Transport.line F gamma u ell) c) :
    (@pullSection (RelativeSquare.Space Generic.projection) (RelativeSquare.Space (modelProjection S a)) (Generic.toModelSquare (modelProjection S a) (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (@pullbackModule (RelativeSquare.Space (modelProjection S a)) (SelfProduct X.variety.structureMap) (Transport.evaluationSquare F gamma (modelProjection S a) u hu) (movingPairBundleLeft X.variety X.contact)) (RegularModel.leftSection X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) (Transport.line F gamma u ell) c) ≫
      (@compositionPullback (RelativeSquare.Space Generic.projection) (RelativeSquare.Space (modelProjection S a)) (SelfProduct X.variety.structureMap) (Generic.toModelSquare (modelProjection S a) (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (Transport.evaluationSquare F gamma (modelProjection S a) u hu) (genericEvaluationSquare F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (toModelSquare_evaluation F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (movingPairBundleLeft X.variety X.contact)).hom = (ParametrizedContact.leftSection Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u (ModelGenericComparison.genericParametrization S a ha)) (genericEvaluation_overC F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)))) := by
  exact (nodal_left_equation_iff F gamma S a ha u hu ell c).mp
    (nodal_left_native F gamma S a ha u hu ell c hc)

private theorem nodal_right_native
    (hc : ContactScalar.morphism X S a (Transport.evaluation F gamma u)
      (Transport.evaluation_overC F gamma (modelProjection S a) u hu) =
    GlobalScalars.scalarEnd (modelLine S a).sheaf
      ((modelProjection S a).appTop (coefficientSection a)) ≫
        RegularModel.dividedContact X S a (Transport.evaluation F gamma u)
          (Transport.line F gamma u ell) c) :
    (@pullSection (Parametrized.Square Lines.P ModelGenericComparison.genericBase) (ModelNumerator.Square S a) (ModelGenericComparison.parametrizedToModelSquare S a ha) (@pullbackModule (ModelNumerator.Square S a) (SelfProduct X.variety.structureMap) (RegularModel.evaluationSquare X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu)) (movingPairBundleRight X.variety X.contact)) (RegularModel.rightSection X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) (Transport.line F gamma u ell) c) ≫
      (@compositionPullback (Parametrized.Square Lines.P ModelGenericComparison.genericBase) (ModelNumerator.Square S a) (SelfProduct X.variety.structureMap) (ModelGenericComparison.parametrizedToModelSquare S a ha) (RegularModel.evaluationSquare X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu)) (ParametrizedContact.evaluationSquare Lines.P ModelGenericComparison.genericBase X (ModelGenericComparison.genericEvaluation S a X.variety (Transport.evaluation F gamma u) ha) (ModelGenericComparison.genericEvaluation_over S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha)) (ModelGenericComparison.parametrizedToModelSquare_evaluation S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha) (movingPairBundleRight X.variety X.contact)).hom = (ParametrizedContact.rightSection Lines.P ModelGenericComparison.genericBase X (ModelGenericComparison.genericEvaluation S a X.variety (Transport.evaluation F gamma u) ha) (ModelGenericComparison.genericEvaluation_over S a X.variety (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) ha))) := by
  exact ModelGenericComparison.rightSection_generic S a X (Transport.evaluation F gamma u)
      (Transport.evaluation_overC F gamma (modelProjection S a) u hu)
      (Transport.line F gamma u ell) c hc ha

private theorem nodal_right_normalized
    (hc : ContactScalar.morphism X S a (Transport.evaluation F gamma u)
      (Transport.evaluation_overC F gamma (modelProjection S a) u hu) =
    GlobalScalars.scalarEnd (modelLine S a).sheaf
      ((modelProjection S a).appTop (coefficientSection a)) ≫
        RegularModel.dividedContact X S a (Transport.evaluation F gamma u)
          (Transport.line F gamma u ell) c) :
    (@pullSection (RelativeSquare.Space Generic.projection) (RelativeSquare.Space (modelProjection S a)) (Generic.toModelSquare (modelProjection S a) (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (@pullbackModule (RelativeSquare.Space (modelProjection S a)) (SelfProduct X.variety.structureMap) (Transport.evaluationSquare F gamma (modelProjection S a) u hu) (movingPairBundleRight X.variety X.contact)) (RegularModel.rightSection X S a (Transport.evaluation F gamma u) (Transport.evaluation_overC F gamma (modelProjection S a) u hu) (Transport.line F gamma u ell) c) ≫
      (@compositionPullback (RelativeSquare.Space Generic.projection) (RelativeSquare.Space (modelProjection S a)) (SelfProduct X.variety.structureMap) (Generic.toModelSquare (modelProjection S a) (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (Transport.evaluationSquare F gamma (modelProjection S a) u hu) (genericEvaluationSquare F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (toModelSquare_evaluation F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)) (movingPairBundleRight X.variety X.contact)).hom = (ParametrizedContact.rightSection Lines.P (genericPoint ≫ toC) X (genericEvaluation F gamma u (ModelGenericComparison.genericParametrization S a ha)) (genericEvaluation_overC F gamma (modelProjection S a) u hu (ModelGenericComparison.genericParametrization S a ha) (ModelGenericComparison.genericParametrization_isPullback S a ha)))) := by
  exact (nodal_right_equation_iff F gamma S a ha u hu ell c).mp
    (nodal_right_native F gamma S a ha u hu ell c hc)

end NodalNormalization

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
    exact nodal_left_normalized F gamma S a ha u hu ell c hc
  · apply right_regular_of_model Q gamma (modelProjection S a) u hu k hk hU
      (RegularModel.rightSection X S a (Transport.evaluation F gamma u)
        (Transport.evaluation_overC F gamma (modelProjection S a) u hu)
        (Transport.line F gamma u ell) c)
    exact nodal_right_normalized F gamma S a ha u hu ell c hc

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
