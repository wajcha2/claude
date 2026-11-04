import LSModelDifferential
import LSRegularModelPair
import LSFamilyBaseChange
import LSCartesianSourceDifferential
import LSModelSourceProductTransport
import LSModelSourceNumerator
import LSModelGenericParametrization
import LSModelNumeratorTransport
import LSModelGenericNormalization
import LSModelTensorScalar

/-!
# Whole-generic-square comparison for the actual conic model

The dense test used below is the residue-field point of the integral
generic square.  The final equalities are on the complete square,
including the diagonal and both outer endpoints.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirty
open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction.TraitContact.ModelGenericComparison

local notation "Model" => LeBrunSalamon.Construction.StableMaps.FormalArcs.Model

open StableMaps.FormalArcs StableMaps.FormalArcs.ModelGeometry
open Smoothing.CoordinateCharts Smoothing.SourceAffineCharts
open FamilyBivectors

variable (F : Smoothing.StandardSource) (a : Coefficients)

variable {d : ℕ} (X : SmoothProperComplexVariety d)
variable (e : Model F a ⟶ X.scheme)
variable (he : e ≫ X.structureMap = modelProjection F a ≫ toC)

/-- Pulling the global source equality through the actual complete
generic parametrization yields the original normalized P1 bivector. -/
theorem genericNumerator_source (ha : a ≠ 0) :
    genericNumerator F a ha ≫ RelativeSquare.boxMap p1Parameter
      (genericSourceVelocity F a ha) (genericSourceVelocity F a ha) =
        scalarSection (genericCoefficient F a ha) ≫ Parametrized.bivector Lines.P genericBase := by
  letI := Parametrized.sourceComparison_isIso Lines.P genericBase
  apply (cancel_mono (Parametrized.sourceComparison Lines.P genericBase)).mp
  simp only [Category.assoc, Parametrized.bivector_comparison]
  let q := parametrizedToModelSquare F a ha
  let j := parametrizedToGenericSquare F a ha
  let c := ModelBivector.canonicalPair F a (toModelSquare F a)
  have hjc : j ≫ c = Parametrized.sourceSquare Lines.P genericBase := by
    rw [← canonicalPair_eq, ← Category.assoc, parametrizedToModelSquare_factor,
      parametrizedToModelSquare_source]
  have hs := LogVelocity.section_comp j (toModelSquare F a) (modelSourceSquare F a)
    c (canonicalPair_eq F a (toModelSquare F a)) q
    (parametrizedToModelSquare_factor F a ha)
    (Parametrized.sourceSquare Lines.P genericBase) hjc
    (parametrizedToModelSquare_source F a ha) (modelSourceNumerator F a)
  have h := congrArg
    (fun s => pullSection j s ≫ (compositionPullback j c
      (Parametrized.sourceSquare Lines.P genericBase) hjc
      (externalTensor Lines.P.structureMap (tangentSheaf Lines.P.structureMap)
        (tangentSheaf Lines.P.structureMap))).hom)
    (genericSourceNumerator_eq F a ha)
  rw [hs, LogVelocity.pullSection_scalar, Category.assoc, compositionPullback_sections] at h
  have ht := numerator_transport F a ha Lines.P.structureMap
    (ModelDifferential.modelPoint F a) (ModelDifferential.modelPoint_over F a)
    p1Projection pullback.condition (genericParametrization_coordinate F a ha)
    (ModelDifferential.modelVelocity F a) (ModelDifferential.modelVelocity F a)
    (genericSourceVelocity F a ha) (genericSourceVelocity F a ha) rfl rfl
  rw [← ht]
  have hcoef : j.appTop
      ((toModelSquare F a ≫ ModelNumerator.squareProjection F a).appTop (coefficientSection a)) =
      genericCoefficient F a ha := by
    change ((j ≫ toModelSquare F a) ≫ ModelNumerator.squareProjection F a).appTop
      (coefficientSection a) = _
    rw [parametrizedToModelSquare_factor]
    rfl
  rw [hcoef] at h
  simpa only [genericSourceNumerator, modelSourceNumerator, modelSourceMorphism,
    Parametrized.sourceComparison, q, j, c, Category.assoc] using h

section Contact

variable {n : ℕ} (Y : ContactFanoManifold n)
variable (f : Model F a ⟶ Y.variety.scheme)
variable (hf : f ≫ Y.variety.structureMap = modelProjection F a ≫ toC)
variable (ell : (modelLine F a).sheaf ≅ pullbackModule f Y.contact.sequence.line.sheaf)
variable (c : Coefficients)

def genericDividedContact (ha : a ≠ 0) :
    pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule (genericEvaluation F a Y.variety f ha) Y.contact.sequence.line.sheaf :=
  (Scheme.Modules.pullback (genericParametrization F a ha)).map
    (RegularModel.dividedContact Y F a f ell c) ≫
      (compositionPullback (genericParametrization F a ha) f
        (genericEvaluation F a Y.variety f ha) rfl Y.contact.sequence.line.sheaf).hom

variable (hc : ContactScalar.morphism Y F a f hf =
  GlobalScalars.scalarEnd (modelLine F a).sheaf
    ((modelProjection F a).appTop (coefficientSection a)) ≫
      RegularModel.dividedContact Y F a f ell c)

include hc in
/-- The one divided contact factor is exactly the original contact
velocity divided by the smoothing element on the generic fibre. -/
theorem genericContact_factor (ha : a ≠ 0) :
    genericSourceVelocity F a ha ≫
      ParametrizedContact.velocity Lines.P genericBase Y
        (genericEvaluation F a Y.variety f ha) (genericEvaluation_over F a Y.variety f hf ha) =
      GlobalScalars.scalarEnd
        (pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf)
        (p1Parameter.appTop (genericBaseCoefficient a)) ≫
          genericDividedContact F a Y f ell c ha := by
  rw [ParametrizedContact.velocity, ← Category.assoc, ← genericVelocity_factor]
  rw [Category.assoc, ← Normalization.BundleGluing.compositionPullback_naturality,
    ← Category.assoc, ← Functor.map_comp]
  change (Scheme.Modules.pullback (genericParametrization F a ha)).map
      (ContactScalar.morphism Y F a f hf) ≫
        (compositionPullback (genericParametrization F a ha) f
          (genericEvaluation F a Y.variety f ha) rfl Y.contact.sequence.line.sheaf).hom = _
  rw [hc, Functor.map_comp, LineEndomorphisms.scalarEnd_pullback]
  have hcoef : (genericParametrization F a ha).appTop
      ((modelProjection F a).appTop (coefficientSection a)) =
      p1Parameter.appTop (genericBaseCoefficient a) := by
    change (genericParametrization F a ha ≫ modelProjection F a).appTop
      (coefficientSection a) = _
    rw [genericParametrization_parameter]
    rfl
  rw [hcoef]
  rfl

include hc in
theorem generic_left_raw (ha : a ≠ 0) :
    genericNumerator F a ha ≫ RelativeSquare.boxMap p1Parameter
      (genericSourceVelocity F a ha ≫ Parametrized.differential Lines.P genericBase
        Y.variety (genericEvaluation F a Y.variety f ha)
          (genericEvaluation_over F a Y.variety f hf ha))
      (genericDividedContact F a Y f ell c ha) =
    Parametrized.bivector Lines.P genericBase ≫ RelativeSquare.boxMap p1Parameter
      (Parametrized.differential Lines.P genericBase Y.variety
        (genericEvaluation F a Y.variety f ha) (genericEvaluation_over F a Y.variety f hf ha))
      (ParametrizedContact.velocity Lines.P genericBase Y
        (genericEvaluation F a Y.variety f ha) (genericEvaluation_over F a Y.variety f hf ha)) := by
  let D := Parametrized.differential Lines.P genericBase Y.variety
    (genericEvaluation F a Y.variety f ha) (genericEvaluation_over F a Y.variety f hf ha)
  let V := ParametrizedContact.velocity Lines.P genericBase Y
    (genericEvaluation F a Y.variety f ha) (genericEvaluation_over F a Y.variety f hf ha)
  have h := congrArg (fun s => s ≫ RelativeSquare.boxMap p1Parameter D V)
    (genericNumerator_source F a ha)
  simp only [Category.assoc, RelativeSquare.boxMap_comp] at h
  rw [genericContact_factor F a Y f hf ell c hc ha,
    TensorScalar.relative_right, genericCoefficient_base] at h
  letI := scalarSection_isIso (genericCoefficient F a ha) (genericCoefficient_isUnit F a ha)
  exact (cancel_epi (scalarSection (genericCoefficient F a ha))).mp h

include hc in
theorem generic_right_raw (ha : a ≠ 0) :
    genericNumerator F a ha ≫ RelativeSquare.boxMap p1Parameter
      (genericDividedContact F a Y f ell c ha)
      (genericSourceVelocity F a ha ≫ Parametrized.differential Lines.P genericBase
        Y.variety (genericEvaluation F a Y.variety f ha)
          (genericEvaluation_over F a Y.variety f hf ha)) =
    Parametrized.bivector Lines.P genericBase ≫ RelativeSquare.boxMap p1Parameter
      (ParametrizedContact.velocity Lines.P genericBase Y
        (genericEvaluation F a Y.variety f ha) (genericEvaluation_over F a Y.variety f hf ha))
      (Parametrized.differential Lines.P genericBase Y.variety
        (genericEvaluation F a Y.variety f ha) (genericEvaluation_over F a Y.variety f hf ha)) := by
  let D := Parametrized.differential Lines.P genericBase Y.variety
    (genericEvaluation F a Y.variety f ha) (genericEvaluation_over F a Y.variety f hf ha)
  let V := ParametrizedContact.velocity Lines.P genericBase Y
    (genericEvaluation F a Y.variety f ha) (genericEvaluation_over F a Y.variety f hf ha)
  have h := congrArg (fun s => s ≫ RelativeSquare.boxMap p1Parameter V D)
    (genericNumerator_source F a ha)
  simp only [Category.assoc, RelativeSquare.boxMap_comp] at h
  rw [genericContact_factor F a Y f hf ell c hc ha,
    TensorScalar.relative_left, genericCoefficient_base] at h
  letI := scalarSection_isIso (genericCoefficient F a ha) (genericCoefficient_isUnit F a ha)
  exact (cancel_epi (scalarSection (genericCoefficient F a ha))).mp h

include hc in
/-- Exact normalization of the actual regular left vector section on
the complete generic square.  The original source bivector, derivative
and external target bundle are retained. -/
theorem leftSection_generic (ha : a ≠ 0) :
    pullSection (parametrizedToModelSquare F a ha)
      (RegularModel.leftSection Y F a f hf ell c) ≫
        (compositionPullback (parametrizedToModelSquare F a ha)
          (RegularModel.evaluationSquare Y F a f hf)
          (ParametrizedContact.evaluationSquare Lines.P genericBase Y
            (genericEvaluation F a Y.variety f ha) (genericEvaluation_over F a Y.variety f hf ha))
          (parametrizedToModelSquare_evaluation F a Y.variety f hf ha)
          (movingPairBundleLeft Y.variety Y.contact)).hom =
      ParametrizedContact.leftSection Lines.P genericBase Y
        (genericEvaluation F a Y.variety f ha) (genericEvaluation_over F a Y.variety f hf ha) := by
  have h := numerator_transport F a ha Y.variety.structureMap f hf
    (genericEvaluation F a Y.variety f ha) (genericEvaluation_over F a Y.variety f hf ha) rfl
    (LogarithmicSource.velocity F a Y.variety f hf)
    (RegularModel.dividedContact Y F a f ell c)
    (genericSourceVelocity F a ha ≫ Parametrized.differential Lines.P genericBase
      Y.variety (genericEvaluation F a Y.variety f ha)
        (genericEvaluation_over F a Y.variety f hf ha))
    (genericDividedContact F a Y f ell c ha)
    (genericVelocity_factor F a Y.variety f hf ha) rfl
  have hraw := congrArg
    (fun s => s ≫ RelativeSquare.comparison p1Parameter Y.variety.structureMap
      genericBase (genericEvaluation F a Y.variety f ha)
      (genericEvaluation_over F a Y.variety f hf ha)
      (tangentSheaf Y.variety.structureMap) Y.contact.sequence.line.sheaf)
    (generic_left_raw F a Y f hf ell c hc ha)
  simp only [Category.assoc] at hraw
  simpa only [RegularModel.leftSection, RegularModel.leftRaw,
    ParametrizedContact.leftSection, Category.assoc] using h.trans hraw

include hc in
/-- Exact normalization of the actual regular right vector section,
on the same whole generic square. -/
theorem rightSection_generic (ha : a ≠ 0) :
    pullSection (parametrizedToModelSquare F a ha)
      (RegularModel.rightSection Y F a f hf ell c) ≫
        (compositionPullback (parametrizedToModelSquare F a ha)
          (RegularModel.evaluationSquare Y F a f hf)
          (ParametrizedContact.evaluationSquare Lines.P genericBase Y
            (genericEvaluation F a Y.variety f ha) (genericEvaluation_over F a Y.variety f hf ha))
          (parametrizedToModelSquare_evaluation F a Y.variety f hf ha)
          (movingPairBundleRight Y.variety Y.contact)).hom =
      ParametrizedContact.rightSection Lines.P genericBase Y
        (genericEvaluation F a Y.variety f ha) (genericEvaluation_over F a Y.variety f hf ha) := by
  have h := numerator_transport F a ha Y.variety.structureMap f hf
    (genericEvaluation F a Y.variety f ha) (genericEvaluation_over F a Y.variety f hf ha) rfl
    (RegularModel.dividedContact Y F a f ell c)
    (LogarithmicSource.velocity F a Y.variety f hf)
    (genericDividedContact F a Y f ell c ha)
    (genericSourceVelocity F a ha ≫ Parametrized.differential Lines.P genericBase
      Y.variety (genericEvaluation F a Y.variety f ha)
        (genericEvaluation_over F a Y.variety f hf ha))
    rfl (genericVelocity_factor F a Y.variety f hf ha)
  have hraw := congrArg
    (fun s => s ≫ RelativeSquare.comparison p1Parameter Y.variety.structureMap
      genericBase (genericEvaluation F a Y.variety f ha)
      (genericEvaluation_over F a Y.variety f hf ha)
      Y.contact.sequence.line.sheaf (tangentSheaf Y.variety.structureMap))
    (generic_right_raw F a Y f hf ell c hc ha)
  simp only [Category.assoc] at hraw
  simpa only [RegularModel.rightSection, RegularModel.rightRaw,
    ParametrizedContact.rightSection, Category.assoc] using h.trans hraw

end Contact

end LeBrunSalamon.Construction.TraitContact.ModelGenericComparison

end
