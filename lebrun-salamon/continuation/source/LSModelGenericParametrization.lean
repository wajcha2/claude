import LSModelDifferential
import LSRegularModelPair
import LSFamilyBaseChange
import LSCartesianSourceDifferential
import LSModelSourceProductTransport

/-!
# Generic-model parametrization and numerator transport

This module extracts the original independent parametrization block, with
its namespace, variable context, declaration headers and proof bodies intact.
The initial candidate is uncompiled; no new input or assumption is introduced.
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

abbrev genericBase : GenericPoint ⟶ ComplexBase := genericPoint ≫ toC
abbrev P1Generic := Parametrized.Source Lines.P genericBase
abbrev p1Projection : P1Generic ⟶ ProjectiveLine :=
  Parametrized.projection Lines.P genericBase
abbrev p1Parameter : P1Generic ⟶ GenericPoint :=
  Parametrized.parameter Lines.P genericBase

/-- The fixed coordinate gauge, on the complete projective-line family. -/
def productGauge : P1Generic ≅ P1Generic where
  hom := pullback.lift (p1Projection ≫ P1CoordinateGauge.iso.inv) p1Parameter (by
    rw [Category.assoc, P1CoordinateGauge.iso_inverse_over]
    exact pullback.condition)
  inv := pullback.lift (p1Projection ≫ P1CoordinateGauge.iso.hom) p1Parameter (by
    rw [Category.assoc, P1CoordinateGauge.iso_over]
    exact pullback.condition)
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.id_comp]

@[reassoc] theorem productGauge_coordinate : productGauge.hom ≫ p1Projection =
    p1Projection ≫ P1CoordinateGauge.iso.inv := pullback.lift_fst _ _ _

@[reassoc] theorem productGauge_base : productGauge.hom ≫ p1Parameter =
    p1Parameter := pullback.lift_snd _ _ _

@[reassoc] theorem productGauge_inverse_base : productGauge.inv ≫ p1Parameter =
    p1Parameter := pullback.lift_snd _ _ _

def gaugedTrivialization (ha : a ≠ 0) : source F a ≅ P1Generic :=
  ModelGeometry.genericTrivialization F a ha ≪≫ productGauge

@[reassoc] theorem gaugedTrivialization_coordinate (ha : a ≠ 0) :
    (gaugedTrivialization F a ha).hom ≫ p1Projection =
      inclusion F a ≫ ModelDifferential.modelPoint F a := by
  rw [gaugedTrivialization, Iso.trans_hom, Category.assoc, productGauge_coordinate,
    ← Category.assoc, ModelGeometry.genericTrivialization_left]
  simp only [ModelGeometry.genericLeft, modelLeft, ModelDifferential.modelPoint,
    ModelDifferential.universalPoint, Category.assoc]

@[reassoc] theorem gaugedTrivialization_base (ha : a ≠ 0) :
    (gaugedTrivialization F a ha).hom ≫ p1Parameter = projection F a := by
  rw [gaugedTrivialization, Iso.trans_hom, Category.assoc, productGauge_base]
  exact ModelGeometry.genericTrivialization_base F a ha

@[reassoc] theorem gaugedTrivialization_inverse_base (ha : a ≠ 0) :
    (gaugedTrivialization F a ha).inv ≫ projection F a = p1Parameter := by
  rw [← gaugedTrivialization_base F a ha]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The canonical parametrization of the whole generic model. -/
def genericParametrization (ha : a ≠ 0) : P1Generic ⟶ Model F a :=
  (gaugedTrivialization F a ha).inv ≫ inclusion F a

@[reassoc] theorem genericParametrization_coordinate (ha : a ≠ 0) :
    genericParametrization F a ha ≫ ModelDifferential.modelPoint F a = p1Projection := by
  rw [genericParametrization, Category.assoc, ← gaugedTrivialization_coordinate F a ha]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

@[reassoc] theorem genericParametrization_parameter (ha : a ≠ 0) :
    genericParametrization F a ha ≫ modelProjection F a = p1Parameter ≫ genericPoint := by
  rw [genericParametrization, Category.assoc,
    show inclusion F a ≫ modelProjection F a = projection F a ≫ genericPoint from
      pullback.condition, ← Category.assoc, gaugedTrivialization_inverse_base]

theorem genericParametrization_isPullback (ha : a ≠ 0) :
    IsPullback (genericParametrization F a ha) p1Parameter
      (modelProjection F a) genericPoint := by
  have h : IsPullback (gaugedTrivialization F a ha).inv p1Parameter
      (projection F a) (𝟙 GenericPoint) := by
    apply IsPullback.of_horiz_isIso
    exact ⟨by simpa only [Category.comp_id] using
      gaugedTrivialization_inverse_base F a ha⟩
  simpa only [genericParametrization, Category.id_comp] using
    h.paste_horiz (IsPullback.of_hasPullback (modelProjection F a) genericPoint)

def parametrizedToGenericSquare (ha : a ≠ 0) :
    Parametrized.Square Lines.P genericBase ⟶ Square F a :=
  RelativeSquare.map p1Parameter (projection F a)
    (gaugedTrivialization F a ha).inv (𝟙 GenericPoint)
    (by simpa only [Category.comp_id] using gaugedTrivialization_inverse_base F a ha)

def parametrizedToModelSquare (ha : a ≠ 0) :
    Parametrized.Square Lines.P genericBase ⟶ ModelNumerator.Square F a :=
  RelativeSquare.map p1Parameter (modelProjection F a)
    (genericParametrization F a ha) genericPoint
    (genericParametrization_parameter F a ha)

@[reassoc] theorem parametrizedToModelSquare_base (ha : a ≠ 0) :
    parametrizedToModelSquare F a ha ≫ ModelNumerator.squareProjection F a =
      (RelativeSquare.left p1Parameter ≫ p1Parameter) ≫ genericPoint := by
  calc
    _ = (parametrizedToModelSquare F a ha ≫
        RelativeSquare.left (modelProjection F a)) ≫ modelProjection F a :=
      (Category.assoc _ _ _).symm
    _ = (RelativeSquare.left p1Parameter ≫ genericParametrization F a ha) ≫
        modelProjection F a := by rw [parametrizedToModelSquare, RelativeSquare.map_left]
    _ = (RelativeSquare.left p1Parameter ≫ p1Parameter) ≫ genericPoint := by
      rw [Category.assoc, genericParametrization_parameter, ← Category.assoc]

@[reassoc] theorem parametrizedToModelSquare_factor (ha : a ≠ 0) :
    parametrizedToGenericSquare F a ha ≫ toModelSquare F a =
      parametrizedToModelSquare F a ha := by
  apply pullback.hom_ext
  · simp only [Category.assoc, toModelSquare_first, parametrizedToGenericSquare,
      parametrizedToModelSquare, RelativeSquare.map_left, RelativeSquare.map_left_assoc,
      genericParametrization]
  · simp only [Category.assoc, toModelSquare_second, parametrizedToGenericSquare,
      parametrizedToModelSquare, RelativeSquare.map_right, RelativeSquare.map_right_assoc,
      genericParametrization]

@[reassoc] theorem parametrizedToModelSquare_source (ha : a ≠ 0) :
    parametrizedToModelSquare F a ha ≫ modelSourceSquare F a =
      Parametrized.sourceSquare Lines.P genericBase :=
  RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
    (genericParametrization F a ha) genericPoint
    (genericParametrization_parameter F a ha) Lines.P.structureMap genericBase toC
    p1Projection (ModelDifferential.modelPoint F a) pullback.condition
    (ModelDifferential.modelPoint_over F a) (genericParametrization_coordinate F a ha)


def genericCotangentComparison (ha : a ≠ 0) :
    pullbackModule (genericParametrization F a ha) (cotangentSheaf (modelProjection F a)) ≅
      cotangentSheaf p1Parameter := by
  letI := CartesianDifferential.isIso_of_isPullback p1Parameter (modelProjection F a)
    (genericParametrization F a ha) genericPoint (genericParametrization_isPullback F a ha)
  exact asIso (RelativeDifferential.cotangent p1Parameter (modelProjection F a)
    (genericParametrization F a ha) genericPoint (genericParametrization_parameter F a ha))

def genericForm (ha : a ≠ 0) : cotangentSheaf p1Parameter ⟶
    dualSheaf (pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf) :=
  LogVelocity.pulledForm (modelProjection F a) p1Parameter
    (genericParametrization F a ha) (modelLine F a).sheaf
    (pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf)
    (genericCotangentComparison F a ha) (Iso.refl _) (LogarithmicSource.fundamentalClass F a)

def genericSourceVelocity (ha : a ≠ 0) :
    pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule p1Projection (tangentSheaf Lines.P.structureMap) :=
  (Scheme.Modules.pullback (genericParametrization F a ha)).map
    (ModelDifferential.modelVelocity F a) ≫
      (compositionPullback (genericParametrization F a ha) (ModelDifferential.modelPoint F a)
        p1Projection (genericParametrization_coordinate F a ha)
        (tangentSheaf Lines.P.structureMap)).hom

theorem genericSourceVelocity_form (ha : a ≠ 0) :
    genericSourceVelocity F a ha =
      LogVelocity.fromForm p1Parameter genericBase
        (pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf)
        (genericForm F a ha) (projectiveLineVariety Lines.P) p1Projection
        pullback.condition := by
  exact CartesianDifferential.fromForm_baseChange_named (modelProjection F a)
    p1Parameter toC (genericParametrization F a ha) genericPoint
    (genericParametrization_parameter F a ha) (modelLine F a).sheaf
    (genericCotangentComparison F a ha) rfl (LogarithmicSource.fundamentalClass F a)
    (projectiveLineVariety Lines.P) (ModelDifferential.modelPoint F a) p1Projection
    (genericParametrization_coordinate F a ha) (ModelDifferential.modelPoint_over F a)
    pullback.condition

variable {d : ℕ} (X : SmoothProperComplexVariety d)
variable (e : Model F a ⟶ X.scheme)
variable (he : e ≫ X.structureMap = modelProjection F a ≫ toC)

def genericEvaluation (ha : a ≠ 0) : P1Generic ⟶ X.scheme :=
  genericParametrization F a ha ≫ e

include he in
theorem genericEvaluation_over (ha : a ≠ 0) :
    genericEvaluation F a X e ha ≫ X.structureMap = p1Parameter ≫ genericBase := by
  rw [genericEvaluation, Category.assoc, he, ← Category.assoc,
    genericParametrization_parameter]
  simp only [genericBase, Category.assoc]

/-- The actual model velocity factors through the actual relative
derivative in the canonical generic parametrization. -/
theorem genericVelocity_factor (ha : a ≠ 0) :
    (Scheme.Modules.pullback (genericParametrization F a ha)).map
      (LogarithmicSource.velocity F a X e he) ≫
        (compositionPullback (genericParametrization F a ha) e (genericEvaluation F a X e ha)
          rfl (tangentSheaf X.structureMap)).hom =
      genericSourceVelocity F a ha ≫
        Parametrized.differential Lines.P genericBase X (genericEvaluation F a X e ha)
          (genericEvaluation_over F a X e he ha) := by
  rw [genericSourceVelocity_form, CartesianDifferential.fromForm_factor]
  exact CartesianDifferential.fromForm_baseChange_named (modelProjection F a)
    p1Parameter toC (genericParametrization F a ha) genericPoint
    (genericParametrization_parameter F a ha) (modelLine F a).sheaf
    (genericCotangentComparison F a ha) rfl (LogarithmicSource.fundamentalClass F a)
    X e (genericEvaluation F a X e ha) rfl he (genericEvaluation_over F a X e he ha)

@[reassoc] theorem parametrizedToModelSquare_evaluation (ha : a ≠ 0) :
    parametrizedToModelSquare F a ha ≫
      RelativeSquare.evaluation (modelProjection F a) X.structureMap toC e he =
      Parametrized.evaluationSquare Lines.P genericBase X
        (genericEvaluation F a X e ha) (genericEvaluation_over F a X e he ha) := by
  exact RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
    (genericParametrization F a ha) genericPoint (genericParametrization_parameter F a ha)
    X.structureMap genericBase toC (genericEvaluation F a X e ha) e
    (genericEvaluation_over F a X e he ha) he rfl

/-- The smoothing element as a regular function on the whole generic
parametrized square. -/
def genericCoefficient (ha : a ≠ 0) :
    RingSections (Parametrized.Square Lines.P genericBase) ⊤ :=
  (parametrizedToModelSquare F a ha ≫ ModelNumerator.squareProjection F a).appTop
    (coefficientSection a)

theorem genericCoefficient_isUnit (ha : a ≠ 0) :
    IsUnit (genericCoefficient F a ha) := by
  exact ModelBivector.parameter_isUnit_of_generic a ha
    (parametrizedToModelSquare F a ha ≫ ModelNumerator.squareProjection F a)
    (RelativeSquare.left p1Parameter ≫ p1Parameter)
    (parametrizedToModelSquare_base F a ha).symm

def genericCoordinate (ha : a ≠ 0) (i j : Fin 2) :
    AlgebraicSection (pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf) :=
  pullSection (genericParametrization F a ha) (ModelNumerator.coordinate F a i j)

/-- The same three homogeneous terms, transported to the complete P1
square.  This is an actual section of the pulled logarithmic lines. -/
def genericNumerator (ha : a ≠ 0) : AlgebraicSection
    (RelativeSquare.box p1Parameter
      (pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf)
      (pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf)) :=
  RelativeSquare.productSection p1Parameter (genericCoordinate F a ha 1 0)
      (genericCoordinate F a ha 0 1) +
    RelativeSquare.productSection p1Parameter (genericCoordinate F a ha 0 1)
      (genericCoordinate F a ha 1 0) -
    scalarSection (2 * genericCoefficient F a ha) ≫
      RelativeSquare.productSection p1Parameter (genericCoordinate F a ha 0 0)
        (genericCoordinate F a ha 0 0)


end LeBrunSalamon.Construction.TraitContact.ModelGenericComparison

end
