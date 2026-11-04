import LSTraitContact
import LSP1CoordinateGauge

/-!
# Exact coordinates of the boundary numerator

The node frames below are the actual quotient-line frames of the model
over C[[t]].  The coordinate gauge is the proved automorphism between
those quotient coordinates and the canonical polynomial charts used to
normalize `sourceBivector`.

The comparison is denominator-cleared and holds over arbitrary affine
test schemes.  In particular it retains nilpotent coefficients.  The
factor `u * w` is displayed explicitly: identifying this factor with
the two actual logarithmic differentials is a separate differential
comparison, rather than an assumption built into a new source bivector.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.P1Charts LeBrunSalamon.P1TwistFrames

namespace LeBrunSalamon.Construction.TraitContact.ModelBivector

local notation "Model" => LeBrunSalamon.Construction.StableMaps.FormalArcs.Model

open StableMaps.FormalArcs
open Smoothing.CoordinateCharts Smoothing.SourceAffineCharts

/-- The literal nodal identity.  No cancellation or reducedness is used. -/
theorem denominatorCleared {R : Type*} [CommRing R]
    (a u v w z : R) (huv : u * v = a) (hwz : w * z = a) :
    (u * z + v * w - 2 * a) * (u * w) = a * (u - w)^2 := by
  calc
    _ = (w * z) * u^2 + (u * v) * w^2 - 2 * a * u * w := by ring
    _ = _ := by rw [huv, hwz]; ring

/-- On an actual unit-parameter test scheme the same identity gives
the normalized coefficient, with the inverse unit explicitly fixed. -/
theorem unitNormalized {R : Type*} [CommRing R]
    (a : Rˣ) (u v w z : R) (huv : u * v = (a : R))
    (hwz : w * z = (a : R)) :
    ((↑a⁻¹ : R) * (u * z + v * w - 2 * (a : R))) * (u * w) =
      (u - w)^2 := by
  rw [mul_assoc, denominatorCleared (a : R) u v w z huv hwz,
    ← mul_assoc, Units.inv_mul, one_mul]

/-- A nonzero smoothing series becomes an actual unit at the fraction
field point.  The statement uses the fixed coefficient inclusion. -/
theorem genericPoint_parameter_isUnit (a : Coefficients) (ha : a ≠ 0) :
    IsUnit (genericPoint.appTop (coefficientSection a)) := by
  have hne : algebraMap Coefficients (FractionRing Coefficients) a ≠ 0 := by
    intro h
    apply ha
    apply IsFractionRing.injective Coefficients (FractionRing Coefficients)
    simpa only [map_zero] using h
  have hn : genericPoint.appTop (coefficientSection a) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Coefficients))).inv
        (algebraMap Coefficients (FractionRing Coefficients) a) := by
    exact (congrArg (fun k : CommRingCat.of Coefficients ⟶
      GenericPoint.presheaf.obj (op ⊤) => k a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
        (algebraMap Coefficients (FractionRing Coefficients))))).symm
  rw [hn]
  exact (isUnit_iff_ne_zero.mpr hne).map
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Coefficients))).inv.hom

/-- The unit persists on every test scheme over the generic point,
including nonreduced ones. -/
theorem parameter_isUnit_of_generic {T : Scheme} (a : Coefficients) (ha : a ≠ 0)
    (s : T ⟶ Trait) (g : T ⟶ GenericPoint) (hg : g ≫ genericPoint = s) :
    IsUnit (s.appTop (coefficientSection a)) := by
  rw [← hg]
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
    (genericPoint_parameter_isUnit a ha).map g.appTop.hom

variable (F : Smoothing.StandardSource) (a : Coefficients)

/-- The actual O(1,1) frame when both quotient coordinates use their
zeroth-coordinate chart.  The input equalities are factorizations of
the specified model map, not freely chosen line identifications. -/
def nodeFrame {T : Scheme} (j : T ⟶ Model F a) (u v : T ⟶ Smoothing.AffineLine)
    (hu : j ≫ modelLeft F a = u ≫ (ratioPoint 0).val)
    (hv : j ≫ modelRight F a = v ≫ (ratioPoint 0).val) :
    pullbackModule j (modelLine F a).sheaf ≅ structureModule T := by
  let H := (projectiveCoordinates 1).hyperplane.sheaf
  letI := tensorPullbackComparison_isIso j
    (pullbackModule (modelLeft F a) H) (pullbackModule (modelRight F a) H)
  exact (asIso (tensorPullbackComparison j
      (pullbackModule (modelLeft F a) H) (pullbackModule (modelRight F a) H))).symm ≪≫
    tensorIso
      (compositionPullback j (modelLeft F a) (u ≫ (ratioPoint 0).val) hu H)
      (compositionPullback j (modelRight F a) (v ≫ (ratioPoint 0).val) hv H) ≪≫
    productFrame u v 0 0

theorem nodeFrame_coordinate {T : Scheme} (j : T ⟶ Model F a)
    (u v : T ⟶ Smoothing.AffineLine)
    (hu : j ≫ modelLeft F a = u ≫ (ratioPoint 0).val)
    (hv : j ≫ modelRight F a = v ≫ (ratioPoint 0).val) (i k : Fin 2) :
    pullSection j (ModelNumerator.coordinate F a i k) ≫
      (nodeFrame F a j u v hu hv).hom =
        scalarSection (coefficient 0 i (u.appTop Smoothing.parameterFunction) *
          coefficient 0 k (v.appTop Smoothing.parameterFunction)) := by
  letI := tensorPullbackComparison_isIso j
    (pullbackModule (modelLeft F a) (projectiveCoordinates 1).hyperplane.sheaf)
    (pullbackModule (modelRight F a) (projectiveCoordinates 1).hyperplane.sheaf)
  rw [ModelNumerator.coordinate, ← tensorPullbackComparison_onSections]
  simp only [nodeFrame, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, tensorSection_map,
    compositionPullback_sections, compositionPullback_sections]
  change tensorSection _ _ ≫
    (tensorMap (ratioPullFrame u 0).hom (ratioPullFrame v 0).hom ≫
      (TensorConstruction.leftUnitIso (structureModule T)).hom) = _
  rw [← Category.assoc, tensorSection_map, ratioPullFrame_coefficient,
    ratioPullFrame_coefficient, tensorScalarSection]

/-- The equation uv=a is pulled from the actual universal conic
equation, through the actual trait map. -/
theorem nodeEquation {T : Scheme} (j : T ⟶ Model F a)
    (u v : T ⟶ Smoothing.AffineLine)
    (hu : j ≫ modelLeft F a = u ≫ (ratioPoint 0).val)
    (hv : j ≫ modelRight F a = v ≫ (ratioPoint 0).val) :
    u.appTop Smoothing.parameterFunction * v.appTop Smoothing.parameterFunction =
      (j ≫ modelProjection F a).appTop (coefficientSection a) := by
  have he := sourceEquation_pullback F (j ≫ LogarithmicSource.toUniversal F a)
  change Smoothing.ConicEquation
    (j ≫ (LogarithmicSource.toUniversal F a ≫ F.parameter))
    (j ≫ modelLeft F a) (j ≫ modelRight F a) at he
  rw [hu, hv] at he
  have hp := (conicEquation_ratios_iff _ u v 0 0).mp he
  have hb : LogarithmicSource.toUniversal F a ≫ F.parameter =
      modelProjection F a ≫ parameterMap a := pullback.condition
  rw [hb] at hp
  simpa only [coefficient, show (1 : Fin 2) ≠ 0 by decide,
    if_neg, if_pos rfl, one_mul, mul_one, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, parameterMap_parameter] using hp

/-- The canonical coordinate of the image under the actual quotient
gauge.  This is the map used by the pre-existing source bivector. -/
def gaugedPoint {T : Scheme} (j : T ⟶ Model F a) : T ⟶ ProjectiveLine :=
  (j ≫ modelLeft F a) ≫ P1CoordinateGauge.iso.inv

theorem gaugedPoint_over {T : Scheme} (j : T ⟶ Model F a) :
    gaugedPoint F a j ≫ Lines.P.structureMap =
      (j ≫ modelProjection F a) ≫ toC := by
  simp only [gaugedPoint, Category.assoc, P1CoordinateGauge.iso_inverse_over,
    modelLeft_toC]

theorem gaugedPoint_node {T : Scheme} (j : T ⟶ Model F a)
    (u : T ⟶ Smoothing.AffineLine)
    (hu : j ≫ modelLeft F a = u ≫ (ratioPoint 0).val) :
    gaugedPoint F a j = u ≫ polynomialChartInclusion 0 := by
  rw [gaugedPoint, hu, Category.assoc]
  exact congrArg (fun k => u ≫ k) (P1CoordinateGauge.quotient_backward 0)

theorem polynomialPoint_mem {T : Scheme} (u : T ⟶ Smoothing.AffineLine) :
    ⊤ ≤ (u ≫ polynomialChartInclusion 0) ⁻¹ᵁ SourceBivectorCoordinates.U := by
  rw [Scheme.Hom.comp_preimage, ← polynomialChartInclusion_range 0,
    Scheme.Hom.preimage_opensRange, Scheme.Hom.preimage_top]

/-- The polynomial coordinate used by the normalized tangent frame is
literally the parameter function of this actual affine chart map. -/
theorem polynomialPoint_coordinate {T : Scheme} (u : T ⟶ Smoothing.AffineLine)
    (hU : ⊤ ≤ (u ≫ polynomialChartInclusion 0) ⁻¹ᵁ SourceBivectorCoordinates.U) :
    (u ≫ polynomialChartInclusion 0).appLE SourceBivectorCoordinates.U ⊤ hU
        SourceBivectorCoordinates.coordinate = u.appTop Smoothing.parameterFunction := by
  have hi : ⊤ ≤ (polynomialChartInclusion 0) ⁻¹ᵁ SourceBivectorCoordinates.U := by
    rw [← polynomialChartInclusion_range 0, Scheme.Hom.preimage_opensRange]
  have hc : (polynomialChartInclusion 0).appLE SourceBivectorCoordinates.U ⊤ hi
      SourceBivectorCoordinates.coordinate = Smoothing.parameterFunction := by
    exact congrArg (fun k : CommRingCat.of (Polynomial ℂ) ⟶
      Smoothing.AffineLine.presheaf.obj (op ⊤) => k Polynomial.X)
      (polynomialChartRingEquiv_symm_appLE 0)
  have hp : (u ≫ polynomialChartInclusion 0).appLE SourceBivectorCoordinates.U ⊤ hU =
      (polynomialChartInclusion 0).appLE SourceBivectorCoordinates.U ⊤ hi ≫ u.appTop := by
    have ht : u.appTop = u.appLE ⊤ ⊤ le_rfl := u.app_eq_appLE
    rw [ht, Scheme.Hom.appLE_comp_appLE]
    rfl
  rw [hp]
  change u.appTop ((polynomialChartInclusion 0).appLE
    SourceBivectorCoordinates.U ⊤ hi SourceBivectorCoordinates.coordinate) = _
  rw [hc]

theorem gaugedPoint_mem {T : Scheme} (j : T ⟶ Model F a)
    (u : T ⟶ Smoothing.AffineLine)
    (hu : j ≫ modelLeft F a = u ≫ (ratioPoint 0).val) :
    ⊤ ≤ gaugedPoint F a j ⁻¹ᵁ SourceBivectorCoordinates.U := by
  rw [gaugedPoint_node F a j u hu]
  exact polynomialPoint_mem u

theorem gaugedPoint_coordinate {T : Scheme} (j : T ⟶ Model F a)
    (u : T ⟶ Smoothing.AffineLine)
    (hu : j ≫ modelLeft F a = u ≫ (ratioPoint 0).val)
    (hU : ⊤ ≤ gaugedPoint F a j ⁻¹ᵁ SourceBivectorCoordinates.U) :
    (gaugedPoint F a j).appLE SourceBivectorCoordinates.U ⊤ hU
      SourceBivectorCoordinates.coordinate = u.appTop Smoothing.parameterFunction := by
  rw [gaugedPoint_node F a j u hu]
  exact polynomialPoint_coordinate u _

section Square

variable {T : Scheme} (f : T ⟶ ModelNumerator.Square F a)

abbrev firstPoint : T ⟶ Model F a := f ≫ RelativeBox.first (modelProjection F a)
abbrev secondPoint : T ⟶ Model F a := f ≫ RelativeBox.second (modelProjection F a)
abbrev base : T ⟶ ComplexBase := (f ≫ ModelNumerator.squareProjection F a) ≫ toC

theorem first_over : gaugedPoint F a (firstPoint F a f) ≫ Lines.P.structureMap =
    base F a f := by
  simpa only [firstPoint, base, ModelNumerator.squareProjection, Category.assoc] using
    gaugedPoint_over F a (firstPoint F a f)

theorem second_over : gaugedPoint F a (secondPoint F a f) ≫ Lines.P.structureMap =
    base F a f := by
  rw [gaugedPoint_over]
  change ((f ≫ pullback.snd (modelProjection F a) (modelProjection F a)) ≫
      modelProjection F a) ≫ toC =
    (f ≫ (pullback.fst (modelProjection F a) (modelProjection F a) ≫
      modelProjection F a)) ≫ toC
  rw [Category.assoc f, ← pullback.condition]

variable (u v w z : T ⟶ Smoothing.AffineLine)
    (hu : firstPoint F a f ≫ modelLeft F a = u ≫ (ratioPoint 0).val)
    (hv : firstPoint F a f ≫ modelRight F a = v ≫ (ratioPoint 0).val)
    (hw : secondPoint F a f ≫ modelLeft F a = w ≫ (ratioPoint 0).val)
    (hz : secondPoint F a f ≫ modelRight F a = z ≫ (ratioPoint 0).val)

/-- Both factors use the actual model's quotient frames. -/
def numeratorFrame : pullbackModule f (ModelNumerator.line F a).sheaf ≅
    structureModule T :=
  ModelNumerator.testFrame F a f
    (nodeFrame F a (firstPoint F a f) u v hu hv)
    (nodeFrame F a (secondPoint F a f) w z hw hz)

theorem numerator_coefficient :
    pullSection f (ModelNumerator.numerator F a) ≫
      (numeratorFrame F a f u v w z hu hv hw hz).hom =
        scalarSection (u.appTop Smoothing.parameterFunction * z.appTop Smoothing.parameterFunction +
          v.appTop Smoothing.parameterFunction * w.appTop Smoothing.parameterFunction -
          2 * (f ≫ ModelNumerator.squareProjection F a).appTop (coefficientSection a)) := by
  rw [numeratorFrame, ModelNumerator.testFrame_numerator]
  simp only [ModelNumerator.firstCoefficient, ModelNumerator.secondCoefficient,
    nodeFrame_coordinate, scalarSection, sectionFromValue_spec, coefficient,
    show (1 : Fin 2) ≠ 0 by decide, if_neg, if_pos rfl, one_mul, mul_one]

def canonicalPair : T ⟶ SelfProduct Lines.P.structureMap :=
  SourceBivectorCoordinates.TestMaps.pair (base F a f)
    (gaugedPoint F a (firstPoint F a f)) (gaugedPoint F a (secondPoint F a f))
    (first_over F a f) (second_over F a f)

def canonicalFrame [IsAffine T] :
    pullbackModule (canonicalPair F a f)
      (externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf ≅
        structureModule T :=
  SourceBivectorCoordinates.TestMaps.pairFrameIso (base F a f)
    (gaugedPoint F a (firstPoint F a f)) (gaugedPoint F a (secondPoint F a f))
    (first_over F a f) (second_over F a f)
    (gaugedPoint_mem F a (firstPoint F a f) u hu)
    (gaugedPoint_mem F a (secondPoint F a f) w hw)

/-- The pre-existing normalized source bivector, through the actual
gauge, has its exact square-difference coefficient. -/
theorem sourceBivector_coefficient [IsAffine T] :
    pullSection (canonicalPair F a f) (sourceBivector Lines.P) ≫
      (canonicalFrame F a f u w hu hw).hom =
        scalarSection ((u.appTop Smoothing.parameterFunction -
          w.appTop Smoothing.parameterFunction)^2) := by
  rw [canonicalPair, canonicalFrame, SourceBivectorCoordinates.TestMaps.sourceBivector_coefficient,
    gaugedPoint_coordinate F a (firstPoint F a f) u hu,
    gaugedPoint_coordinate F a (secondPoint F a f) w hw]

/-- Exact denominator-cleared comparison with the original source
bivector.  The displayed u*w is the coefficient needed from the two
logarithmic source differentials; this theorem does not replace those
differentials by a freely chosen map. -/
theorem numerator_sourceBivector_denominatorCleared [IsAffine T] :
    (pullSection f (ModelNumerator.numerator F a) ≫
      (numeratorFrame F a f u v w z hu hv hw hz).hom) ≫
        scalarSection (u.appTop Smoothing.parameterFunction * w.appTop Smoothing.parameterFunction) =
      scalarSection ((f ≫ ModelNumerator.squareProjection F a).appTop (coefficientSection a)) ≫
        (pullSection (canonicalPair F a f) (sourceBivector Lines.P) ≫
          (canonicalFrame F a f u w hu hw).hom) := by
  rw [numerator_coefficient, sourceBivector_coefficient, ← scalarSection_mul,
    ← scalarSection_mul]
  congr 1
  apply denominatorCleared
  · simpa only [firstPoint, ModelNumerator.squareProjection, Category.assoc] using
      nodeEquation F a (firstPoint F a f) u v hu hv
  · have h := nodeEquation F a (secondPoint F a f) w z hw hz
    have hb : secondPoint F a f ≫ modelProjection F a =
        f ≫ ModelNumerator.squareProjection F a := by
      change (f ≫ pullback.snd _ _) ≫ modelProjection F a =
        f ≫ (pullback.fst _ _ ≫ modelProjection F a)
      rw [Category.assoc, pullback.condition]
    simpa only [hb] using h

/-- Exact normalization after inversion of the actual pulled smoothing
parameter.  This leaves no undetermined nonzero scalar. -/
theorem numerator_sourceBivector_normalized [IsAffine T]
    (ha : IsUnit ((f ≫ ModelNumerator.squareProjection F a).appTop (coefficientSection a))) :
    scalarSection (↑ha.unit⁻¹ : RingSections T ⊤) ≫
      ((pullSection f (ModelNumerator.numerator F a) ≫
        (numeratorFrame F a f u v w z hu hv hw hz).hom) ≫
          scalarSection (u.appTop Smoothing.parameterFunction * w.appTop Smoothing.parameterFunction)) =
      pullSection (canonicalPair F a f) (sourceBivector Lines.P) ≫
        (canonicalFrame F a f u w hu hw).hom := by
  rw [numerator_sourceBivector_denominatorCleared, ← Category.assoc,
    ← scalarSection_mul, ha.val_inv_mul, scalarSection_one, Category.id_comp]

/-- Application to the generic point uses only nonvanishing of the
original series, not a newly supplied scalar-normalization hypothesis. -/
theorem numerator_sourceBivector_generic [IsAffine T] (ha : a ≠ 0)
    (g : T ⟶ GenericPoint)
    (hg : g ≫ genericPoint = f ≫ ModelNumerator.squareProjection F a) :
    let hunit := parameter_isUnit_of_generic a ha
      (f ≫ ModelNumerator.squareProjection F a) g hg
    scalarSection (↑hunit.unit⁻¹ : RingSections T ⊤) ≫
      ((pullSection f (ModelNumerator.numerator F a) ≫
        (numeratorFrame F a f u v w z hu hv hw hz).hom) ≫
          scalarSection (u.appTop Smoothing.parameterFunction * w.appTop Smoothing.parameterFunction)) =
      pullSection (canonicalPair F a f) (sourceBivector Lines.P) ≫
        (canonicalFrame F a f u w hu hw).hom :=
  numerator_sourceBivector_normalized F a f u v w z hu hv hw hz
    (parameter_isUnit_of_generic a ha (f ≫ ModelNumerator.squareProjection F a) g hg)

end Square

end LeBrunSalamon.Construction.TraitContact.ModelBivector

end
