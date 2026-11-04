import LSModelDifferential
import LSRegularModelPair
import LSFamilyBaseChange

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

abbrev source := ModelGeometry.GenericModel F a
abbrev projection := ModelGeometry.genericProjection F a
abbrev inclusion : source F a ⟶ Model F a :=
  pullback.fst (modelProjection F a) genericPoint
abbrev Square := RelativeSquare.Space (projection F a)
abbrev squareBase : Square F a ⟶ GenericPoint :=
  RelativeSquare.left (projection F a) ≫ projection F a

def toModelSquare : Square F a ⟶ ModelNumerator.Square F a :=
  RelativeSquare.map (projection F a) (modelProjection F a)
    (inclusion F a) genericPoint pullback.condition

@[reassoc] theorem toModelSquare_first : toModelSquare F a ≫
    RelativeBox.first (modelProjection F a) =
      RelativeSquare.left (projection F a) ≫ inclusion F a :=
  RelativeSquare.map_left _ _ _ _ _

@[reassoc] theorem toModelSquare_second : toModelSquare F a ≫
    RelativeBox.second (modelProjection F a) =
      RelativeSquare.right (projection F a) ≫ inclusion F a :=
  RelativeSquare.map_right _ _ _ _ _

@[reassoc] theorem toModelSquare_base :
    toModelSquare F a ≫ ModelNumerator.squareProjection F a =
      squareBase F a ≫ genericPoint := by
  rw [ModelNumerator.squareProjection, ← Category.assoc, toModelSquare_first,
    Category.assoc, pullback.condition, ← Category.assoc]

theorem source_smooth (ha : a ≠ 0) : Smooth (projection F a) := by
  letI : Smooth Lines.P.structureMap :=
    smoothProperComplexVariety_smooth (projectiveLineVariety Lines.P)
  exact MorphismProperty.of_isPullback (ModelGeometry.genericLeft_isPullback F a ha)
    (show Smooth Lines.P.structureMap from inferInstance)

theorem square_integral (ha : a ≠ 0) : IsIntegral (Square F a) := by
  letI : GeometricallyIntegral (projection F a) :=
    ModelGeometry.generic_geometricallyIntegral F a ha
  letI : Smooth (projection F a) := source_smooth F a ha
  letI : IsIntegral (source F a) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (projection F a)
  letI : IsLocallyNoetherian (source F a) :=
    LocallyOfFiniteType.isLocallyNoetherian (projection F a)
  exact inferInstance

/-- A literal whole-trait point u=1,v=a of the node chart. -/
def unitPlane : Trait ⟶ Plane := planeFromFunctions toC 1 (coefficientSection a)

theorem unitPlane_parameter :
    unitPlane a ≫ polynomialLine (parameterPolynomial 0) = parameterMap a := by
  apply functionMap_ext toC
  · rw [Category.assoc, polynomialLine_over, unitPlane, planeFromFunctions_over]
  · exact parameterMap_toC a
  rw [Scheme.Hom.comp_appTop]
  change (unitPlane a).appTop
    ((polynomialLine (parameterPolynomial 0)).appTop Smoothing.parameterFunction) = _
  rw [polynomialLine_parameter, unitPlane, planeFromFunctions_apply,
    parameterMap_parameter]
  simp only [parameterPolynomial, if_pos rfl, if_true, if_false, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_X, show (1 : Fin 2) ≠ 0 by decide, if_neg, one_mul]

def unitModel : Trait ⟶ Model F a :=
  pullback.lift (unitPlane a ≫ modelMap F 0) (𝟙 Trait) (by
    rw [Category.assoc, (modelMap_spec F 0).1, unitPlane_parameter, Category.id_comp])

@[reassoc] theorem unitModel_parameter : unitModel F a ≫ modelProjection F a = 𝟙 Trait :=
  pullback.lift_snd _ _ _

@[reassoc] theorem unitModel_universal :
    unitModel F a ≫ LogarithmicSource.toUniversal F a = unitPlane a ≫ modelMap F 0 :=
  pullback.lift_fst _ _ _

@[reassoc] theorem unitModel_left : unitModel F a ≫ modelLeft F a =
    (unitPlane a ≫ polynomialLine (MvPolynomial.X 0)) ≫ (ratioPoint 0).val := by
  change unitModel F a ≫ (LogarithmicSource.toUniversal F a ≫ F.left) = _
  rw [← Category.assoc, unitModel_universal, Category.assoc, (modelMap_spec F 0).2.1]
  simp only [leftPolynomial, leftIndex, if_pos rfl, show (0 : Fin 3) ≠ 1 by decide,
    if_neg, if_true, if_false, Category.assoc]

@[reassoc] theorem unitModel_right : unitModel F a ≫ modelRight F a =
    (unitPlane a ≫ polynomialLine (MvPolynomial.X 1)) ≫ (ratioPoint 0).val := by
  change unitModel F a ≫ (LogarithmicSource.toUniversal F a ≫ F.right) = _
  rw [← Category.assoc, unitModel_universal, Category.assoc, (modelMap_spec F 0).2.2]
  simp only [rightPolynomial, rightIndex, show (0 : Fin 3) ≠ 1 by decide,
    show (0 : Fin 3) ≠ 2 by decide, if_neg, if_true, if_false, Category.assoc]

def genericUnit : GenericPoint ⟶ source F a :=
  pullback.lift (genericPoint ≫ unitModel F a) (𝟙 GenericPoint) (by
    rw [Category.assoc, unitModel_parameter, Category.comp_id, Category.id_comp])

@[reassoc] theorem genericUnit_inclusion : genericUnit F a ≫ inclusion F a =
    genericPoint ≫ unitModel F a := pullback.lift_fst _ _ _

def unitSquare : GenericPoint ⟶ Square F a :=
  pullback.lift (genericUnit F a) (genericUnit F a) rfl

@[reassoc] theorem unitSquare_first :
    (unitSquare F a ≫ toModelSquare F a) ≫ RelativeBox.first (modelProjection F a) =
      genericPoint ≫ unitModel F a := by
  rw [Category.assoc, toModelSquare_first, ← Category.assoc]
  change (unitSquare F a ≫ pullback.fst (projection F a) (projection F a)) ≫ inclusion F a = _
  rw [unitSquare, pullback.lift_fst, genericUnit_inclusion]

@[reassoc] theorem unitSquare_second :
    (unitSquare F a ≫ toModelSquare F a) ≫ RelativeBox.second (modelProjection F a) =
      genericPoint ≫ unitModel F a := by
  rw [Category.assoc, toModelSquare_second, ← Category.assoc]
  change (unitSquare F a ≫ pullback.snd (projection F a) (projection F a)) ≫ inclusion F a = _
  rw [unitSquare, pullback.lift_snd, genericUnit_inclusion]

def nodeOpen : (Square F a).Opens :=
  ((ModelBivector.firstPoint F a (toModelSquare F a) ≫ modelLeft F a) ⁻¹ᵁ ratioOpen 0 ⊓
    (ModelBivector.firstPoint F a (toModelSquare F a) ≫ modelRight F a) ⁻¹ᵁ ratioOpen 0) ⊓
  ((ModelBivector.secondPoint F a (toModelSquare F a) ≫ modelLeft F a) ⁻¹ᵁ ratioOpen 0 ⊓
    (ModelBivector.secondPoint F a (toModelSquare F a) ≫ modelRight F a) ⁻¹ᵁ ratioOpen 0)

theorem nodeOpen_nonempty : (nodeOpen F a : Set (Square F a)).Nonempty := by
  let x : GenericPoint := default
  refine ⟨unitSquare F a x, ?_⟩
  have hl : ((unitSquare F a ≫ toModelSquare F a) ≫
      RelativeBox.first (modelProjection F a)) ≫ modelLeft F a =
      ((genericPoint ≫ unitPlane a) ≫ polynomialLine (MvPolynomial.X 0)) ≫
        (ratioPoint 0).val := by
    rw [unitSquare_first, Category.assoc, unitModel_left]
    simp only [Category.assoc]
  have hr : ((unitSquare F a ≫ toModelSquare F a) ≫
      RelativeBox.first (modelProjection F a)) ≫ modelRight F a =
      ((genericPoint ≫ unitPlane a) ≫ polynomialLine (MvPolynomial.X 1)) ≫
        (ratioPoint 0).val := by
    rw [unitSquare_first, Category.assoc, unitModel_right]
    simp only [Category.assoc]
  have hl' : ((unitSquare F a ≫ toModelSquare F a) ≫
      RelativeBox.second (modelProjection F a)) ≫ modelLeft F a =
      ((genericPoint ≫ unitPlane a) ≫ polynomialLine (MvPolynomial.X 0)) ≫
        (ratioPoint 0).val := by
    rw [unitSquare_second, Category.assoc, unitModel_left]
    simp only [Category.assoc]
  have hr' : ((unitSquare F a ≫ toModelSquare F a) ≫
      RelativeBox.second (modelProjection F a)) ≫ modelRight F a =
      ((genericPoint ≫ unitPlane a) ≫ polynomialLine (MvPolynomial.X 1)) ≫
        (ratioPoint 0).val := by
    rw [unitSquare_second, Category.assoc, unitModel_right]
    simp only [Category.assoc]
  change
    ((((unitSquare F a ≫ toModelSquare F a) ≫ RelativeBox.first (modelProjection F a)) ≫
        modelLeft F a) x ∈ ratioOpen 0 ∧
      (((unitSquare F a ≫ toModelSquare F a) ≫ RelativeBox.first (modelProjection F a)) ≫
        modelRight F a) x ∈ ratioOpen 0) ∧
    ((((unitSquare F a ≫ toModelSquare F a) ≫ RelativeBox.second (modelProjection F a)) ≫
        modelLeft F a) x ∈ ratioOpen 0 ∧
      (((unitSquare F a ≫ toModelSquare F a) ≫ RelativeBox.second (modelProjection F a)) ≫
        modelRight F a) x ∈ ratioOpen 0)
  constructor
  · constructor
    · change _ ∈ (ratioOpen 0 : Set ProjectiveLine)
      rw [hl, ← ratioPoint_range]
      exact ⟨((genericPoint ≫ unitPlane a) ≫ polynomialLine (MvPolynomial.X 0)) x, rfl⟩
    · change _ ∈ (ratioOpen 0 : Set ProjectiveLine)
      rw [hr, ← ratioPoint_range]
      exact ⟨((genericPoint ≫ unitPlane a) ≫ polynomialLine (MvPolynomial.X 1)) x, rfl⟩
  · constructor
    · change _ ∈ (ratioOpen 0 : Set ProjectiveLine)
      rw [hl', ← ratioPoint_range]
      exact ⟨((genericPoint ≫ unitPlane a) ≫ polynomialLine (MvPolynomial.X 0)) x, rfl⟩
    · change _ ∈ (ratioOpen 0 : Set ProjectiveLine)
      rw [hr', ← ratioPoint_range]
      exact ⟨((genericPoint ≫ unitPlane a) ≫ polynomialLine (MvPolynomial.X 1)) x, rfl⟩

/-- The node chart contains an actual dense affine test of the whole
generic square.  This constructs the test and all four actual ratio
maps; none of these witnesses is added to the theorem's hypotheses. -/
theorem denseNodeTest_exists (ha : a ≠ 0) :
    ∃ (T : Scheme) (j : T ⟶ Square F a), IsAffine T ∧ DenseRange j.base ∧
      ∃ u v w z : T ⟶ Smoothing.AffineLine,
        ModelBivector.firstPoint F a (j ≫ toModelSquare F a) ≫ modelLeft F a = u ≫ (ratioPoint 0).val ∧
        ModelBivector.firstPoint F a (j ≫ toModelSquare F a) ≫ modelRight F a = v ≫ (ratioPoint 0).val ∧
        ModelBivector.secondPoint F a (j ≫ toModelSquare F a) ≫ modelLeft F a = w ≫ (ratioPoint 0).val ∧
        ModelBivector.secondPoint F a (j ≫ toModelSquare F a) ≫ modelRight F a = z ≫ (ratioPoint 0).val := by
  letI : IsIntegral (Square F a) := square_integral F a ha
  let eta := _root_.genericPoint (Square F a)
  let T := Spec ((Square F a).residueField eta)
  let j : T ⟶ Square F a := (Square F a).fromSpecResidueField eta
  have hd : DenseRange j.base := by
    rw [denseRange_iff_closure_range]
    change closure (Set.range ((Square F a).fromSpecResidueField eta)) = Set.univ
    rw [Scheme.range_fromSpecResidueField]
    exact genericPoint_closure (Square F a)
  have heta : eta ∈ nodeOpen F a :=
    ((genericPoint_spec (Square F a)).mem_open_set_iff (nodeOpen F a).isOpen).mpr
      (by simpa using nodeOpen_nonempty F a)
  have hj (t : T) : j t ∈ nodeOpen F a := by
    change (Square F a).fromSpecResidueField eta t ∈ nodeOpen F a
    rw [Scheme.fromSpecResidueField_apply]
    exact heta
  let p := ModelBivector.firstPoint F a (j ≫ toModelSquare F a)
  let q := ModelBivector.secondPoint F a (j ≫ toModelSquare F a)
  have h₁ : Set.range (p ≫ modelLeft F a) ⊆ Set.range (ratioPoint 0).val := by
    rw [ratioPoint_range]
    rintro _ ⟨t, rfl⟩
    exact (hj t).1.1
  have h₂ : Set.range (p ≫ modelRight F a) ⊆ Set.range (ratioPoint 0).val := by
    rw [ratioPoint_range]
    rintro _ ⟨t, rfl⟩
    exact (hj t).1.2
  have h₃ : Set.range (q ≫ modelLeft F a) ⊆ Set.range (ratioPoint 0).val := by
    rw [ratioPoint_range]
    rintro _ ⟨t, rfl⟩
    exact (hj t).2.1
  have h₄ : Set.range (q ≫ modelRight F a) ⊆ Set.range (ratioPoint 0).val := by
    rw [ratioPoint_range]
    rintro _ ⟨t, rfl⟩
    exact (hj t).2.2
  letI := ratioPoint_openImmersion 0
  refine ⟨T, j, inferInstance, hd,
    IsOpenImmersion.lift (ratioPoint 0).val (p ≫ modelLeft F a) h₁,
    IsOpenImmersion.lift (ratioPoint 0).val (p ≫ modelRight F a) h₂,
    IsOpenImmersion.lift (ratioPoint 0).val (q ≫ modelLeft F a) h₃,
    IsOpenImmersion.lift (ratioPoint 0).val (q ≫ modelRight F a) h₄, ?_, ?_, ?_, ?_⟩
  all_goals exact (IsOpenImmersion.lift_fac _ _ _).symm

def modelSourceSquare : ModelNumerator.Square F a ⟶ SelfProduct Lines.P.structureMap :=
  RelativeSquare.evaluation (modelProjection F a) Lines.P.structureMap toC
    (ModelDifferential.modelPoint F a) (ModelDifferential.modelPoint_over F a)

def modelSourceMorphism : (ModelNumerator.line F a).sheaf ⟶
    pullbackModule (modelSourceSquare F a)
      (externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf :=
  RelativeSquare.boxMap (modelProjection F a)
    (ModelDifferential.modelVelocity F a) (ModelDifferential.modelVelocity F a) ≫
      RelativeSquare.comparison (modelProjection F a) Lines.P.structureMap toC
        (ModelDifferential.modelPoint F a) (ModelDifferential.modelPoint_over F a)
        (tangentSheaf Lines.P.structureMap) (tangentSheaf Lines.P.structureMap)

def modelSourceNumerator : AlgebraicSection
    (pullbackModule (modelSourceSquare F a)
      (externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf) :=
  ModelNumerator.numerator F a ≫ modelSourceMorphism F a

@[reassoc] theorem canonicalPair_first {T : Scheme} (f : T ⟶ ModelNumerator.Square F a) :
    ModelBivector.canonicalPair F a f ≫ firstProjection Lines.P.structureMap =
      ModelBivector.gaugedPoint F a (ModelBivector.firstPoint F a f) := by
  simp only [ModelBivector.canonicalPair, SourceBivectorCoordinates.TestMaps.pair,
    firstProjection, pullback.lift_fst]

@[reassoc] theorem canonicalPair_second {T : Scheme} (f : T ⟶ ModelNumerator.Square F a) :
    ModelBivector.canonicalPair F a f ≫ secondProjection Lines.P.structureMap =
      ModelBivector.gaugedPoint F a (ModelBivector.secondPoint F a f) := by
  simp only [ModelBivector.canonicalPair, SourceBivectorCoordinates.TestMaps.pair,
    secondProjection, pullback.lift_snd]

@[reassoc] theorem canonicalPair_eq {T : Scheme} (f : T ⟶ ModelNumerator.Square F a) :
    f ≫ modelSourceSquare F a = ModelBivector.canonicalPair F a f := by
  apply pullback.hom_ext
  · change (f ≫ modelSourceSquare F a) ≫ firstProjection Lines.P.structureMap = _
    rw [Category.assoc, modelSourceSquare, RelativeSquare.evaluation_left,
      canonicalPair_first, ← Category.assoc]
    exact ModelDifferential.modelPoint_gauged F a (ModelBivector.firstPoint F a f)
  · change (f ≫ modelSourceSquare F a) ≫ secondProjection Lines.P.structureMap = _
    rw [Category.assoc, modelSourceSquare, RelativeSquare.evaluation_right,
      canonicalPair_second, ← Category.assoc]
    exact ModelDifferential.modelPoint_gauged F a (ModelBivector.secondPoint F a f)

theorem canonicalPair_comp {T Y : Scheme} (j : T ⟶ Y)
    (f : Y ⟶ ModelNumerator.Square F a) :
    j ≫ ModelBivector.canonicalPair F a f = ModelBivector.canonicalPair F a (j ≫ f) := by
  rw [← canonicalPair_eq F a f, ← Category.assoc, canonicalPair_eq]

/-- On a product of the actual homogeneous sections, the global
source morphism has exactly the endpoint normalization of squareVelocity. -/
theorem sourceProduct_pullback {T : Scheme} (f : T ⟶ ModelNumerator.Square F a)
    (s t : AlgebraicSection (modelLine F a).sheaf) :
    pullSection f (RelativeBox.section (modelProjection F a) s t ≫ modelSourceMorphism F a) ≫
      (compositionPullback f (modelSourceSquare F a) (ModelBivector.canonicalPair F a f)
        (canonicalPair_eq F a f)
        (externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf).hom =
      pullSection f (RelativeBox.section (modelProjection F a) s t) ≫
        ModelDifferential.squareVelocity F a f := by
  let P := SourceBivectorCoordinates.TestMaps.pairPullIso (ModelBivector.base F a f)
    (ModelBivector.gaugedPoint F a (ModelBivector.firstPoint F a f))
    (ModelBivector.gaugedPoint F a (ModelBivector.secondPoint F a f))
    (ModelBivector.first_over F a f) (ModelBivector.second_over F a f)
  have hp : P.hom =
      (Descent.LineValue.externalAlongIso Lines.P.structureMap
        (ModelBivector.canonicalPair F a f)
        (ModelBivector.gaugedPoint F a (ModelBivector.firstPoint F a f))
        (ModelBivector.gaugedPoint F a (ModelBivector.secondPoint F a f))
        (canonicalPair_first F a f) (canonicalPair_second F a f)
        (tangentSheaf Lines.P.structureMap) (tangentSheaf Lines.P.structureMap)).inv := by
    rfl
  have h := RelativeSquare.product_pullback (modelProjection F a) Lines.P.structureMap toC
    (ModelDifferential.modelPoint F a) (ModelDifferential.modelPoint_over F a)
    f (ModelBivector.canonicalPair F a f) (canonicalPair_eq F a f)
    (ModelBivector.gaugedPoint F a (ModelBivector.firstPoint F a f))
    (ModelBivector.gaugedPoint F a (ModelBivector.secondPoint F a f))
    (canonicalPair_first F a f) (canonicalPair_second F a f)
    (ModelDifferential.modelPoint_gauged F a (ModelBivector.firstPoint F a f))
    (ModelDifferential.modelPoint_gauged F a (ModelBivector.secondPoint F a f))
    (s ≫ ModelDifferential.modelVelocity F a) (t ≫ ModelDifferential.modelVelocity F a)
  rw [← hp, ← RelativeSquare.productSection_map] at h
  apply (cancel_mono P.hom).mp
  have hr :
      (pullSection f (RelativeBox.section (modelProjection F a) s t) ≫
        ModelDifferential.squareVelocity F a f) ≫ P.hom =
      tensorSection
        (pullSection (ModelBivector.firstPoint F a f) (s ≫ ModelDifferential.modelVelocity F a) ≫
          (compositionPullback (ModelBivector.firstPoint F a f) (ModelDifferential.modelPoint F a)
            (ModelBivector.gaugedPoint F a (ModelBivector.firstPoint F a f))
            (ModelDifferential.modelPoint_gauged F a (ModelBivector.firstPoint F a f))
            (tangentSheaf Lines.P.structureMap)).hom)
        (pullSection (ModelBivector.secondPoint F a f) (t ≫ ModelDifferential.modelVelocity F a) ≫
          (compositionPullback (ModelBivector.secondPoint F a f) (ModelDifferential.modelPoint F a)
            (ModelBivector.gaugedPoint F a (ModelBivector.secondPoint F a f))
            (ModelDifferential.modelPoint_gauged F a (ModelBivector.secondPoint F a f))
            (tangentSheaf Lines.P.structureMap)).hom) := by
    simp only [ModelDifferential.squareVelocity, Category.assoc, P,
      Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, RelativeBox.pullIso_section, tensorSection_map]
    simp only [ModelDifferential.nodeVelocity, pullSection_naturality, Category.assoc]
  apply Eq.trans ?_ hr.symm
  simpa only [modelSourceMorphism, RelativeSquare.productSection,
    RelativeBox.section, Category.assoc] using h

theorem section_scale {Y : Scheme} {E : OModule Y}
    (r : RingSections Y ⊤) (s : AlgebraicSection E) :
    sectionFromValue (r • sectionValue s) = scalarSection r ≫ s := by
  apply (sectionValue_bijective E).injective
  rw [sectionFromValue_spec, sectionValue_comp, scalarSection, sectionFromValue_spec]
  simpa only [smul_eq_mul, mul_one] using
    ((s.app ⊤).hom.map_smul r (1 : RingSections Y ⊤)).symm

/-- Actual source-numerator specialization, before any density or
generic-fibre argument. -/
theorem sourceNumerator_pullback {T : Scheme} (f : T ⟶ ModelNumerator.Square F a) :
    pullSection f (modelSourceNumerator F a) ≫
      (compositionPullback f (modelSourceSquare F a) (ModelBivector.canonicalPair F a f)
        (canonicalPair_eq F a f)
        (externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf).hom =
      pullSection f (ModelNumerator.numerator F a) ≫ ModelDifferential.squareVelocity F a f := by
  have hadd {E : OModule (ModelNumerator.Square F a)} (s t : AlgebraicSection E) :
      pullSection f (s + t) = pullSection f s + pullSection f t := by
    simp only [pullSection, restrictSection, Functor.map_add, Preadditive.comp_add]
  unfold modelSourceNumerator
  rw [ModelNumerator.numerator, section_scale]
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Normalization.pullSection_sub,
    hadd, Category.assoc, LogVelocity.pullSection_scalar]
  rw [sourceProduct_pullback, sourceProduct_pullback, sourceProduct_pullback]

def genericSourceNumerator : AlgebraicSection
    (pullbackModule (ModelBivector.canonicalPair F a (toModelSquare F a))
      (externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf) :=
  pullSection (toModelSquare F a) (modelSourceNumerator F a) ≫
    (compositionPullback (toModelSquare F a) (modelSourceSquare F a)
      (ModelBivector.canonicalPair F a (toModelSquare F a))
      (canonicalPair_eq F a (toModelSquare F a))
      (externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf).hom

/-- Equality on the dense affine node test extends to the complete
generic square because the actual target is a line bundle and the
generic square is integral. -/
theorem genericSourceNumerator_eq (ha : a ≠ 0) :
    genericSourceNumerator F a =
      scalarSection ((toModelSquare F a ≫ ModelNumerator.squareProjection F a).appTop
        (coefficientSection a)) ≫
      pullSection (ModelBivector.canonicalPair F a (toModelSquare F a)) (sourceBivector Lines.P) := by
  letI : IsIntegral (Square F a) := square_integral F a ha
  obtain ⟨T, j, hT, hj, u, v, w, z, hu, hv, hw, hz⟩ := denseNodeTest_exists F a ha
  letI := hT
  let E := externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine
  let c := ModelBivector.canonicalPair F a (toModelSquare F a)
  let c' := ModelBivector.canonicalPair F a (j ≫ toModelSquare F a)
  let hcc := canonicalPair_comp F a j (toModelSquare F a)
  apply dominant_pullSection_injective j hj (fun _ => inferInstance) (pullbackLine c E)
  apply (cancel_mono (compositionPullback j c c' hcc E.sheaf).hom).mp
  have hs := LogVelocity.section_comp j (toModelSquare F a) (modelSourceSquare F a)
    c (canonicalPair_eq F a (toModelSquare F a)) (j ≫ toModelSquare F a) rfl
    c' hcc (canonicalPair_eq F a (j ≫ toModelSquare F a)) (modelSourceNumerator F a)
  change pullSection j (genericSourceNumerator F a) ≫
    (compositionPullback j c c' hcc E.sheaf).hom = _ at hs
  rw [hs, sourceNumerator_pullback, LogVelocity.pullSection_scalar,
    Category.assoc, compositionPullback_sections]
  have hn := ModelDifferential.numerator_sourceBivector_denominatorCleared F a
    (j ≫ toModelSquare F a) u v w z hu hv hw hz
  simpa only [c', Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Category.assoc] using hn

/-- The two actual logarithmic source differentials send the global
numerator to a times the original normalized source bivector on the
entire smooth generic square. -/
theorem generic_source_denominatorCleared (ha : a ≠ 0) :
    pullSection (toModelSquare F a) (ModelNumerator.numerator F a) ≫
      ModelDifferential.squareVelocity F a (toModelSquare F a) =
      scalarSection ((toModelSquare F a ≫ ModelNumerator.squareProjection F a).appTop
        (coefficientSection a)) ≫
      pullSection (ModelBivector.canonicalPair F a (toModelSquare F a)) (sourceBivector Lines.P) := by
  rw [← sourceNumerator_pullback]
  exact genericSourceNumerator_eq F a ha

theorem genericParameter_isUnit (ha : a ≠ 0) :
    IsUnit ((toModelSquare F a ≫ ModelNumerator.squareProjection F a).appTop (coefficientSection a)) :=
  ModelBivector.parameter_isUnit_of_generic a ha
    (toModelSquare F a ≫ ModelNumerator.squareProjection F a) (squareBase F a)
    (toModelSquare_base F a).symm

/-- Exact normalized equality on the complete generic square, retaining
both outer endpoints and the diagonal. -/
theorem generic_source_normalized (ha : a ≠ 0) :
    scalarSection (↑(genericParameter_isUnit F a ha).unit⁻¹ : RingSections (Square F a) ⊤) ≫
      pullSection (toModelSquare F a) (ModelNumerator.numerator F a) ≫
        ModelDifferential.squareVelocity F a (toModelSquare F a) =
      pullSection (ModelBivector.canonicalPair F a (toModelSquare F a)) (sourceBivector Lines.P) := by
  rw [generic_source_denominatorCleared F a ha, ← Category.assoc, ← scalarSection_mul,
    (genericParameter_isUnit F a ha).val_inv_mul, scalarSection_one, Category.id_comp]

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

namespace CartesianDifferential

open ContactDerivativeIsoProof

theorem sameBase {C D B : Scheme} (piC : C ⟶ B) (piD : D ⟶ B)
    (r : C ⟶ D) (hr : r ≫ piD = piC)
    (h : r ≫ piD = piC ≫ 𝟙 B) :
    RelativeDifferential.cotangent piC piD r (𝟙 B) h =
      cotangentMap r piD ≫ eqToHom (congrArg cotangentSheaf hr) := by
  apply RelativeDifferential.pulledCotangent_hom_ext r piD
  intro U z
  change (RelativeDifferential.cotangent piC piD r (𝟙 B) h).app (r ⁻¹ᵁ U)
      (pullLocalSection r (cotangentSheaf piD) U
        ((cotangentPresentation piD).differential.apply U z)) =
    (eqToHom (congrArg cotangentSheaf hr)).app (r ⁻¹ᵁ U)
      ((cotangentMap r piD).app (r ⁻¹ᵁ U)
        (pullLocalSection r (cotangentSheaf piD) U
          ((cotangentPresentation piD).differential.apply U z)))
  rw [RelativeDifferential.cotangent_differential,
    cotangentMap_differential, differential_transport]

/-- Canonical relative differentials are isomorphisms on every
Cartesian source square, including a separately named source model. -/
theorem isIso_of_isPullback {C A D B : Scheme}
    (piC : C ⟶ A) (piD : D ⟶ B) (r : C ⟶ D) (b : A ⟶ B)
    (h : IsPullback r piC piD b) :
    IsIso (RelativeDifferential.cotangent piC piD r b h.w) := by
  let i := h.isoPullback
  have hi : i.hom ≫ pullback.snd piD b = piC := h.isoPullback_hom_snd
  have hj : i.hom ≫ pullback.snd piD b = piC ≫ 𝟙 A := by
    simpa only [Category.comp_id] using hi
  letI := openImmersion_cotangentMap_isIso i.hom (pullback.snd piD b)
  haveI : IsIso (RelativeDifferential.cotangent piC (pullback.snd piD b)
      i.hom (𝟙 A) hj) := by
    rw [sameBase piC (pullback.snd piD b) i.hom hi hj]
    infer_instance
  letI := LeBrunSalamon.StandardInputs.cotangentPullback_isIso piD b
  have hh : (i.hom ≫ pullback.fst piD b) ≫ piD = piC ≫ ((𝟙 A) ≫ b) := by
    rw [h.isoPullback_hom_fst, Category.id_comp]
    exact h.w
  have hc := RelativeDifferential.cotangent_comp piC (pullback.snd piD b) piD
    i.hom (𝟙 A) (pullback.fst piD b) b hj pullback.condition hh
  rw [RelativeDifferential.cotangent_baseChange,
    RelativeDifferential.cotangent_congr piC piD h.isoPullback_hom_fst
      (Category.id_comp b) hh h.w] at hc
  have hc' : (compositionPullback i.hom (pullback.fst piD b) r
      h.isoPullback_hom_fst (cotangentSheaf piD)).hom ≫
        RelativeDifferential.cotangent piC piD r b h.w =
      (Scheme.Modules.pullback i.hom).map (CotangentBaseChange.canonicalMap piD b) ≫
        RelativeDifferential.cotangent piC (pullback.snd piD b) i.hom (𝟙 A) hj := by
    simpa only [compositionPullback, Iso.trans_hom, Iso.app_hom,
      eqToIso.hom, Category.assoc] using hc
  haveI : IsIso ((compositionPullback i.hom (pullback.fst piD b) r
      h.isoPullback_hom_fst (cotangentSheaf piD)).hom ≫
        RelativeDifferential.cotangent piC piD r b h.w) := by
    rw [hc']
    infer_instance
  exact IsIso.of_isIso_comp_left _ _

/-- An arbitrary actual source form factors through the relative
derivative of a parametrized target map, with no scalar normalization. -/
theorem fromForm_factor {B : Scheme} (P : ProjectiveLineOverC)
    (sB : B ⟶ ComplexBase) (M : OModule (Parametrized.Source P sB))
    (q : cotangentSheaf (Parametrized.parameter P sB) ⟶ dualSheaf M)
    {d : ℕ} (X : SmoothProperComplexVariety d)
    (e : Parametrized.Source P sB ⟶ X.scheme)
    (he : e ≫ X.structureMap = Parametrized.parameter P sB ≫ sB) :
    LogVelocity.fromForm (Parametrized.parameter P sB) sB M q
      (projectiveLineVariety P) (Parametrized.projection P sB) pullback.condition ≫
        Parametrized.differential P sB X e he =
      LogVelocity.fromForm (Parametrized.parameter P sB) sB M q X e he := by
  letI := dualBaseChange_isIso (Parametrized.projection P sB)
    (smooth_cotangent_rank P.structureMap 1 (projectiveLineVariety P).smooth)
  letI := LeBrunSalamon.StandardInputs.cotangentPullback_isIso P.structureMap sB
  simp only [LogVelocity.fromForm, Parametrized.differential, Category.assoc,
    IsIso.inv_hom_id_assoc]
  rw [← transpose_comp]
  have hcot : Parametrized.relativeCotangent P sB X e he ≫
      (RelativeDifferential.cotangent (Parametrized.parameter P sB) P.structureMap
        (Parametrized.projection P sB) sB pullback.condition ≫ q) =
      RelativeDifferential.cotangent (Parametrized.parameter P sB) X.structureMap
        e sB he ≫ q := by
    change (Parametrized.relativeCotangentMap P sB X e he ≫
      inv (CotangentBaseChange.canonicalMap P.structureMap sB)) ≫
        (CotangentBaseChange.canonicalMap P.structureMap sB ≫ q) =
          Parametrized.relativeCotangentMap P sB X e he ≫ q
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  rw [hcot]

theorem fromForm_congr {S B : Scheme} (pi : S ⟶ B) (sB : B ⟶ ComplexBase)
    (M : OModule S) (q : cotangentSheaf pi ⟶ dualSheaf M)
    {d : ℕ} (X : SmoothProperComplexVariety d) (e e' : S ⟶ X.scheme)
    (h : e = e') (he : e ≫ X.structureMap = pi ≫ sB)
    (he' : e' ≫ X.structureMap = pi ≫ sB) :
    LogVelocity.fromForm pi sB M q X e he ≫
      eqToHom (congrArg (fun f => pullbackModule f (tangentSheaf X.structureMap)) h) =
        LogVelocity.fromForm pi sB M q X e' he' := by
  subst e'
  simp only [eqToHom_refl, Category.comp_id]

/-- Named-target form of logarithmic velocity base change. -/
theorem fromForm_baseChange_named {S B S' B' : Scheme}
    (pi : S ⟶ B) (pi' : S' ⟶ B') (sB : B ⟶ ComplexBase)
    (r : S' ⟶ S) (b : B' ⟶ B) (hr : r ≫ pi = pi' ≫ b)
    (M : OModule S)
    (C : pullbackModule r (cotangentSheaf pi) ≅ cotangentSheaf pi')
    (hC : C.hom = RelativeDifferential.cotangent pi' pi r b hr)
    (q : cotangentSheaf pi ⟶ dualSheaf M)
    {d : ℕ} (X : SmoothProperComplexVariety d)
    (e : S ⟶ X.scheme) (e' : S' ⟶ X.scheme) (hre : r ≫ e = e')
    (he : e ≫ X.structureMap = pi ≫ sB)
    (he' : e' ≫ X.structureMap = pi' ≫ (b ≫ sB)) :
    (Scheme.Modules.pullback r).map (LogVelocity.fromForm pi sB M q X e he) ≫
      (compositionPullback r e e' hre (tangentSheaf X.structureMap)).hom =
    LogVelocity.fromForm pi' (b ≫ sB) (pullbackModule r M)
      (LogVelocity.pulledForm pi pi' r M (pullbackModule r M) C (Iso.refl _) q)
      X e' he' := by
  have hec : (r ≫ e) ≫ X.structureMap = pi' ≫ (b ≫ sB) := by
    rw [hre]
    exact he'
  have hb := LogVelocity.fromForm_baseChange pi pi' sB r b hr M
    (pullbackModule r M) C hC (Iso.refl _) q X e he hec
  have hh := fromForm_congr pi' (b ≫ sB) (pullbackModule r M)
    (LogVelocity.pulledForm pi pi' r M (pullbackModule r M) C (Iso.refl _) q)
    X (r ≫ e) e' hre hec he'
  rw [hb] at hh
  simpa only [Iso.refl_inv, Category.id_comp, compositionPullback,
    Iso.trans_hom, Iso.app_hom, eqToIso.hom, Category.assoc] using hh

end CartesianDifferential

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

/-- Base change of the actual three-term model numerator, after any
specified pair of maps out of its logarithmic line. -/
theorem numerator_transport (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    pullSection (parametrizedToModelSquare F a ha)
      (ModelNumerator.numerator F a ≫
        RelativeSquare.boxMap (modelProjection F a) uB vB ≫
          RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom =
      genericNumerator F a ha ≫ RelativeSquare.boxMap p1Parameter uA vA ≫
        RelativeSquare.comparison p1Parameter sY genericBase eA heA E H := by
  let k := genericParametrization F a ha
  let q := parametrizedToModelSquare F a ha
  have hp (s t : AlgebraicSection (modelLine F a).sheaf) :=
    RelativeSquare.product_baseChange p1Parameter (modelProjection F a)
      sY genericBase toC eA eB heA heB k hke q
      (RelativeSquare.map_left _ _ _ _ _) (RelativeSquare.map_right _ _ _ _ _)
      (RelativeSquare.map_evaluation p1Parameter (modelProjection F a) k genericPoint
        (genericParametrization_parameter F a ha) sY genericBase toC eA eB heA heB hke)
      (s ≫ uB) (t ≫ vB) (pullSection k s ≫ uA) (pullSection k t ≫ vA)
      (by rw [pullSection_naturality, Category.assoc, hu])
      (by rw [pullSection_naturality, Category.assoc, hv])
  have hadd {V : OModule (ModelNumerator.Square F a)}
      (s t : AlgebraicSection V) : pullSection q (s + t) = pullSection q s + pullSection q t := by
    simp only [pullSection, restrictSection, Functor.map_add, Preadditive.comp_add]
  unfold genericNumerator ModelNumerator.numerator
  rw [section_scale]
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Normalization.pullSection_sub,
    hadd, Category.assoc, LogVelocity.pullSection_scalar]
  simp only [RelativeBox.section, ← RelativeSquare.productSection_map]
  rw [hp, hp, hp]
  simp only [genericCoordinate, genericCoefficient, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, map_mul, map_ofNat, k, q, Category.assoc]

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

namespace TensorScalar

theorem right {Y : Scheme} {E E' H H' : OModule Y}
    (r : RingSections Y ⊤) (u : E ⟶ E') (v : H ⟶ H') :
    tensorMap u (GlobalScalars.scalarEnd H r ≫ v) =
      GlobalScalars.scalarEnd (tensorSheaf E H) r ≫ tensorMap u v := by
  apply ((tensorPresentation E H).universal _).1
  apply sheafBilinearMap_ext
  intro U x y
  change (tensorMap u (GlobalScalars.scalarEnd H r ≫ v)).app U
      ((tensorPresentation E H).pair.apply U x y) =
    (tensorMap u v).app U
      ((GlobalScalars.scalarEnd (tensorSheaf E H) r).app U
        ((tensorPresentation E H).pair.apply U x y))
  rw [tensorMap_apply, GlobalScalars.scalarEnd_app, map_smul, tensorMap_apply]
  simp only [GlobalScalars.scalarEnd_app, map_smul, LinearMap.smul_apply]

theorem «section» {Y : Scheme} {E : OModule Y} (s : AlgebraicSection E)
    (r : RingSections Y ⊤) :
    s ≫ GlobalScalars.scalarEnd E r = scalarSection r ≫ s := by
  rw [← section_scale]
  apply (sectionValue_bijective E).injective
  rw [sectionValue_comp, sectionFromValue_spec]
  simp only [GlobalScalars.scalarEnd_app, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, CommRingCat.id_apply]

theorem relative_right {C B : Scheme} (pi : C ⟶ B)
    {E E' H H' : OModule C} (r : RingSections B ⊤)
    (u : E ⟶ E') (v : H ⟶ H') (s : AlgebraicSection (RelativeSquare.box pi E H)) :
    s ≫ RelativeSquare.boxMap pi u (GlobalScalars.scalarEnd H (pi.appTop r) ≫ v) =
      scalarSection ((RelativeSquare.left pi ≫ pi).appTop r) ≫
        s ≫ RelativeSquare.boxMap pi u v := by
  have hr : (RelativeSquare.right pi).appTop (pi.appTop r) =
      (RelativeSquare.left pi ≫ pi).appTop r := by
    change (RelativeSquare.right pi ≫ pi).appTop r = _
    rw [← pullback.condition]
  unfold RelativeSquare.boxMap
  rw [Functor.map_comp, LineEndomorphisms.scalarEnd_pullback, hr, right,
    ← Category.assoc, «section»]
  simp only [Category.assoc]

theorem relative_left {C B : Scheme} (pi : C ⟶ B)
    {E E' H H' : OModule C} (r : RingSections B ⊤)
    (u : E ⟶ E') (v : H ⟶ H') (s : AlgebraicSection (RelativeSquare.box pi E H)) :
    s ≫ RelativeSquare.boxMap pi (GlobalScalars.scalarEnd E (pi.appTop r) ≫ u) v =
      scalarSection ((RelativeSquare.left pi ≫ pi).appTop r) ≫
        s ≫ RelativeSquare.boxMap pi u v := by
  rw [ScalarTensor.relative_move, relative_right]

end TensorScalar

def genericBaseCoefficient : RingSections GenericPoint ⊤ :=
  genericPoint.appTop (coefficientSection a)

theorem genericCoefficient_base (ha : a ≠ 0) :
    (RelativeSquare.left p1Parameter ≫ p1Parameter).appTop (genericBaseCoefficient a) =
      genericCoefficient F a ha := by
  change ((RelativeSquare.left p1Parameter ≫ p1Parameter) ≫ genericPoint).appTop
    (coefficientSection a) = _
  have hm : (RelativeSquare.left p1Parameter ≫ p1Parameter) ≫ genericPoint =
      parametrizedToModelSquare F a ha ≫ ModelNumerator.squareProjection F a :=
    (parametrizedToModelSquare_base F a ha).symm
  exact congrArg (fun k => k.appTop (coefficientSection a)) hm

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
