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
  change pullSection f (RelativeBox.section (modelProjection F a) s t ≫
      modelSourceMorphism F a) ≫
    (compositionPullback f (modelSourceSquare F a) (ModelBivector.canonicalPair F a f)
      (canonicalPair_eq F a f)
      (externalTensor Lines.P.structureMap (tangentSheaf Lines.P.structureMap)
        (tangentSheaf Lines.P.structureMap))).hom =
    pullSection f (RelativeBox.section (modelProjection F a) s t) ≫
      ModelDifferential.squareVelocity F a f
  let P : pullbackModule (ModelBivector.canonicalPair F a f)
      (externalTensor Lines.P.structureMap (tangentSheaf Lines.P.structureMap)
        (tangentSheaf Lines.P.structureMap)) ≅
    tensorSheaf
      (pullbackModule (ModelBivector.gaugedPoint F a (ModelBivector.firstPoint F a f))
        (tangentSheaf Lines.P.structureMap))
      (pullbackModule (ModelBivector.gaugedPoint F a (ModelBivector.secondPoint F a f))
        (tangentSheaf Lines.P.structureMap)) :=
    SourceBivectorCoordinates.TestMaps.pairPullIso (ModelBivector.base F a f)
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
  simpa only [modelSourceMorphism, modelSourceSquare, RelativeSquare.productSection,
    RelativeBox.section, ModelBivector.firstPoint, ModelBivector.secondPoint,
    RelativeSquare.left, RelativeSquare.right, RelativeBox.first, RelativeBox.second,
    Category.assoc] using h

theorem section_scale {Y : Scheme} {E : OModule Y}
    (r : RingSections Y ⊤) (s : AlgebraicSection E) :
    sectionFromValue (r • sectionValue s) = scalarSection r ≫ s := by
  apply (sectionValue_bijective E).injective
  rw [sectionFromValue_spec, sectionValue_comp, scalarSection, sectionFromValue_spec]
  change r • Scheme.Modules.Hom.app s ⊤ (1 : RingSections Y ⊤) =
    Scheme.Modules.Hom.app s ⊤ r
  simpa only [smul_eq_mul, mul_one] using
    (Scheme.Modules.Hom.app_smul s r (1 : RingSections Y ⊤)).symm

end LeBrunSalamon.Construction.TraitContact.ModelGenericComparison

end
