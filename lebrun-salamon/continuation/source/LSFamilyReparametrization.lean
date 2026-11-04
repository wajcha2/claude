import LSFiniteTypeSpreading
import LSContactLineTests
import LSFamilyDescentReparametrization

/-!
# Reparametrization in families and over arbitrary fields

Complex-point detection is used only on reduced schemes locally of
finite type over C.  A field-valued source automorphism is first spread
while retaining the original parameterized family; the tensor identities
then return along the actual field-valued base map.
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

namespace LeBrunSalamon.Construction.FamilyBivectors

namespace SectionTransport

/-- A compatible reparametrization identity on an entire fibre gives
the same identity after pulling the two family sections to that fibre. -/
theorem reparametrization_on_fibre {T Y Z : Scheme}
    (i : T ⟶ Y) (a : Y ⟶ Y) (e : T ⟶ T) (hia : i ≫ a = e ≫ i)
    (f g : Y ⟶ Z) (haf : a ≫ f = g)
    (f₀ g₀ : T ⟶ Z) (hif : i ≫ f = f₀) (hig : i ≫ g = g₀)
    (hef : e ≫ f₀ = g₀) {E : OModule Z}
    (s : AlgebraicSection (pullbackModule f E))
    (t : AlgebraicSection (pullbackModule g E))
    (s₀ : AlgebraicSection (pullbackModule f₀ E))
    (t₀ : AlgebraicSection (pullbackModule g₀ E))
    (hs : pullSection i s ≫ (compositionPullback i f f₀ hif E).hom = s₀)
    (ht : pullSection i t ≫ (compositionPullback i g g₀ hig E).hom = t₀)
    (he : pullSection e s₀ ≫ (compositionPullback e f₀ g₀ hef E).hom = t₀) :
    pullSection i (pullSection a s ≫ (compositionPullback a f g haf E).hom) =
      pullSection i t := by
  have heif : (e ≫ i) ≫ f = g₀ := by rw [Category.assoc, hif, hef]
  apply (cancel_mono (compositionPullback i g g₀ hig E).hom).mp
  rw [pullSection_naturality]
  simp only [Category.assoc]
  rw [composition_assoc i a f (e ≫ i) g g₀ hia haf hig heif E,
    ← Category.assoc, compositionPullback_sections]
  rw [pull_specialization e i f (e ≫ i) f₀ g₀ rfl hif hef heif s s₀ hs,
    he, ht]

/-- An already proved reparametrization identity survives arbitrary
base change.  No density or point-detection hypothesis occurs here. -/
theorem reparametrization_baseChange {T Y Z : Scheme}
    (i : T ⟶ Y) (a : Y ⟶ Y) (e : T ⟶ T) (hia : i ≫ a = e ≫ i)
    (f g : Y ⟶ Z) (haf : a ≫ f = g)
    (f₀ g₀ : T ⟶ Z) (hif : i ≫ f = f₀) (hig : i ≫ g = g₀)
    (hef : e ≫ f₀ = g₀) {E : OModule Z}
    (s : AlgebraicSection (pullbackModule f E))
    (t : AlgebraicSection (pullbackModule g E))
    (s₀ : AlgebraicSection (pullbackModule f₀ E))
    (t₀ : AlgebraicSection (pullbackModule g₀ E))
    (hs : pullSection i s ≫ (compositionPullback i f f₀ hif E).hom = s₀)
    (ht : pullSection i t ≫ (compositionPullback i g g₀ hig E).hom = t₀)
    (h : pullSection a s ≫ (compositionPullback a f g haf E).hom = t) :
    pullSection e s₀ ≫ (compositionPullback e f₀ g₀ hef E).hom = t₀ := by
  have heif : (e ≫ i) ≫ f = g₀ := by rw [Category.assoc, hif, hef]
  have hc := congrArg (fun v => pullSection i v ≫
    (compositionPullback i g g₀ hig E).hom) h
  rw [ht, pullSection_naturality] at hc
  simp only [Category.assoc] at hc
  rw [composition_assoc i a f (e ≫ i) g g₀ hia haf hig heif E,
    ← Category.assoc, compositionPullback_sections,
    pull_specialization e i f (e ≫ i) f₀ g₀ rfl hif hef heif s s₀ hs] at hc
  exact hc

end SectionTransport

namespace FamilyReparametrization

open Parametrized

variable (P : ProjectiveLineOverC) {B : Scheme} (sB : B ⟶ ComplexBase)

abbrev BasePoint := PointsOver ComplexBase (𝟙 ComplexBase) B sB

def inclusion (t : BasePoint sB) : ProjectiveLine ⟶ Source P sB :=
  pullback.lift (𝟙 ProjectiveLine) (P.structureMap ≫ t.val) (by
    simp only [Category.id_comp, Category.assoc, t.property, Category.comp_id])

@[reassoc] theorem inclusion_projection (t : BasePoint sB) :
    inclusion P sB t ≫ projection P sB = 𝟙 ProjectiveLine := pullback.lift_fst _ _ _

@[reassoc] theorem inclusion_parameter (t : BasePoint sB) :
    inclusion P sB t ≫ parameter P sB = P.structureMap ≫ t.val :=
  pullback.lift_snd _ _ _

def fibreSquare (t : BasePoint sB) : SelfProduct P.structureMap ⟶ Square P sB :=
  squareAtSection P sB t.val (inclusion P sB t) (inclusion_parameter P sB t)

@[reassoc] theorem fibreSquare_left (t : BasePoint sB) :
    fibreSquare P sB t ≫ RelativeSquare.left (parameter P sB) =
      firstProjection P.structureMap ≫ inclusion P sB t :=
  squareAtSection_left P sB t.val _ _

@[reassoc] theorem fibreSquare_right (t : BasePoint sB) :
    fibreSquare P sB t ≫ RelativeSquare.right (parameter P sB) =
      secondProjection P.structureMap ≫ inclusion P sB t :=
  squareAtSection_right P sB t.val _ _

abbrev squareToC : Square P sB ⟶ ComplexBase :=
  RelativeSquare.left (parameter P sB) ≫ parameter P sB ≫ sB

abbrev SquarePoint := PointsOver ComplexBase (𝟙 ComplexBase) (Square P sB) (squareToC P sB)

def basePoint (z : SquarePoint P sB) : BasePoint sB :=
  ⟨z.val ≫ RelativeSquare.left (parameter P sB) ≫ parameter P sB,
    by simpa only [Category.assoc] using z.property⟩

def coordinates (z : SquarePoint P sB) : ComplexBase ⟶ SelfProduct P.structureMap :=
  z.val ≫ sourceSquare P sB

@[reassoc] theorem coordinates_left (z : SquarePoint P sB) :
    coordinates P sB z ≫ firstProjection P.structureMap =
      z.val ≫ RelativeSquare.left (parameter P sB) ≫ projection P sB := by
  simp only [coordinates, sourceSquare, Category.assoc, RelativeSquare.evaluation_left]

@[reassoc] theorem coordinates_right (z : SquarePoint P sB) :
    coordinates P sB z ≫ secondProjection P.structureMap =
      z.val ≫ RelativeSquare.right (parameter P sB) ≫ projection P sB := by
  simp only [coordinates, sourceSquare, Category.assoc, RelativeSquare.evaluation_right]

theorem sourcePoint_factor (t : BasePoint sB)
    (a : ComplexBase ⟶ Source P sB) (ha : a ≫ parameter P sB = t.val) :
    (a ≫ projection P sB) ≫ inclusion P sB t = a := by
  have hz : (a ≫ projection P sB) ≫ P.structureMap = 𝟙 ComplexBase := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha, t.property]
  apply pullback.hom_ext
  · simp only [Category.assoc, inclusion_projection, Category.comp_id]
  · rw [Category.assoc, inclusion_parameter, ← Category.assoc, hz,
      Category.id_comp, ha]

@[reassoc] theorem point_factorization (z : SquarePoint P sB) :
    coordinates P sB z ≫ fibreSquare P sB (basePoint P sB z) = z.val := by
  apply pullback.hom_ext
  · rw [Category.assoc, fibreSquare_left, ← Category.assoc, coordinates_left]
    apply sourcePoint_factor P sB (basePoint P sB z)
    rfl
  · rw [Category.assoc, fibreSquare_right, ← Category.assoc, coordinates_right]
    apply sourcePoint_factor P sB (basePoint P sB z)
    simpa only [basePoint, Category.assoc] using congrArg (fun f => z.val ≫ f)
      (pullback.condition (f := parameter P sB) (g := parameter P sB)).symm

/-- Whole-fibre equality detects family sections only under the actual
reduced and locally-finite-type hypotheses required by point detection. -/
theorem sections_eq_of_fibres [AlgebraicGeometry.IsReduced (Square P sB)]
    [LocallyOfFiniteType (squareToC P sB)] {r : ℕ}
    (E : AlgebraicVectorBundle (Square P sB) r)
    (a b : AlgebraicSection E.sheaf)
    (h : ∀ t : BasePoint sB,
      pullSection (fibreSquare P sB t) a = pullSection (fibreSquare P sB t) b) : a = b := by
  apply ComplexPointSectionDetection.section_eq (squareToC P sB) E
  intro z
  have hz := congrArg (fun v => pullSection (coordinates P sB z) v ≫
    (compositionPullback (coordinates P sB z)
      (fibreSquare P sB (basePoint P sB z)) z.val
      (point_factorization P sB z) E.sheaf).hom) (h (basePoint P sB z))
  simpa only [compositionPullback_sections] using hz

theorem square_reduced [AlgebraicGeometry.IsReduced B] [LocallyOfFiniteType sB] :
    AlgebraicGeometry.IsReduced (Square P sB) := by
  letI : Smooth P.structureMap := smoothProperComplexVariety_smooth (projectiveLineVariety P)
  letI : ConnectedSpace ProjectiveLine := (projectiveLineVariety P).connected
  letI : GeometricallyIntegral P.structureMap :=
    LeBrunSalamon.StandardInputs.smooth_connected_complex_geometricallyIntegral P.structureMap
  letI : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian sB
  letI : AlgebraicGeometry.IsReduced (Source P sB) := inferInstance
  letI : IsLocallyNoetherian (Source P sB) :=
    LocallyOfFiniteType.isLocallyNoetherian (parameter P sB)
  change AlgebraicGeometry.IsReduced (pullback (parameter P sB) (parameter P sB))
  infer_instance

theorem square_locallyOfFiniteType [LocallyOfFiniteType sB] :
    LocallyOfFiniteType (squareToC P sB) := by
  letI : Smooth P.structureMap := smoothProperComplexVariety_smooth (projectiveLineVariety P)
  dsimp only [squareToC, RelativeSquare.left, parameter]
  infer_instance

/-- The original nonconstant curves on every complex fibre, with
their actual whole-source evaluation identities. -/
structure NonconstantFamily {n : ℕ} (X : ContactFanoManifold n)
    (f : Source P sB ⟶ X.variety.scheme) where
  curve : BasePoint sB → RationalCurve P X.variety
  curve_spec : ∀ t, inclusion P sB t ≫ f = (curve t).map

variable (e : Source P sB ≅ Source P sB)
variable (he : e.hom ≫ parameter P sB = parameter P sB)

include he in
theorem inverse_parameter : e.inv ≫ parameter P sB = parameter P sB := by
  calc
    _ = e.inv ≫ (e.hom ≫ parameter P sB) := congrArg (fun f => e.inv ≫ f) he.symm
    _ = _ := by rw [← Category.assoc, e.inv_hom_id, Category.id_comp]

def fibreHom (t : BasePoint sB) : ProjectiveLine ⟶ ProjectiveLine :=
  inclusion P sB t ≫ e.hom ≫ projection P sB

include he in
@[reassoc] theorem fibreHom_overC (t : BasePoint sB) :
    fibreHom P sB e t ≫ P.structureMap = P.structureMap := by
  simp only [fibreHom, Category.assoc, projection, pullback.condition]
  rw [← Category.assoc e.hom, he, ← Category.assoc, inclusion_parameter,
    Category.assoc, t.property, Category.comp_id]

include he in
@[reassoc] theorem fibreHom_inclusion (t : BasePoint sB) :
    fibreHom P sB e t ≫ inclusion P sB t = inclusion P sB t ≫ e.hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, inclusion_projection, Category.comp_id, fibreHom]
  · rw [Category.assoc, inclusion_parameter, ← Category.assoc,
      fibreHom_overC P sB e he t, Category.assoc, he, inclusion_parameter]

def fibreIso (t : BasePoint sB) : ProjectiveLine ≅ ProjectiveLine where
  hom := fibreHom P sB e t
  inv := fibreHom P sB e.symm t
  hom_inv_id := by
    change fibreHom P sB e t ≫ (inclusion P sB t ≫ e.inv ≫ projection P sB) = _
    rw [← Category.assoc, fibreHom_inclusion P sB e he t]
    simp only [Category.assoc, e.hom_inv_id_assoc, inclusion_projection]
  inv_hom_id := by
    change fibreHom P sB e.symm t ≫ (inclusion P sB t ≫ e.hom ≫ projection P sB) = _
    rw [← Category.assoc,
      fibreHom_inclusion P sB e.symm (inverse_parameter P sB e he) t]
    simp only [Category.assoc, e.inv_hom_id_assoc, inclusion_projection]

@[reassoc] theorem fibreIso_overC (t : BasePoint sB) :
    (fibreIso P sB e he t).hom ≫ P.structureMap = P.structureMap :=
  fibreHom_overC P sB e he t

def squareMap : Square P sB ⟶ Square P sB :=
  RelativeSquare.map (parameter P sB) (parameter P sB) e.hom (𝟙 B)
    (by simpa only [Category.comp_id] using he)

@[reassoc] theorem squareMap_left :
    squareMap P sB e he ≫ RelativeSquare.left (parameter P sB) =
      RelativeSquare.left (parameter P sB) ≫ e.hom :=
  RelativeSquare.map_left _ _ _ _ _

@[reassoc] theorem squareMap_right :
    squareMap P sB e he ≫ RelativeSquare.right (parameter P sB) =
      RelativeSquare.right (parameter P sB) ≫ e.hom :=
  RelativeSquare.map_right _ _ _ _ _

@[reassoc] theorem fibreSquare_squareMap (t : BasePoint sB) :
    fibreSquare P sB t ≫ squareMap P sB e he =
      curveSquareMap P (Reparametrization.curve P (fibreIso P sB e he t)
        (fibreIso_overC P sB e he t)) ≫ fibreSquare P sB t := by
  apply pullback.hom_ext
  · simp only [Category.assoc, squareMap_left, fibreSquare_left_assoc,
      fibreSquare_left, curveSquareMap_first_assoc]
    rw [fibreHom_inclusion P sB e he t]
  · simp only [Category.assoc, squareMap_right, fibreSquare_right_assoc,
      fibreSquare_right, curveSquareMap_second_assoc]
    rw [fibreHom_inclusion P sB e he t]

def reparametrizeCurve {n : ℕ} (X : ContactFanoManifold n)
    (f : RationalCurve P X.variety) (a : ProjectiveLine ≅ ProjectiveLine)
    (ha : a.hom ≫ P.structureMap = P.structureMap) : RationalCurve P X.variety where
  map := a.hom ≫ f.map
  overC := by rw [Category.assoc, f.overC, ha]
  nonconstant := by
    rintro ⟨x, hx, hc⟩
    apply f.nonconstant
    refine ⟨x, hx, ?_⟩
    calc
      f.map = a.inv ≫ (a.hom ≫ f.map) := by simp only [Iso.inv_hom_id_assoc]
      _ = a.inv ≫ (P.structureMap ≫ x) := congrArg (fun z => a.inv ≫ z) hc
      _ = P.structureMap ≫ x := by
        rw [← Category.assoc, SourceReparamProof.inverse_overC P a ha]

variable {n : ℕ} (X : ContactFanoManifold n)
variable (f : Source P sB ⟶ X.variety.scheme)
variable (hf : f ≫ X.variety.structureMap = parameter P sB ≫ sB)
variable (C : NonconstantFamily P sB X f)
variable (g : Source P sB ⟶ X.variety.scheme)
variable (hg : g ≫ X.variety.structureMap = parameter P sB ≫ sB)
variable (hcomp : e.hom ≫ f = g)

def reparametrizedFamily : NonconstantFamily P sB X g where
  curve t := reparametrizeCurve P X (C.curve t) (fibreIso P sB e he t)
    (fibreIso_overC P sB e he t)
  curve_spec t := by
    change inclusion P sB t ≫ g = fibreHom P sB e t ≫ (C.curve t).map
    rw [← hcomp, ← Category.assoc,
      ← fibreHom_inclusion P sB e he t, Category.assoc, C.curve_spec]

include hcomp in
@[reassoc] theorem squareMap_evaluation :
    squareMap P sB e he ≫ ParametrizedContact.evaluationSquare P sB X f hf =
      ParametrizedContact.evaluationSquare P sB X g hg :=
  RelativeSquare.map_evaluation (parameter P sB) (parameter P sB) e.hom (𝟙 B)
    (by simpa only [Category.comp_id] using he) X.variety.structureMap sB sB
    g f hg hf hcomp

@[reassoc] theorem fibreSquare_evaluation (t : BasePoint sB) :
    fibreSquare P sB t ≫ ParametrizedContact.evaluationSquare P sB X f hf =
      curveSquareMap P (C.curve t) :=
  squareAtSection_evaluation P sB X.variety f hf t.val (inclusion P sB t)
    (inclusion_parameter P sB t) (C.curve t) (C.curve_spec t)

theorem left_at_fibre (t : BasePoint sB) :
    pullSection (fibreSquare P sB t) (ParametrizedContact.leftSection P sB X f hf) ≫
        (compositionPullback (fibreSquare P sB t)
          (ParametrizedContact.evaluationSquare P sB X f hf)
          (curveSquareMap P (C.curve t)) (fibreSquare_evaluation P sB X f hf C t)
          (movingPairBundleLeft X.variety X.contact)).hom =
      Curve.leftSection P X (C.curve t) :=
  ParametrizedContact.leftSection_atCurve P sB X f hf t.val t.property
    (inclusion P sB t) (inclusion_projection P sB t) (inclusion_parameter P sB t)
    (C.curve t) (C.curve_spec t)

theorem right_at_fibre (t : BasePoint sB) :
    pullSection (fibreSquare P sB t) (ParametrizedContact.rightSection P sB X f hf) ≫
        (compositionPullback (fibreSquare P sB t)
          (ParametrizedContact.evaluationSquare P sB X f hf)
          (curveSquareMap P (C.curve t)) (fibreSquare_evaluation P sB X f hf C t)
          (movingPairBundleRight X.variety X.contact)).hom =
      Curve.rightSection P X (C.curve t) :=
  ParametrizedContact.rightSection_atCurve P sB X f hf t.val t.property
    (inclusion P sB t) (inclusion_projection P sB t) (inclusion_parameter P sB t)
    (C.curve t) (C.curve_spec t)

include C in
/-- Actual reparametrization invariance over a reduced locally
finite-type base; the only point test is on its complete source square. -/
theorem leftSection_finiteType [AlgebraicGeometry.IsReduced B] [LocallyOfFiniteType sB] :
    pullSection (squareMap P sB e he) (ParametrizedContact.leftSection P sB X f hf) ≫
        (compositionPullback (squareMap P sB e he)
          (ParametrizedContact.evaluationSquare P sB X f hf)
          (ParametrizedContact.evaluationSquare P sB X g hg)
          (squareMap_evaluation P sB e he X f hf g hg hcomp)
          (movingPairBundleLeft X.variety X.contact)).hom =
      ParametrizedContact.leftSection P sB X g hg := by
  letI : AlgebraicGeometry.IsReduced (Square P sB) := square_reduced P sB
  letI : LocallyOfFiniteType (squareToC P sB) := square_locallyOfFiniteType P sB
  apply sections_eq_of_fibres P sB
    (MovingPair.leftBundle (ParametrizedContact.evaluationSquare P sB X g hg))
  intro t
  let D := reparametrizedFamily P sB e he X f C g hcomp
  let a := fibreIso P sB e he t
  have ha : a.hom ≫ P.structureMap = P.structureMap := fibreIso_overC P sB e he t
  have hg' : (D.curve t).map = a.hom ≫ (C.curve t).map := rfl
  exact SectionTransport.reparametrization_on_fibre (fibreSquare P sB t)
    (squareMap P sB e he) (curveSquareMap P (Reparametrization.curve P a ha))
    (fibreSquare_squareMap P sB e he t)
    (ParametrizedContact.evaluationSquare P sB X f hf)
    (ParametrizedContact.evaluationSquare P sB X g hg)
    (squareMap_evaluation P sB e he X f hf g hg hcomp)
    (curveSquareMap P (C.curve t)) (curveSquareMap P (D.curve t))
    (fibreSquare_evaluation P sB X f hf C t) (fibreSquare_evaluation P sB X g hg D t)
    (Reparametrization.square_comp P a ha X (C.curve t) (D.curve t) hg')
    (ParametrizedContact.leftSection P sB X f hf)
    (ParametrizedContact.leftSection P sB X g hg)
    (Curve.leftSection P X (C.curve t)) (Curve.leftSection P X (D.curve t))
    (left_at_fibre P sB X f hf C t) (left_at_fibre P sB X g hg D t)
    (Reparametrization.leftSection P a ha X (C.curve t) (D.curve t) hg')

include C in
theorem rightSection_finiteType [AlgebraicGeometry.IsReduced B] [LocallyOfFiniteType sB] :
    pullSection (squareMap P sB e he) (ParametrizedContact.rightSection P sB X f hf) ≫
        (compositionPullback (squareMap P sB e he)
          (ParametrizedContact.evaluationSquare P sB X f hf)
          (ParametrizedContact.evaluationSquare P sB X g hg)
          (squareMap_evaluation P sB e he X f hf g hg hcomp)
          (movingPairBundleRight X.variety X.contact)).hom =
      ParametrizedContact.rightSection P sB X g hg := by
  letI : AlgebraicGeometry.IsReduced (Square P sB) := square_reduced P sB
  letI : LocallyOfFiniteType (squareToC P sB) := square_locallyOfFiniteType P sB
  apply sections_eq_of_fibres P sB
    (MovingPair.rightBundle (ParametrizedContact.evaluationSquare P sB X g hg))
  intro t
  let D := reparametrizedFamily P sB e he X f C g hcomp
  let a := fibreIso P sB e he t
  have ha : a.hom ≫ P.structureMap = P.structureMap := fibreIso_overC P sB e he t
  have hg' : (D.curve t).map = a.hom ≫ (C.curve t).map := rfl
  exact SectionTransport.reparametrization_on_fibre (fibreSquare P sB t)
    (squareMap P sB e he) (curveSquareMap P (Reparametrization.curve P a ha))
    (fibreSquare_squareMap P sB e he t)
    (ParametrizedContact.evaluationSquare P sB X f hf)
    (ParametrizedContact.evaluationSquare P sB X g hg)
    (squareMap_evaluation P sB e he X f hf g hg hcomp)
    (curveSquareMap P (C.curve t)) (curveSquareMap P (D.curve t))
    (fibreSquare_evaluation P sB X f hf C t) (fibreSquare_evaluation P sB X g hg D t)
    (Reparametrization.square_comp P a ha X (C.curve t) (D.curve t) hg')
    (ParametrizedContact.rightSection P sB X f hf)
    (ParametrizedContact.rightSection P sB X g hg)
    (Curve.rightSection P X (C.curve t)) (Curve.rightSection P X (D.curve t))
    (right_at_fibre P sB X f hf C t) (right_at_fibre P sB X g hg D t)
    (Reparametrization.rightSection P a ha X (C.curve t) (D.curve t) hg')

end FamilyReparametrization

namespace FamilyReparametrization

open Parametrized

variable (P : ProjectiveLineOverC)

/-- Functoriality of the literal source-family map. -/
theorem sourceMap_comp {A B C : Scheme}
    {sA : A ⟶ ComplexBase} {sB : B ⟶ ComplexBase} {sC : C ⟶ ComplexBase}
    (a : PointsOver A sA B sB) (b : PointsOver B sB C sC)
    (c : PointsOver A sA C sC) (h : a.val ≫ b.val = c.val) :
    rationalSourceMap P a ≫ rationalSourceMap P b = rationalSourceMap P c := by
  apply pullback.hom_ext
  · simp only [rationalSourceMap, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [rationalSourceMap, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, h]

@[reassoc] theorem inclusion_sourceMap {A B : Scheme}
    (sA : A ⟶ ComplexBase) (sB : B ⟶ ComplexBase)
    (u : PointsOver A sA B sB) (t : BasePoint sA) :
    inclusion P sA t ≫ rationalSourceMap P u =
      inclusion P sB (⟨t.val ≫ u.val, by
        rw [Category.assoc, u.property, t.property]⟩ : BasePoint sB) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, rationalSourceMap, pullback.lift_fst, inclusion_projection]
  · simp only [Category.assoc, rationalSourceMap, pullback.lift_snd, inclusion_parameter]

theorem pulledEvaluation_overC {A B : Scheme}
    (sA : A ⟶ ComplexBase) (sB : B ⟶ ComplexBase)
    (u : PointsOver A sA B sB) {n : ℕ} (X : ContactFanoManifold n)
    (f : Source P sB ⟶ X.variety.scheme)
    (hf : f ≫ X.variety.structureMap = parameter P sB ≫ sB) :
    (rationalSourceMap P u ≫ f) ≫ X.variety.structureMap = parameter P sA ≫ sA := by
  rw [Category.assoc, hf, ← Category.assoc]
  simp only [rationalSourceMap, parameter, pullback.lift_snd_assoc,
    Category.assoc, u.property]

def pulledFamily {A B : Scheme}
    (sA : A ⟶ ComplexBase) (sB : B ⟶ ComplexBase)
    (u : PointsOver A sA B sB) {n : ℕ} (X : ContactFanoManifold n)
    (f : Source P sB ⟶ X.variety.scheme) (C : NonconstantFamily P sB X f) :
    NonconstantFamily P sA X (rationalSourceMap P u ≫ f) where
  curve t := C.curve ⟨t.val ≫ u.val, by rw [Category.assoc, u.property, t.property]⟩
  curve_spec t := by
    rw [← Category.assoc, inclusion_sourceMap]
    exact C.curve_spec _

/-- The entire square of a spread automorphism commutes with its
actual base-change map, including every diagonal point. -/
theorem squareMap_baseChange {A B : Scheme}
    (sA : A ⟶ ComplexBase) (sB : B ⟶ ComplexBase)
    (b : A ⟶ B) (k : Source P sA ⟶ Source P sB)
    (hk : k ≫ parameter P sB = parameter P sA ≫ b)
    (eA : Source P sA ≅ Source P sA)
    (heA : eA.hom ≫ parameter P sA = parameter P sA)
    (eB : Source P sB ≅ Source P sB)
    (heB : eB.hom ≫ parameter P sB = parameter P sB)
    (he : k ≫ eB.hom = eA.hom ≫ k) :
    RelativeSquare.map (parameter P sA) (parameter P sB) k b hk ≫
        squareMap P sB eB heB =
      squareMap P sA eA heA ≫
        RelativeSquare.map (parameter P sA) (parameter P sB) k b hk := by
  apply pullback.hom_ext
  · simp only [Category.assoc, squareMap_left, RelativeSquare.map_left,
      RelativeSquare.map_left_assoc, squareMap_left_assoc, he]
  · simp only [Category.assoc, squareMap_right, RelativeSquare.map_right,
      RelativeSquare.map_right_assoc, squareMap_right_assoc, he]

end FamilyReparametrization

namespace FamilyReparametrization

open Parametrized

variable (P : ProjectiveLineOverC) {B₀ : Scheme}
variable (s₀ : B₀ ⟶ ComplexBase) [LocallyOfFiniteType s₀]
variable {n : ℕ} (X : ContactFanoManifold n)
variable (f₀ : Source P s₀ ⟶ X.variety.scheme)
variable (hf₀ : f₀ ≫ X.variety.structureMap = parameter P s₀ ≫ s₀)
variable (C₀ : NonconstantFamily P s₀ X f₀)
variable (K : Type) [Field K] (sK : Spec (CommRingCat.of K) ⟶ ComplexBase)
variable (t : PointsOver (Spec (CommRingCat.of K)) sK B₀ s₀)
variable (f : Source P sK ⟶ X.variety.scheme)
variable (hf : f ≫ X.variety.structureMap = parameter P sK ≫ sK)
variable (htf : rationalSourceMap P t ≫ f₀ = f)
variable (e : Source P sK ≅ Source P sK)
variable (he : e.hom ≫ parameter P sK = parameter P sK)
variable (g : Source P sK ⟶ X.variety.scheme)
variable (hg : g ≫ X.variety.structureMap = parameter P sK ≫ sK)
variable (hcomp : e.hom ≫ f = g)

include hf₀ C₀ htf in
/-- Both normalized tensors are invariant under an arbitrary
field-valued reparametrization.  The given parameter point and the
original family are retained when spreading the automorphism. -/
theorem sections_field :
    (pullSection (squareMap P sK e he) (ParametrizedContact.leftSection P sK X f hf) ≫
        (compositionPullback (squareMap P sK e he)
          (ParametrizedContact.evaluationSquare P sK X f hf)
          (ParametrizedContact.evaluationSquare P sK X g hg)
          (squareMap_evaluation P sK e he X f hf g hg hcomp)
          (movingPairBundleLeft X.variety X.contact)).hom =
      ParametrizedContact.leftSection P sK X g hg) ∧
    (pullSection (squareMap P sK e he) (ParametrizedContact.rightSection P sK X f hf) ≫
        (compositionPullback (squareMap P sK e he)
          (ParametrizedContact.evaluationSquare P sK X f hf)
          (ParametrizedContact.evaluationSquare P sK X g hg)
          (squareMap_evaluation P sK e he X f hf g hg hcomp)
          (movingPairBundleRight X.variety X.contact)).hom =
      ParametrizedContact.rightSection P sK X g hg) := by
  letI : IsProper P.structureMap := ProjectiveLineProof.structureMap_proper P
  obtain ⟨B, sB, hBaff, hBint, hBft, u, hu, b, hbt, hb, eB, heB, hspread⟩ :=
    LeBrunSalamon.StandardInputs.proper_automorphism_spreads_with_parameter
      K sK P.structureMap s₀ t e he
  letI : IsIntegral B := hBint
  letI : LocallyOfFiniteType sB := hBft
  let u₀ : PointsOver B sB B₀ s₀ := ⟨u, hu⟩
  let tB : PointsOver (Spec (CommRingCat.of K)) sK B sB := ⟨b, hb⟩
  let k : Source P sK ⟶ Source P sB := rationalSourceMap P tB
  have hk₁ : k ≫ projection P sB = projection P sK := pullback.lift_fst _ _ _
  have hk₂ : k ≫ parameter P sB = parameter P sK ≫ b := pullback.lift_snd _ _ _
  have hkauto : k ≫ eB.hom = e.hom ≫ k := hspread
  let fB : Source P sB ⟶ X.variety.scheme := rationalSourceMap P u₀ ≫ f₀
  have hfB : fB ≫ X.variety.structureMap = parameter P sB ≫ sB :=
    pulledEvaluation_overC P sB s₀ u₀ X f₀ hf₀
  let CB : NonconstantFamily P sB X fB := pulledFamily P sB s₀ u₀ X f₀ C₀
  let gB : Source P sB ⟶ X.variety.scheme := eB.hom ≫ fB
  have hgB : gB ≫ X.variety.structureMap = parameter P sB ≫ sB := by
    change (eB.hom ≫ fB) ≫ X.variety.structureMap = _
    rw [Category.assoc, hfB, ← Category.assoc, heB]
  have hkf : k ≫ fB = f := by
    change rationalSourceMap P tB ≫ (rationalSourceMap P u₀ ≫ f₀) = f
    rw [← Category.assoc, sourceMap_comp P tB u₀ t hbt, htf]
  have hkg : k ≫ gB = g := by
    change k ≫ (eB.hom ≫ fB) = g
    rw [← Category.assoc, hkauto, Category.assoc, hkf, hcomp]
  let q : Square P sK ⟶ Square P sB :=
    RelativeSquare.map (parameter P sK) (parameter P sB) k b hk₂
  have hq₁ : q ≫ RelativeSquare.left (parameter P sB) =
      RelativeSquare.left (parameter P sK) ≫ k := RelativeSquare.map_left _ _ _ _ _
  have hq₂ : q ≫ RelativeSquare.right (parameter P sB) =
      RelativeSquare.right (parameter P sK) ≫ k := RelativeSquare.map_right _ _ _ _ _
  have hqf : q ≫ ParametrizedContact.evaluationSquare P sB X fB hfB =
      ParametrizedContact.evaluationSquare P sK X f hf :=
    RelativeSquare.map_evaluation (parameter P sK) (parameter P sB) k b hk₂
      X.variety.structureMap sK sB f fB hf hfB hkf
  have hqg : q ≫ ParametrizedContact.evaluationSquare P sB X gB hgB =
      ParametrizedContact.evaluationSquare P sK X g hg :=
    RelativeSquare.map_evaluation (parameter P sK) (parameter P sB) k b hk₂
      X.variety.structureMap sK sB g gB hg hgB hkg
  have hqa : q ≫ squareMap P sB eB heB = squareMap P sK e he ≫ q :=
    squareMap_baseChange P sK sB b k hk₂ e he eB heB hkauto
  constructor
  · exact SectionTransport.reparametrization_baseChange q
      (squareMap P sB eB heB) (squareMap P sK e he) hqa
      (ParametrizedContact.evaluationSquare P sB X fB hfB)
      (ParametrizedContact.evaluationSquare P sB X gB hgB)
      (squareMap_evaluation P sB eB heB X fB hfB gB hgB rfl)
      (ParametrizedContact.evaluationSquare P sK X f hf)
      (ParametrizedContact.evaluationSquare P sK X g hg) hqf hqg
      (squareMap_evaluation P sK e he X f hf g hg hcomp)
      (ParametrizedContact.leftSection P sB X fB hfB)
      (ParametrizedContact.leftSection P sB X gB hgB)
      (ParametrizedContact.leftSection P sK X f hf)
      (ParametrizedContact.leftSection P sK X g hg)
      (ParametrizedContact.leftSection_baseChange P sK sB b hb k hk₁ hk₂
        X fB hfB f hf hkf q hq₁ hq₂ hqf)
      (ParametrizedContact.leftSection_baseChange P sK sB b hb k hk₁ hk₂
        X gB hgB g hg hkg q hq₁ hq₂ hqg)
      (leftSection_finiteType P sB eB heB X fB hfB CB gB hgB rfl)
  · exact SectionTransport.reparametrization_baseChange q
      (squareMap P sB eB heB) (squareMap P sK e he) hqa
      (ParametrizedContact.evaluationSquare P sB X fB hfB)
      (ParametrizedContact.evaluationSquare P sB X gB hgB)
      (squareMap_evaluation P sB eB heB X fB hfB gB hgB rfl)
      (ParametrizedContact.evaluationSquare P sK X f hf)
      (ParametrizedContact.evaluationSquare P sK X g hg) hqf hqg
      (squareMap_evaluation P sK e he X f hf g hg hcomp)
      (ParametrizedContact.rightSection P sB X fB hfB)
      (ParametrizedContact.rightSection P sB X gB hgB)
      (ParametrizedContact.rightSection P sK X f hf)
      (ParametrizedContact.rightSection P sK X g hg)
      (ParametrizedContact.rightSection_baseChange P sK sB b hb k hk₁ hk₂
        X fB hfB f hf hkf q hq₁ hq₂ hqf)
      (ParametrizedContact.rightSection_baseChange P sK sB b hb k hk₁ hk₂
        X gB hgB g hg hkg q hq₁ hq₂ hqg)
      (rightSection_finiteType P sB eB heB X fB hfB CB gB hgB rfl)

include hf₀ C₀ htf in
theorem leftSection_field :
    pullSection (squareMap P sK e he) (ParametrizedContact.leftSection P sK X f hf) ≫
        (compositionPullback (squareMap P sK e he)
          (ParametrizedContact.evaluationSquare P sK X f hf)
          (ParametrizedContact.evaluationSquare P sK X g hg)
          (squareMap_evaluation P sK e he X f hf g hg hcomp)
          (movingPairBundleLeft X.variety X.contact)).hom =
      ParametrizedContact.leftSection P sK X g hg :=
  (sections_field P s₀ X f₀ hf₀ C₀ K sK t f hf htf e he g hg hcomp).1

include hf₀ C₀ htf in
theorem rightSection_field :
    pullSection (squareMap P sK e he) (ParametrizedContact.rightSection P sK X f hf) ≫
        (compositionPullback (squareMap P sK e he)
          (ParametrizedContact.evaluationSquare P sK X f hf)
          (ParametrizedContact.evaluationSquare P sK X g hg)
          (squareMap_evaluation P sK e he X f hf g hg hcomp)
          (movingPairBundleRight X.variety X.contact)).hom =
      ParametrizedContact.rightSection P sK X g hg :=
  (sections_field P s₀ X f₀ hf₀ C₀ K sK t f hf htf e he g hg hcomp).2

end FamilyReparametrization

end LeBrunSalamon.Construction.FamilyBivectors

end
