import LSFiniteTypeSpreading
import LSContactLineTests
import LSFamilyReparamExpansionStages

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
  have hleft : (z.val ≫ RelativeSquare.left (parameter P sB)) ≫ parameter P sB =
      (basePoint P sB z).val := by
    simp only [basePoint, Category.assoc]
  have hright : (z.val ≫ RelativeSquare.right (parameter P sB)) ≫ parameter P sB =
      (basePoint P sB z).val := by
    simpa only [basePoint, Category.assoc] using
      congrArg (fun f => z.val ≫ f)
        (pullback.condition (f := parameter P sB) (g := parameter P sB)).symm
  apply pullback.hom_ext
  · rw [Category.assoc, fibreSquare_left, ← Category.assoc, coordinates_left]
    simpa only [Category.assoc, RelativeSquare.left] using
      (sourcePoint_factor P sB (basePoint P sB z)
        (z.val ≫ RelativeSquare.left (parameter P sB)) hleft)
  · rw [Category.assoc, fibreSquare_right, ← Category.assoc, coordinates_right]
    simpa only [Category.assoc, RelativeSquare.right] using
      (sourcePoint_factor P sB (basePoint P sB z)
        (z.val ≫ RelativeSquare.right (parameter P sB)) hright)

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
    change inclusion P sB t ≫ e.inv ≫ e.hom ≫ projection P sB = 𝟙 ProjectiveLine
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
  · simp only [Category.assoc, squareMap_left, fibreSquare_left_assoc, fibreSquare_left]
    rw [← Category.assoc
      (curveSquareMap P (Reparametrization.curve P (fibreIso P sB e he t)
        (fibreIso_overC P sB e he t)))
      (firstProjection P.structureMap) (inclusion P sB t)]
    erw [curveSquareMap_first P (Reparametrization.curve P (fibreIso P sB e he t)
        (fibreIso_overC P sB e he t))]
    change firstProjection P.structureMap ≫ inclusion P sB t ≫ e.hom =
      (firstProjection P.structureMap ≫ fibreHom P sB e t) ≫ inclusion P sB t
    rw [Category.assoc, fibreHom_inclusion P sB e he t]
  · simp only [Category.assoc, squareMap_right, fibreSquare_right_assoc, fibreSquare_right]
    rw [← Category.assoc
      (curveSquareMap P (Reparametrization.curve P (fibreIso P sB e he t)
        (fibreIso_overC P sB e he t)))
      (secondProjection P.structureMap) (inclusion P sB t)]
    erw [curveSquareMap_second P (Reparametrization.curve P (fibreIso P sB e he t)
        (fibreIso_overC P sB e he t))]
    change secondProjection P.structureMap ≫ inclusion P sB t ≫ e.hom =
      (secondProjection P.structureMap ≫ fibreHom P sB e t) ≫ inclusion P sB t
    rw [Category.assoc, fibreHom_inclusion P sB e he t]

end FamilyReparametrization

end LeBrunSalamon.Construction.FamilyBivectors

end
