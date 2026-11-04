import LSFiniteTypeSpreading
import LSContactLineTests
import LSFamilyDescentReparametrization
import LSFamilyReparametrizationFibres

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

namespace FamilyReparametrization

open Parametrized

variable (P : ProjectiveLineOverC) {B : Scheme} (sB : B ⟶ ComplexBase)

variable (e : Source P sB ≅ Source P sB)
variable (he : e.hom ≫ parameter P sB = parameter P sB)

variable {n : ℕ} (X : ContactFanoManifold n)
variable (f : Source P sB ⟶ X.variety.scheme)
variable (hf : f ≫ X.variety.structureMap = parameter P sB ≫ sB)
variable (C : NonconstantFamily P sB X f)
variable (g : Source P sB ⟶ X.variety.scheme)
variable (hg : g ≫ X.variety.structureMap = parameter P sB ≫ sB)
variable (hcomp : e.hom ≫ f = g)

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
