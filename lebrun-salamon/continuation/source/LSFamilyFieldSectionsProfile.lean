import LSFiniteTypeSpreading
import LSContactLineTests
import LSFamilyDescentReparametrization
import LSFamilyReparametrizationFibres
import LSFamilyReparametrizationFieldBaseChange
import LSFamilyReparametrizationLeftFiniteType
import LSFamilyReparametrizationRightFiniteType

/-!
# Reparametrization in families and over arbitrary fields

Complex-point detection is used only on reduced schemes locally of
finite type over C.  A field-valued source automorphism is first spread
while retaining the original parameterized family; the tensor identities
then return along the actual field-valued base map.
-/

noncomputable section
set_option profiler true
set_option stderrAsMessages false
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

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "FAMILY_FIELD_STAGE ENTER_sections_field"
  err.flush


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

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "FAMILY_FIELD_STAGE EXIT_sections_field"
  err.flush


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "FAMILY_FIELD_STAGE ENTER_leftSection_field"
  err.flush


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

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "FAMILY_FIELD_STAGE EXIT_leftSection_field"
  err.flush


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "FAMILY_FIELD_STAGE ENTER_rightSection_field"
  err.flush


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

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "FAMILY_FIELD_STAGE EXIT_rightSection_field"
  err.flush


end FamilyReparametrization

end LeBrunSalamon.Construction.FamilyBivectors

end
