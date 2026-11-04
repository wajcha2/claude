import LSGenericFamilyCartesianComparison
import LSFamilyBaseChange
import LSParametrizedBaseChange
import LSFamilySmoothNormalization
import LSFieldParametrization
import LSFamilyReparametrization
import LSGenericFamilyPointComparison
import LSGenericFamilyFieldTransport

/-!
# Comparison with actual field-valued parametrizations

The normalized descended sections are first compared over every actual
point of the original parametrization cover, over an arbitrary scheme.
Field-valued alternative parametrizations are compared after the actual
residue-field extension of that cover. No complex-point argument is
applied to a fraction-field spectrum.
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

section BundledFieldConstruction

namespace FamilyReparametrization

open Parametrized

variable (P : ProjectiveLineOverC) {B₀ : Scheme}
variable (s₀ : B₀ ⟶ ComplexBase) [LocallyOfFiniteType s₀]
variable {n : ℕ} (X : ContactFanoManifold n)
variable (f₀ : Source P s₀ ⟶ X.variety.scheme)
variable (hf₀ : f₀ ≫ X.variety.structureMap = parameter P s₀ ≫ s₀)
variable (C₀ : NonconstantFamily P s₀ X f₀)
variable (K : CommRingCat) [hK : Fact (IsField K)]
local instance : Field K := hK.out.toField
variable (sK : Spec K ⟶ ComplexBase)
variable (t : PointsOver (Spec K) sK B₀ s₀)
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
private theorem sections_bundled_field :
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
  let tB : PointsOver (Spec K) sK B sB := ⟨b, hb⟩
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


end FamilyReparametrization

end BundledFieldConstruction

private theorem field_equation_transport {T Y Z : Scheme}
    (q q' : T ⟶ Y) (hq : q = q')
    (f f' : Y ⟶ Z) (hf : f = f') (r r' : T ⟶ Z) (hr : r = r')
    (h : q ≫ f = r) (h' : q' ≫ f' = r') (E : OModule Z)
    (s : AlgebraicSection (pullbackModule f E))
    (s' : AlgebraicSection (pullbackModule f' E)) (hs : HEq s s')
    (t : AlgebraicSection (pullbackModule r E))
    (t' : AlgebraicSection (pullbackModule r' E)) (ht : HEq t t') :
    (pullSection q s ≫ (compositionPullback q f r h E).hom = t) ↔
      (pullSection q' s' ≫ (compositionPullback q' f' r' h' E).hom = t') := by
  cases hq
  cases hf
  cases hr
  have hs' : s = s' := eq_of_heq hs
  cases hs'
  have ht' : t = t' := eq_of_heq ht
  cases ht'
  rfl

namespace CartesianParametrization

variable {P : ProjectiveLineOverC} {p : ProjectiveLinePoint P}
variable {n : ℕ} {X : ContactFanoManifold n} {g : VeryFreeContactConic P p X}
variable {N : FullConicNeighborhood P p X g}
variable {F : StableMaps.ProjectiveNodalFamily P p X.variety X.contact.sequence.line 2}
variable (Q : StableMaps.FullHomComparison P p X.variety N.homSpace N.neighborhood
  X.contact.sequence.line 2 F)
-- A field structure is chosen only from the actual bundled ring predicate.
variable (K : CommRingCat) [hK : Fact (IsField K)] (sK : Spec K ⟶ ComplexBase)

local instance : Field K := hK.out.toField
variable (q : PointsOver (Spec K) sK Q.cover Q.coverToC)
variable (b : Spec K ⟶ F.smoothOpen.toScheme) (hq : q.val ≫ Q.toSmooth = b)
variable (k : Parametrized.Source P sK ⟶ F.source)
variable (hk : IsPullback k (Parametrized.parameter P sK) F.parameter (b ≫ F.smoothOpen.ι))
variable (a : Parametrized.Square P sK ⟶ F.smoothSquareOpen.toScheme)
variable (ha : a ≫ F.smoothSquareOpen.ι = RelativeSquare.map (Parametrized.parameter P sK)
  F.parameter k (b ≫ F.smoothOpen.ι) hk.w)


private theorem field_square_eq :
    FamilyReparametrization.squareMap P sK (transition Q sK q b hq k hk)
      (transition_parameter Q sK q b hq k hk) = square Q sK q b hq k hk := by
  rfl

private theorem field_input_map_eq :
    ParametrizedContact.evaluationSquare P sK X (SmoothFamily.atPointEvaluation Q sK q)
      (SmoothFamily.atPointEvaluation_overC Q sK q) =
      SmoothFamily.atPointSquareEvaluation Q sK q := by
  rfl

private theorem field_output_map_eq :
    ParametrizedContact.evaluationSquare P sK X (evaluation (F := F) sK k)
      (evaluation_overC Q sK q b hq k hk) = squareEvaluation Q sK q b hq k hk := by
  rfl

private theorem field_left_input_heq :
    @HEq (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (ParametrizedContact.evaluationSquare P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (movingPairBundleLeft X.variety X.contact)))
      (ParametrizedContact.leftSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q))
      (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (SmoothFamily.atPointSquareEvaluation Q sK q) (movingPairBundleLeft X.variety X.contact)))
      (ParametrizedContact.leftSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) := by rfl

private theorem field_left_output_heq :
    @HEq (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (ParametrizedContact.evaluationSquare P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (movingPairBundleLeft X.variety X.contact)))
      (ParametrizedContact.leftSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk))
      (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (squareEvaluation Q sK q b hq k hk) (movingPairBundleLeft X.variety X.contact)))
      (ParametrizedContact.leftSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) := by rfl

private theorem field_left_invariance_transport
    (hi : pullSection (FamilyReparametrization.squareMap P sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)) (ParametrizedContact.leftSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) ≫
      (compositionPullback (FamilyReparametrization.squareMap P sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)) (ParametrizedContact.evaluationSquare P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (ParametrizedContact.evaluationSquare P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (FamilyReparametrization.squareMap_evaluation P sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk) X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q) (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk) (transition_evaluation Q sK q b hq k hk)) (movingPairBundleLeft X.variety X.contact)).hom = (ParametrizedContact.leftSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk))) :
    pullSection (square Q sK q b hq k hk) (ParametrizedContact.leftSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) ≫
      (compositionPullback (square Q sK q b hq k hk) (SmoothFamily.atPointSquareEvaluation Q sK q) (squareEvaluation Q sK q b hq k hk) (square_evaluation Q sK q b hq k hk) (movingPairBundleLeft X.variety X.contact)).hom = (ParametrizedContact.leftSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) := by
  exact (field_equation_transport (FamilyReparametrization.squareMap P sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)) (square Q sK q b hq k hk) (field_square_eq Q K sK q b hq k hk)
    (ParametrizedContact.evaluationSquare P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (SmoothFamily.atPointSquareEvaluation Q sK q) (field_input_map_eq Q K sK q)
    (ParametrizedContact.evaluationSquare P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (squareEvaluation Q sK q b hq k hk) (field_output_map_eq Q K sK q b hq k hk)
    (FamilyReparametrization.squareMap_evaluation P sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk) X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q) (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk) (transition_evaluation Q sK q b hq k hk)) (square_evaluation Q sK q b hq k hk) (movingPairBundleLeft X.variety X.contact)
    (ParametrizedContact.leftSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (ParametrizedContact.leftSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (field_left_input_heq Q K sK q)
    (ParametrizedContact.leftSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (ParametrizedContact.leftSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (field_left_output_heq Q K sK q b hq k hk)).mp hi

private theorem field_right_input_heq :
    @HEq (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (ParametrizedContact.evaluationSquare P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (movingPairBundleRight X.variety X.contact)))
      (ParametrizedContact.rightSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q))
      (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (SmoothFamily.atPointSquareEvaluation Q sK q) (movingPairBundleRight X.variety X.contact)))
      (ParametrizedContact.rightSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) := by rfl

private theorem field_right_output_heq :
    @HEq (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (ParametrizedContact.evaluationSquare P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (movingPairBundleRight X.variety X.contact)))
      (ParametrizedContact.rightSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk))
      (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (squareEvaluation Q sK q b hq k hk) (movingPairBundleRight X.variety X.contact)))
      (ParametrizedContact.rightSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) := by rfl

private theorem field_right_invariance_transport
    (hi : pullSection (FamilyReparametrization.squareMap P sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)) (ParametrizedContact.rightSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) ≫
      (compositionPullback (FamilyReparametrization.squareMap P sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)) (ParametrizedContact.evaluationSquare P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (ParametrizedContact.evaluationSquare P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (FamilyReparametrization.squareMap_evaluation P sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk) X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q) (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk) (transition_evaluation Q sK q b hq k hk)) (movingPairBundleRight X.variety X.contact)).hom = (ParametrizedContact.rightSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk))) :
    pullSection (square Q sK q b hq k hk) (ParametrizedContact.rightSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) ≫
      (compositionPullback (square Q sK q b hq k hk) (SmoothFamily.atPointSquareEvaluation Q sK q) (squareEvaluation Q sK q b hq k hk) (square_evaluation Q sK q b hq k hk) (movingPairBundleRight X.variety X.contact)).hom = (ParametrizedContact.rightSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) := by
  exact (field_equation_transport (FamilyReparametrization.squareMap P sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)) (square Q sK q b hq k hk) (field_square_eq Q K sK q b hq k hk)
    (ParametrizedContact.evaluationSquare P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (SmoothFamily.atPointSquareEvaluation Q sK q) (field_input_map_eq Q K sK q)
    (ParametrizedContact.evaluationSquare P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (squareEvaluation Q sK q b hq k hk) (field_output_map_eq Q K sK q b hq k hk)
    (FamilyReparametrization.squareMap_evaluation P sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk) X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q) (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk) (transition_evaluation Q sK q b hq k hk)) (square_evaluation Q sK q b hq k hk) (movingPairBundleRight X.variety X.contact)
    (ParametrizedContact.rightSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (ParametrizedContact.rightSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (field_right_input_heq Q K sK q)
    (ParametrizedContact.rightSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (ParametrizedContact.rightSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (field_right_output_heq Q K sK q b hq k hk)).mp hi

/-- Comparison over an arbitrary field when an actual Q-point has
been supplied. Reparametrization is proved by finite-type spreading of
the actual automorphism, and retains the original family evaluation. -/
theorem smoothLeft_field :
    pullSection a (SmoothFamily.smoothLeft Q) ≫
      (compositionPullback a (SmoothFamily.smoothEvaluation (F := F))
        (squareEvaluation Q sK q b hq k hk) (smooth_evaluation Q sK q b hq k hk a ha)
        (movingPairBundleLeft X.variety X.contact)).hom =
      ParametrizedContact.leftSection P sK X (evaluation (F := F) sK k)
        (evaluation_overC Q sK q b hq k hk) := by
  letI : LocallyOfFiniteType Q.coverToC := SmoothFamily.cover_locallyOfFiniteType Q
  apply smoothLeft_of_invariance Q sK q b hq k hk a ha
  apply field_left_invariance_transport Q K sK q b hq k hk
  exact (FamilyReparametrization.sections_bundled_field P Q.coverToC X
    (SmoothFamily.evaluation Q) (SmoothFamily.evaluation_overC Q)
    (SmoothFamily.nonconstantFamily Q) K sK q
    (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q) rfl
    (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)
    (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)
    (transition_evaluation Q sK q b hq k hk)).1

theorem smoothRight_field :
    pullSection a (SmoothFamily.smoothRight Q) ≫
      (compositionPullback a (SmoothFamily.smoothEvaluation (F := F))
        (squareEvaluation Q sK q b hq k hk) (smooth_evaluation Q sK q b hq k hk a ha)
        (movingPairBundleRight X.variety X.contact)).hom =
      ParametrizedContact.rightSection P sK X (evaluation (F := F) sK k)
        (evaluation_overC Q sK q b hq k hk) := by
  letI : LocallyOfFiniteType Q.coverToC := SmoothFamily.cover_locallyOfFiniteType Q
  apply smoothRight_of_invariance Q sK q b hq k hk a ha
  apply field_right_invariance_transport Q K sK q b hq k hk
  exact (FamilyReparametrization.sections_bundled_field P Q.coverToC X
    (SmoothFamily.evaluation Q) (SmoothFamily.evaluation_overC Q)
    (SmoothFamily.nonconstantFamily Q) K sK q
    (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q) rfl
    (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)
    (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)
    (transition_evaluation Q sK q b hq k hk)).2

end CartesianParametrization

end LeBrunSalamon.Construction.FamilyBivectors

end
