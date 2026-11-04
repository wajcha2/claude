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

end LeBrunSalamon.Construction.TraitContact.ModelGenericComparison

end
