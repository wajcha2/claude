import RecompileExtensionsPart04Geometry

/-! Restriction of the actual represented family to its given centre and
normalization of the restricted coefficient. This does not identify any
square-zero ideal or assert a smoothness conclusion. -/

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Construction LeBrunSalamon.Construction.Smoothing

namespace LeBrunSalamon.Next3i.CentralCoefficient

/-- The source projection of the actual family change. -/
theorem familyChange_fst {S Y T H : Scheme} (pi : Y ⟶ S)
    (t : T ⟶ S) (h : H ⟶ S) (a : T ⟶ H) (ha : a ≫ h = t) :
    HomDeformationInput.familyChange pi t h a ha ≫ pullback.fst pi h =
      pullback.fst pi t :=
  pullback.lift_fst _ _ _

/-- The parameter projection of the actual family change. -/
theorem familyChange_snd {S Y T H : Scheme} (pi : Y ⟶ S)
    (t : T ⟶ S) (h : H ⟶ S) (a : T ⟶ H) (ha : a ≫ h = t) :
    HomDeformationInput.familyChange pi t h a ha ≫ pullback.snd pi h =
      pullback.snd pi t ≫ a :=
  pullback.lift_snd _ _ _

/-- Base change composes through the literal maps and their base equations. -/
theorem familyChange_comp {S Y T₀ T₁ T₂ : Scheme} (pi : Y ⟶ S)
    (t₀ : T₀ ⟶ S) (t₁ : T₁ ⟶ S) (t₂ : T₂ ⟶ S)
    (i : T₀ ⟶ T₁) (hi : i ≫ t₁ = t₀)
    (j : T₁ ⟶ T₂) (hj : j ≫ t₂ = t₁)
    (hij : (i ≫ j) ≫ t₂ = t₀) :
    HomDeformationInput.familyChange pi t₀ t₁ i hi ≫
        HomDeformationInput.familyChange pi t₁ t₂ j hj =
      HomDeformationInput.familyChange pi t₀ t₂ (i ≫ j) hij := by
  apply pullback.hom_ext
  · simp only [Category.assoc, HomDeformationInput.familyChange,
      pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [Category.assoc, HomDeformationInput.familyChange,
      pullback.lift_snd, pullback.lift_snd_assoc]

/-- Changing a parameter map by equality preserves the actual family map,
including arbitrary witnesses of its base equation. -/
theorem familyChange_congr {S Y T H : Scheme} (pi : Y ⟶ S)
    (t : T ⟶ S) (h : H ⟶ S) (a a' : T ⟶ H)
    (ha : a ≫ h = t) (ha' : a' ≫ h = t) (e : a = a') :
    HomDeformationInput.familyChange pi t h a ha =
      HomDeformationInput.familyChange pi t h a' ha' := by
  cases e
  rfl

/-- A parameter lift reduces to the given central family map. -/
theorem familyChange_centre {S Y T₀ T H : Scheme} (pi : Y ⟶ S)
    (t₀ : T₀ ⟶ S) (t : T ⟶ S) (h : H ⟶ S)
    (i : T₀ ⟶ T) (hi : i ≫ t = t₀)
    (a : T ⟶ H) (ha : a ≫ h = t)
    (a₀ : T₀ ⟶ H) (ha₀ : a₀ ≫ h = t₀) (hia : i ≫ a = a₀) :
    HomDeformationInput.familyChange pi t₀ t i hi ≫
        HomDeformationInput.familyChange pi t h a ha =
      HomDeformationInput.familyChange pi t₀ h a₀ ha₀ := by
  have hcomp : (i ≫ a) ≫ h = t₀ :=
    (Category.assoc i a h).trans ((congrArg (fun u : T ⟶ S => i ≫ u) ha).trans hi)
  exact (familyChange_comp pi t₀ t h i hi a ha hcomp).trans
    (familyChange_congr pi t₀ h (i ≫ a) a₀ hcomp ha₀ hia)

/-- The actual pullback composition isomorphism followed by the actual
map equality, for an arbitrary coefficient module. -/
def pullbackRestrictionIso {A B C : Scheme} (i : A ⟶ B)
    (g : B ⟶ C) (g₀ : A ⟶ C) (hg : i ≫ g = g₀) (E : OModule C) :
    pullbackModule i (pullbackModule g E) ≅ pullbackModule g₀ E :=
  (Scheme.Modules.pullbackComp i g).app E ≪≫
    (Scheme.Modules.pullbackCongr hg).app E

section Presentation

variable {S Y : Scheme} (pi : Y ⟶ S) (sS : S ⟶ ComplexBase)
    {d : ℕ} (X : SmoothProperComplexVariety d)
    (H : HomDeformationInput.Presentation pi sS X)
    (p : ComplexBase ⟶ H.parameter) (b : ComplexBase ⟶ S)
    (hb : p ≫ H.toBase = b)
    {T : Scheme} (t : T ⟶ S) (i : ComplexBase ⟶ T) (hi : i ≫ t = b)
    (a : T ⟶ H.parameter) (ha : a ≫ H.toBase = t) (hia : i ≫ a = p)

include hia

/-- The represented test-family evaluation restricts to exactly the
original fibre evaluation in the hypothesis of OBL056. -/
theorem evaluation_restrict :
    HomDeformationInput.familyChange pi b t i hi ≫
        (HomDeformationInput.familyChange pi t H.toBase a ha ≫ H.evaluation) =
      HomDeformationInput.familyChange pi b H.toBase p hb ≫ H.evaluation := by
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun u : pullback pi b ⟶ pullback pi H.toBase => u ≫ H.evaluation)
      (familyChange_centre pi b t H.toBase i hi a ha p hb hia))

/-- Coefficient normalization uses only pullback composition and the
proved equality of actual evaluation maps. -/
def centralCoefficientIso (E : OModule X.scheme) :
    pullbackModule (HomDeformationInput.familyChange pi b t i hi)
      (pullbackModule (HomDeformationInput.familyChange pi t H.toBase a ha ≫ H.evaluation) E) ≅
    pullbackModule (HomDeformationInput.familyChange pi b H.toBase p hb ≫ H.evaluation) E :=
  pullbackRestrictionIso _ _ _
    (evaluation_restrict pi sS X H p b hb t i hi a ha hia) E

/-- The original extension-splitting H1 predicate is transported through
the actual coefficient isomorphism; no cohomology theory is changed. -/
theorem centralCoefficient_h1_iff (E : OModule X.scheme) :
    HasVanishingFirstCohomology
      (pullbackModule (HomDeformationInput.familyChange pi b t i hi)
        (pullbackModule (HomDeformationInput.familyChange pi t H.toBase a ha ≫ H.evaluation) E)) ↔
    HasVanishingFirstCohomology
      (pullbackModule (HomDeformationInput.familyChange pi b H.toBase p hb ≫ H.evaluation) E) :=
  FirstCohomology.iso_iff
    (centralCoefficientIso pi sS X H p b hb t i hi a ha hia E)

/-- Exact use of the original tangent-coefficient hH1. This says only
that the represented tangent coefficient has vanishing H1 on the centre. -/
theorem centralTangent_h1
    (hH1 : HasVanishingFirstCohomology
      (pullbackModule (HomDeformationInput.familyChange pi b H.toBase p hb ≫ H.evaluation)
        (tangentSheaf X.structureMap))) :
    HasVanishingFirstCohomology
      (pullbackModule (HomDeformationInput.familyChange pi b t i hi)
        (pullbackModule (HomDeformationInput.familyChange pi t H.toBase a ha ≫ H.evaluation)
          (tangentSheaf X.structureMap))) :=
  (centralCoefficient_h1_iff pi sS X H p b hb t i hi a ha hia
    (tangentSheaf X.structureMap)).mpr hH1

end Presentation
end LeBrunSalamon.Next3i.CentralCoefficient

end
