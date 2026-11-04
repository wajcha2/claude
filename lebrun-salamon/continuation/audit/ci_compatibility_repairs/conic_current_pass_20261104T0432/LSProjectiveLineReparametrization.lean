import RecompileExtensionsPart02

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTen
open LeBrunSalamon.PhaseFourteen LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton
open LeBrunSalamon.Construction LeBrunSalamon.Construction.Lines
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety identityCurveContact intrinsicTangentBundle
namespace LeBrunSalamon.Refinement.SourceReparamProof

theorem inverse_overC (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap) :
    e.inv ≫ P.structureMap = P.structureMap := by
  calc
    _ = e.inv ≫ (e.hom ≫ P.structureMap) := congrArg (fun f => e.inv ≫ f) he.symm
    _ = _ := by rw [← Category.assoc, e.inv_hom_id, Category.id_comp]

def isoCurve (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap) :
    RationalCurve P (projectiveLineVariety P) where
  map := e.hom
  overC := he
  nonconstant := by
    rintro ⟨x, hx, hc⟩
    let p0 := ProjectiveLinePoint.rebase P marking
    let pinf := ProjectiveLinePoint.rebase P infinity
    have hp : p0.map ≫ e.hom = pinf.map ≫ e.hom := by
      rw [hc, ← Category.assoc, p0.overC, Category.id_comp,
        ← Category.assoc, pinf.overC, Category.id_comp]
    have hp' : p0.map = pinf.map := (cancel_mono e.hom).mp hp
    exact zero_ne_infinity ((ProjectiveLinePoint.rebase_map_eq_iff P marking infinity).1 hp')

/-- Construct the inverse differential at an abstract variety before
specializing to the concrete projective-line model. -/
def differentialIso {d e : ℕ} (X : SmoothProperComplexVariety d)
    (Y : SmoothProperComplexVariety e) (f : X.scheme ⟶ Y.scheme) [IsIso f]
    (hf : f ≫ Y.structureMap = X.structureMap) :
    tangentSheaf X.structureMap ≅ pullbackModule f (tangentSheaf Y.structureMap) := by
  let d : tangentSheaf X.structureMap ⟶ pullbackModule f (tangentSheaf Y.structureMap) :=
    differentialOver X Y f hf
  letI : IsIso d := ContactDerivativeIsoProof.differentialOver_isIso X Y f hf
  exact asIso d

def derivativeIso (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap) :
    tangentSheaf P.structureMap ≅ pullbackModule e.hom (tangentSheaf P.structureMap) :=
  differentialIso (projectiveLineVariety P) (projectiveLineVariety P) e.hom he

theorem differentialIso_hom {d e : ℕ} (X : SmoothProperComplexVariety d)
    (Y : SmoothProperComplexVariety e) (f : X.scheme ⟶ Y.scheme) [IsIso f]
    (hf : f ≫ Y.structureMap = X.structureMap) :
    (differentialIso X Y f hf).hom = differentialOver X Y f hf := rfl

theorem derivativeIso_hom (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap) :
    (derivativeIso P e he).hom =
      differentialOver (projectiveLineVariety P) (projectiveLineVariety P) e.hom he :=
  differentialIso_hom (projectiveLineVariety P) (projectiveLineVariety P) e.hom he



theorem velocity_cancel_form (P : ProjectiveLineOverC) {n : ℕ}
    {X : SmoothProperComplexVariety (2*n+1)} (C : IntrinsicContactStructure X)
    (f : RationalCurve P X) [IsIso C.sequence.form] :
    curveContactVelocity P C f ≫
        (Scheme.Modules.pullback f.map).map (inv C.sequence.form) =
      differentialOver (projectiveLineVariety P) X f.map f.overC := by
  unfold curveContactVelocity
  rw [Category.assoc, ← (Scheme.Modules.pullback f.map).map_comp,
    IsIso.hom_inv_id, (Scheme.Modules.pullback f.map).map_id, Category.comp_id]

theorem identity_form_isIso (P : ProjectiveLineOverC) :
    IsIso (identityCurveContact P).sequence.form := by
  change IsIso (𝟙 (tangentSheaf P.structureMap))
  infer_instance

universe u v

theorem functor_identity_form_inv_comp {D : Type u} [Category.{v} D]
    (F : OModule ProjectiveLine ⥤ D) (P : ProjectiveLineOverC)
    [IsIso (identityCurveContact P).sequence.form]
    {A : D} (d : A ⟶ F.obj (identityCurveContact P).sequence.line.sheaf) :
    d ≫ F.map (inv (identityCurveContact P).sequence.form) = d := by
  have hi : inv (𝟙 (tangentSheaf P.structureMap)) =
      𝟙 (tangentSheaf P.structureMap) := by
    simpa only [Category.comp_id] using
      (IsIso.inv_hom_id (𝟙 (tangentSheaf P.structureMap)))
  change d ≫ F.map (inv (𝟙 (tangentSheaf P.structureMap))) = d
  rw [hi, F.map_id, Category.comp_id]


theorem identity_velocity_by_cancel (P : ProjectiveLineOverC)
    (f : RationalCurve P (projectiveLineVariety P)) :
    @Eq (tangentSheaf P.structureMap ⟶ pullbackModule f.map (tangentSheaf P.structureMap))
      (curveContactVelocity P (identityCurveContact P) f)
      (differentialOver (projectiveLineVariety P) (projectiveLineVariety P) f.map f.overC) := by
  letI : IsIso (identityCurveContact P).sequence.form := identity_form_isIso P
  exact (functor_identity_form_inv_comp (Scheme.Modules.pullback f.map) P
    (curveContactVelocity P (identityCurveContact P) f)).symm.trans
      (velocity_cancel_form P (identityCurveContact P) f)

theorem source_contactVelocity (P : ProjectiveLineOverC)
    (e : ProjectiveLine ≅ ProjectiveLine) (he : e.hom ≫ P.structureMap = P.structureMap) :
    curveContactVelocity P (identityCurveContact P) (isoCurve P e he) =
      (derivativeIso P e he).hom :=
  (identity_velocity_by_cancel P (isoCurve P e he)).trans (derivativeIso_hom P e he).symm

end LeBrunSalamon.Refinement.SourceReparamProof
end
