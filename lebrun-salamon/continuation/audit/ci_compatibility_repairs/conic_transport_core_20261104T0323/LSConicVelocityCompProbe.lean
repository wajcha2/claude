import LSConicDifferentialHomProbe

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTen
open LeBrunSalamon.PhaseFourteen LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton
open LeBrunSalamon.Refinement LeBrunSalamon.Refinement.Jets
open LeBrunSalamon.Construction LeBrunSalamon.Construction.Lines

-- These are existing type aliases. Expose their projections to rewrite
-- matching, so the actual chart rings and projective-line scheme agree.
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety PointFrame.ChartRing
  identityCurveContact intrinsicTangentBundle

set_option maxHeartbeats 250000
set_option diagnostics true
namespace LeBrunSalamon.Refinement

namespace SourceReparamProof

open ConicJetProof

theorem curveContactVelocity_comp (P : ProjectiveLineOverC) {n : ℕ}
    {X : SmoothProperComplexVariety (2*n+1)} (C : IntrinsicContactStructure X)
    (f g : RationalCurve P X) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap) (hg : g.map = e.hom ≫ f.map) :
    (derivativeIso P e he).hom ≫
      (Scheme.Modules.pullback e.hom).map (curveContactVelocity P C f) ≫
      (compositionPullback e.hom f.map g.map hg.symm C.sequence.line.sheaf).hom =
      curveContactVelocity P C g := by
  rcases g with ⟨gmap, hgC, hgNonconstant⟩
  change gmap = e.hom ≫ f.map at hg
  subst gmap
  simp only [compositionPullback, Iso.trans_hom, Iso.app_hom,
    eqToIso_refl, Iso.refl_hom, Category.comp_id]
  have hn := (Scheme.Modules.pullbackComp e.hom f.map).hom.naturality C.sequence.form
  change (Scheme.Modules.pullback e.hom).map
        ((Scheme.Modules.pullback f.map).map C.sequence.form) ≫
      (Scheme.Modules.pullbackComp e.hom f.map).hom.app C.sequence.line.sheaf =
    (Scheme.Modules.pullbackComp e.hom f.map).hom.app (tangentSheaf X.structureMap) ≫
      (Scheme.Modules.pullback (e.hom ≫ f.map)).map C.sequence.form at hn
  change (derivativeIso P e he).hom ≫
      (Scheme.Modules.pullback e.hom).map (curveContactVelocity P C f) ≫
      (Scheme.Modules.pullbackComp e.hom f.map).hom.app C.sequence.line.sheaf = _
  calc
    _ = (differentialOver (projectiveLineVariety P) (projectiveLineVariety P) e.hom he ≫
        (Scheme.Modules.pullback e.hom).map
          (differentialOver (projectiveLineVariety P) X f.map f.overC) ≫
        (Scheme.Modules.pullbackComp e.hom f.map).hom.app (tangentSheaf X.structureMap)) ≫
          (Scheme.Modules.pullback (e.hom ≫ f.map)).map C.sequence.form := by
      simp only [curveContactVelocity, Functor.map_comp, Category.assoc]
      rw [hn] <;> rfl
    _ = _ := by
      rw [ContactDerivativeIsoProof.differentialOver_comp (projectiveLineVariety P)
        (projectiveLineVariety P) X e.hom f.map he f.overC hgC] <;> rfl


end SourceReparamProof
end LeBrunSalamon.Refinement
end
