import LSConicDifferentialHomProbe
import LSConicIsoCurveProbe

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

theorem source_contactVelocity (P : ProjectiveLineOverC)
    (e : ProjectiveLine ≅ ProjectiveLine) (he : e.hom ≫ P.structureMap = P.structureMap) :
    curveContactVelocity P (identityCurveContact P) (isoCurve P e he) =
      (derivativeIso P e he).hom := by
  calc
    _ = differentialOver (projectiveLineVariety P) (projectiveLineVariety P) e.hom he := by
      change differentialOver (projectiveLineVariety P) (projectiveLineVariety P) e.hom he ≫
        (Scheme.Modules.pullback e.hom).map (𝟙 (tangentSheaf P.structureMap)) = _
      rw [(Scheme.Modules.pullback e.hom).map_id, Category.comp_id]
    _ = _ := (derivativeIso_hom P e he).symm

end SourceReparamProof
end LeBrunSalamon.Refinement
end
