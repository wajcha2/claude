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

abbrev imageFrame (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap)
    (S : AffineLineFrame (identityCurveContact P).sequence.line) :
    AffineLineFrame (identityCurveContact P).sequence.line where
  openSet := e.inv ⁻¹ᵁ S.openSet
  isAffine := S.isAffine.preimage e.inv
  coefficient := by
    let D : SectionsOn (tangentSheaf P.structureMap) (e.inv ⁻¹ᵁ S.openSet)
        ≃ₗ[RingSections ProjectiveLine (e.inv ⁻¹ᵁ S.openSet)]
      SectionsOn (pullbackModule e.inv (tangentSheaf P.structureMap))
        (e.inv ⁻¹ᵁ S.openSet) :=
      (((SheafOfModules.evaluation ProjectiveLine.ringCatSheaf
        (op (e.inv ⁻¹ᵁ S.openSet))).mapIso
          (derivativeIso P e.symm (inverse_overC P e he))).toLinearEquiv)
    exact D.trans
      (PointFrame.LocalFrameJetProof.coefficientOn S e.inv (e.inv ⁻¹ᵁ S.openSet) le_rfl)

theorem imageFrame_support (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap)
    (S : AffineLineFrame (identityCurveContact P).sequence.line) :
    S.openSet ≤ e.hom ⁻¹ᵁ (imageFrame P e he S).openSet := by
  change S.openSet ≤ (e.hom ≫ e.inv) ⁻¹ᵁ S.openSet
  rw [e.hom_inv_id]
  simp


end SourceReparamProof
end LeBrunSalamon.Refinement
end
