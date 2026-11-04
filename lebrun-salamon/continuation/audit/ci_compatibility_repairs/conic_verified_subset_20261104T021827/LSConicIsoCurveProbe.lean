import LSConicSecondSymbolProbe

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


end SourceReparamProof
end LeBrunSalamon.Refinement
end
