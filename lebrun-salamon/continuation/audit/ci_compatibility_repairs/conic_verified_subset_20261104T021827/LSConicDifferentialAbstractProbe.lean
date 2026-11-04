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

open ConicJetProof

def differentialIso {d e : ℕ} (X : SmoothProperComplexVariety d)
    (Y : SmoothProperComplexVariety e) (f : X.scheme ⟶ Y.scheme) [IsIso f]
    (hf : f ≫ Y.structureMap = X.structureMap) :
    tangentSheaf X.structureMap ≅ pullbackModule f (tangentSheaf Y.structureMap) := by
  let d : tangentSheaf X.structureMap ⟶ pullbackModule f (tangentSheaf Y.structureMap) :=
    differentialOver X Y f hf
  letI : IsIso d := ContactDerivativeIsoProof.differentialOver_isIso X Y f hf
  exact asIso d


end SourceReparamProof
end LeBrunSalamon.Refinement
end
