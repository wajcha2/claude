import LSConicImageFrameProbe
import LSConicPullExpansionProbe

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

def sourceTransport (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap) :
    ExternalSquareSections (projectiveLineVariety P) (identityCurveContact P).sequence.line :=
  curvePull P (isoCurve P e he) (identityCurveContact P).sequence.line (sourceBivector P) ≫
    externalTensorMap P.structureMap (derivativeIso P e he).inv (derivativeIso P e he).inv

def sourceTransportExpansion (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap) :
    ExternalExpansion (projectiveLineVariety P) (identityCurveContact P).sequence.line
      (sourceTransport P e he) :=
  SourceMixedSymbol.mappedExpansion (M := (identityCurveContact P).sequence.line)
    (pulledExpansion P (isoCurve P e he) (SourceMixedSymbol.sourceKernel P).expansion)
    (derivativeIso P e he).inv

theorem sourceTransport_symmetric (P : ProjectiveLineOverC)
    (e : ProjectiveLine ≅ ProjectiveLine) (he : e.hom ≫ P.structureMap = P.structureMap) :
    IsSymmetricExternalSection P.structureMap (identityCurveContact P).sequence.line
      (sourceTransport P e he) :=
  CurveExchangeProof.map_symmetric (projectiveLineVariety P)
    (pullbackBundle e.hom (identityCurveContact P).sequence.line)
    (identityCurveContact P).sequence.line (derivativeIso P e he).inv _
    (curvePull_symmetric P (isoCurve P e he) _ _ (SourceMixedSymbol.sourceKernel P).symmetric)

theorem sourceTransport_orderTwo (P : ProjectiveLineOverC)
    (e : ProjectiveLine ≅ ProjectiveLine) (he : e.hom ≫ P.structureMap = P.structureMap) :
    VanishesQuadraticallyAlongDiagonal P.structureMap
      (externalSquareLine P.structureMap (identityCurveContact P).sequence.line).sheaf
      (sourceTransport P e he) := by
  have h2 : VanishesQuadraticallyAlongDiagonal P.structureMap
      (externalSquareLine P.structureMap
        (pullbackBundle e.hom (identityCurveContact P).sequence.line)).sheaf
      (curvePull P (isoCurve P e he) (identityCurveContact P).sequence.line
        (sourceBivector P)) :=
    curvePull_orderTwo P (isoCurve P e he) (identityCurveContact P).sequence.line
      (sourceBivector P) (SourceMixedSymbol.sourceKernel P).symmetric
      (SourceMixedSymbol.sourceKernel P).orderTwo
  exact SourceMixedSymbol.mapped_orderTwo (Y := projectiveLineVariety P)
    (L := pullbackBundle e.hom (identityCurveContact P).sequence.line)
    (M := (identityCurveContact P).sequence.line)
    (B := curvePull P (isoCurve P e he) (identityCurveContact P).sequence.line
      (sourceBivector P)) (derivativeIso P e he).inv h2


end SourceReparamProof
end LeBrunSalamon.Refinement
end
