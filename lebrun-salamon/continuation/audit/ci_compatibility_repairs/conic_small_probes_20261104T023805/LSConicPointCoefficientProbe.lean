import LSConicNormalizedPointProbe

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

theorem pointDifferential_contact_coefficient (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) (f : RationalCurve P X)
    {x : ComplexPoint X} (hx : p.map ≫ f.map = x.map)
    {M : LineBundle ProjectiveLine}
    (S : PointFrame (projectiveLineVariety P) M ⟨p.map, p.overC⟩)
    (F : PointFrame X C.sequence.line x) (A : ContactAtPoint C F)
    (hV : S.frame.openSet ≤ f.map ⁻¹ᵁ F.frame.openSet)
    (u : SectionsOn (tangentSheaf P.structureMap) S.frame.openSet) :
    A.theta (F.fiberEquiv (SourceTangent.pointDifferential (projectiveLineVariety P) X
      f.map f.overC ⟨p.map, p.overC⟩ x hx
      (PositiveFrame.localFiberValue p.map (tangentSheaf P.structureMap)
        S.frame.openSet S.pointSupport u))) =
      S.evaluation (PointFrame.LocalFrameJetProof.coefficientOn F.frame f.map S.frame.openSet hV
        ((curveContactVelocity P C f).app S.frame.openSet u)) := by
  rw [theta_fiber_coefficient C F A]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (F.lineFiberCoefficient (fiberMap C.sequence.form x.map
        (fiberComposition f.map p.map x.map hx (tangentSheaf X.structureMap)
          (fiberMap (differentialOver (projectiveLineVariety P) X f.map f.overC) p.map
            (PositiveFrame.localFiberValue p.map (tangentSheaf P.structureMap)
              S.frame.openSet S.pointSupport u))))) = _
  rw [← ContactPositive.fiberComposition_naturality,
    ← ContactPositive.fiberMap_comp, ← PositiveFrame.localFiberValue_map]
  rw [F.lineFiberCoefficient_composition f.map p.map hx S.frame.openSet hV S.pointSupport]
  exact (S.evaluation_eq_localRingValue _).symm


end SourceReparamProof
end LeBrunSalamon.Refinement
end
