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

/-- The coefficient identity is first proved over an arbitrary source variety,
so normalization of pullback/fiber maps does not unfold the concrete P1 model. -/
theorem pointDifferential_contact_coefficient_general {d n : ℕ}
    (Y : SmoothProperComplexVariety d) {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) (f : Y.scheme ⟶ X.scheme)
    (hf : f ≫ X.structureMap = Y.structureMap)
    (y : ComplexPoint Y) {x : ComplexPoint X} (hx : y.map ≫ f = x.map)
    {M : LineBundle Y.scheme} (S : PointFrame Y M y)
    (F : PointFrame X C.sequence.line x) (A : ContactAtPoint C F)
    (hV : S.frame.openSet ≤ f ⁻¹ᵁ F.frame.openSet)
    (u : SectionsOn (tangentSheaf Y.structureMap) S.frame.openSet) :
    A.theta (F.fiberEquiv (SourceTangent.pointDifferential Y X f hf y x hx
      (PositiveFrame.localFiberValue y.map (tangentSheaf Y.structureMap)
        S.frame.openSet S.pointSupport u))) =
      S.evaluation (PointFrame.LocalFrameJetProof.coefficientOn F.frame f S.frame.openSet hV
        ((differentialOver Y X f hf ≫
          (Scheme.Modules.pullback f).map C.sequence.form).app S.frame.openSet u)) := by
  let v := PositiveFrame.localFiberValue y.map (tangentSheaf Y.structureMap)
    S.frame.openSet S.pointSupport u
  have hform : fiberMap C.sequence.form x.map
      (SourceTangent.pointDifferential Y X f hf y x hx v) =
      fiberComposition f y.map x.map hx C.sequence.line.sheaf
        (PositiveFrame.localFiberValue y.map (pullbackModule f C.sequence.line.sheaf)
          S.frame.openSet S.pointSupport
          ((differentialOver Y X f hf ≫
            (Scheme.Modules.pullback f).map C.sequence.form).app S.frame.openSet u)) := by
    rw [PositiveFrame.localFiberValue_map]
    change fiberMap C.sequence.form x.map
      (fiberComposition f y.map x.map hx (tangentSheaf X.structureMap)
        (fiberMap (differentialOver Y X f hf) y.map v)) =
      fiberComposition f y.map x.map hx C.sequence.line.sheaf
        (fiberMap (differentialOver Y X f hf ≫
          (Scheme.Modules.pullback f).map C.sequence.form) y.map v)
    rw [ContactPositive.fiberMap_comp]
    exact (ContactPositive.fiberComposition_naturality f y.map x.map hx
      C.sequence.form (fiberMap (differentialOver Y X f hf) y.map v)).symm
  rw [theta_fiber_coefficient C F A]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    (F.lineFiberCoefficient (fiberMap C.sequence.form x.map
      (SourceTangent.pointDifferential Y X f hf y x hx v))) = _
  rw [hform, F.lineFiberCoefficient_composition f y.map hx
    S.frame.openSet hV S.pointSupport]
  exact (S.evaluation_eq_localRingValue _).symm

end SourceReparamProof
end LeBrunSalamon.Refinement
end
