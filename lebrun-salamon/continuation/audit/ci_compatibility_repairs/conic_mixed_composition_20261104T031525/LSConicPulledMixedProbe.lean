import LSConicPointCoefficientProbe

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

theorem pulled_mixed_point (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)} {C : IntrinsicContactStructure X}
    (K : NormalizedContactKernel X C) (f : RationalCurve P X)
    {x : ComplexPoint X} (hx : p.map ≫ f.map = x.map)
    {M : LineBundle ProjectiveLine}
    (S : PointFrame (projectiveLineVariety P) M ⟨p.map, p.overC⟩)
    (F : PointFrame X C.sequence.line x) (A : ContactAtPoint C F)
    (hV : S.frame.openSet ≤ f.map ⁻¹ᵁ F.frame.openSet)
    (u : SectionsOn (tangentSheaf P.structureMap) S.frame.openSet) :
    S.evaluation ((pulledExpansion P f K.expansion).mixedSecond
      (SourceMixedSymbol.frameOn (M := pullbackBundle f.map C.sequence.line) S.frame
        (PointFrame.LocalFrameJetProof.coefficientOn F.frame f.map S.frame.openSet hV)) u u) =
      -2 * (S.evaluation
        (PointFrame.LocalFrameJetProof.coefficientOn F.frame f.map S.frame.openSet hV
          ((curveContactVelocity P C f).app S.frame.openSet u))) ^ 2 := by
  let w := SourceTangent.pointDifferential (projectiveLineVariety P) X
    f.map f.overC ⟨p.map, p.overC⟩ x hx
    (PositiveFrame.localFiberValue p.map (tangentSheaf P.structureMap)
      S.frame.openSet S.pointSupport u)
  let m := PointFrame.LocalFrameJetProof.coefficientOn F.frame f.map S.frame.openSet hV
  have hc (a : AlgebraicSection C.sequence.line.sheaf) :
      (SourceMixedSymbol.frameOn (M := pullbackBundle f.map C.sequence.line) S.frame m).localCoefficient
        (pullSection f.map a) =
      f.map.appLE F.frame.openSet S.frame.openSet hV (F.coefficient a) := by
    change m (Scheme.Modules.Hom.app (pullSection f.map a)
      S.frame.openSet (1 : RingSections ProjectiveLine _)) = _
    rw [ScalarSections.section_app_one]
    exact PointFrame.LocalFrameJetProof.coefficientOn_global F.frame f.map S.frame.openSet hV a
  have hD (a : F.ChartRing) : (F.fiberEquiv w).val a =
      S.evaluation (tangentActs P.structureMap S.frame.openSet u
        (f.map.appLE F.frame.openSet S.frame.openSet hV a)) :=
    pointDifferential_frame_function (projectiveLineVariety P) X f.map f.overC
      ⟨p.map, p.overC⟩ x hx S F hV u a
  have hm : (∑ i, (F.fiberEquiv w).val (F.coefficient (K.expansion.left i)) *
      (F.fiberEquiv w).val (F.coefficient (K.expansion.right i))) =
      S.evaluation ((pulledExpansion P f K.expansion).mixedSecond
        (SourceMixedSymbol.frameOn (M := pullbackBundle f.map C.sequence.line) S.frame m) u u) := by
    simp only [ExternalExpansion.mixedSecond, map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro i hi
    change (F.fiberEquiv w).val (F.coefficient (K.expansion.left i)) *
        (F.fiberEquiv w).val (F.coefficient (K.expansion.right i)) =
      S.evaluation (tangentActs P.structureMap S.frame.openSet u
        ((SourceMixedSymbol.frameOn (M := pullbackBundle f.map C.sequence.line)
          S.frame m).localCoefficient (pullSection f.map (K.expansion.left i)))) *
      S.evaluation (tangentActs P.structureMap S.frame.openSet u
        ((SourceMixedSymbol.frameOn (M := pullbackBundle f.map C.sequence.line)
          S.frame m).localCoefficient (pullSection f.map (K.expansion.right i))))
    rw [hD, hD, hc, hc]
  have hz := normalized_point_quadratic K F A w
  rw [hm, pointDifferential_contact_coefficient P p C f hx S F A hV u] at hz
  linear_combination hz


end SourceReparamProof
end LeBrunSalamon.Refinement
end
