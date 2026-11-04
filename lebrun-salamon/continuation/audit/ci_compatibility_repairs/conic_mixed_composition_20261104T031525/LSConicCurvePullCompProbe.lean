import LSConicPullExpansionProbe
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

theorem curveKernelIdentity_curvePull (P : ProjectiveLineOverC) {n : ℕ}
    {X : SmoothProperComplexVariety (2*n+1)} (C : IntrinsicContactStructure X)
    (f : RationalCurve P X) (B : ExternalSquareSections X C.sequence.line) :
    CurveKernelIdentity P C f B ↔
      curvePull P f C.sequence.line B = sourceBivector P ≫
        externalTensorMap P.structureMap (curveContactVelocity P C f) (curveContactVelocity P C f) := by
  rw [curveKernelIdentity_iff]
  let q := curveExternalComparison P f C.sequence.line.sheaf C.sequence.line.sheaf
  letI : IsIso q := curveExternalComparison_isIso P f C.sequence.line.sheaf C.sequence.line.sheaf
  constructor
  · intro h
    have hh := congrArg (fun a => a ≫ inv q) h
    simpa only [curvePull, sourceContactValue, q, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id] using hh
  · intro h
    rw [← curvePull_comparison P f C.sequence.line B, h]
    rfl

/-- Composition of actual curve pullbacks, proved on a genuine finite
external expansion and the canonical composition pullback on each factor. -/
theorem curvePull_iso_comp (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f g : RationalCurve P X)
    (e : ProjectiveLine ≅ ProjectiveLine) (he : e.hom ≫ P.structureMap = P.structureMap)
    (hg : g.map = e.hom ≫ f.map) (L : LineBundle X.scheme)
    (B : ExternalSquareSections X L) :
    curvePull P (isoCurve P e he) (pullbackBundle f.map L) (curvePull P f L B) ≫
      externalTensorMap P.structureMap
        (compositionPullback e.hom f.map g.map hg.symm L.sheaf).hom
        (compositionPullback e.hom f.map g.map hg.symm L.sheaf).hom =
      curvePull P g L B := by
  obtain ⟨E⟩ := externalExpansion_exists X L B
  rw [(pulledExpansion P (isoCurve P e he) (pulledExpansion P f E)).equation,
    Preadditive.sum_comp, (pulledExpansion P g E).equation]
  apply Finset.sum_congr rfl
  intro i hi
  change externalProductSection P.structureMap
      (pullSection e.hom (pullSection f.map (E.left i)))
      (pullSection e.hom (pullSection f.map (E.right i))) ≫
        externalTensorMap P.structureMap
          (compositionPullback e.hom f.map g.map hg.symm L.sheaf).hom
          (compositionPullback e.hom f.map g.map hg.symm L.sheaf).hom = _
  rw [CurveExchangeProof.externalTensorMap_product P.structureMap
    (pullbackBundle e.hom (pullbackBundle f.map L)) (pullbackBundle g.map L)
    (compositionPullback e.hom f.map g.map hg.symm L.sheaf).hom
    (pullSection e.hom (pullSection f.map (E.left i)))
    (pullSection e.hom (pullSection f.map (E.right i))),
    compositionPullback_sections, compositionPullback_sections] <;> rfl


end SourceReparamProof
end LeBrunSalamon.Refinement
end
