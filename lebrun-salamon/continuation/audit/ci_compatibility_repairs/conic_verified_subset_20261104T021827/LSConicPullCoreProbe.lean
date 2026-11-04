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

/-- Pull the actual external section back along the actual curve square,
then use the specified canonical external-product comparison. -/
def curvePull (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X)
    (L : LineBundle X.scheme) (B : ExternalSquareSections X L) :
    ExternalSquareSections (projectiveLineVariety P) (pullbackBundle f.map L) := by
  let q := curveExternalComparison P f L.sheaf L.sheaf
  letI : IsIso q := curveExternalComparison_isIso P f L.sheaf L.sheaf
  exact pullSection (curveSquareMap P f) B ≫ inv q

theorem curvePull_comparison (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X)
    (L : LineBundle X.scheme) (B : ExternalSquareSections X L) :
    curvePull P f L B ≫ curveExternalComparison P f L.sheaf L.sheaf =
      pullSection (curveSquareMap P f) B := by
  letI := curveExternalComparison_isIso P f L.sheaf L.sheaf
  simp only [curvePull, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem curvePull_product (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X)
    (L : LineBundle X.scheme) (a b : AlgebraicSection L.sheaf) :
    curvePull P f L (externalProductSection X.structureMap a b) =
      externalProductSection P.structureMap (pullSection f.map a) (pullSection f.map b) := by
  letI := curveExternalComparison_isIso P f L.sheaf L.sheaf
  apply (cancel_mono (curveExternalComparison P f L.sheaf L.sheaf)).mp
  rw [curvePull_comparison, curveExternalComparison_onProducts]

theorem curvePull_sum (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X)
    (L : LineBundle X.scheme) {N : ℕ} (B : Fin N → ExternalSquareSections X L) :
    curvePull P f L (∑ i, B i) = ∑ i, curvePull P f L (B i) := by
  simp only [curvePull, pullSection, restrictSection, Functor.map_sum,
    Preadditive.comp_sum, Preadditive.sum_comp]


end SourceReparamProof
end LeBrunSalamon.Refinement
end
