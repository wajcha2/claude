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

theorem mapped_mixed_of_orderTwo {d : ℕ} {Y : SmoothProperComplexVariety d}
    {L M : LineBundle Y.scheme} {B : ExternalSquareSections Y L}
    (E : ExternalExpansion Y L B) (q : L.sheaf ⟶ M.sheaf)
    (h2 : VanishesQuadraticallyAlongDiagonal Y.structureMap
      (externalSquareLine Y.structureMap L).sheaf B)
    (S : AffineLineFrame L)
    (m : SectionsOn M.sheaf S.openSet ≃ₗ[RingSections Y.scheme S.openSet]
      RingSections Y.scheme S.openSet)
    (u : SectionsOn (tangentSheaf Y.structureMap) S.openSet) :
    (SourceMixedSymbol.mappedExpansion E q).mixedSecond (SourceMixedSymbol.frameOn S m) u u =
      (SourceMixedSymbol.multiplier q S m)^2 * E.mixedSecond S u u := by
  rw [(SourceMixedSymbol.mappedExpansion E q).mixedSecond_eq_neg_of_orderTwo
      (SourceMixedSymbol.mapped_orderTwo q h2),
    SourceMixedSymbol.mapped_secondSlotSecond,
    E.diagonalValue_zero_of_orderTwo h2, E.secondSlotFirst_zero_of_orderTwo h2,
    E.mixedSecond_eq_neg_of_orderTwo h2]
  ring


end SourceReparamProof
end LeBrunSalamon.Refinement
end
