import LSConicPullCoreProbe

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

def pulledExpansion (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X)
    {L : LineBundle X.scheme} {B : ExternalSquareSections X L}
    (E : ExternalExpansion X L B) :
    ExternalExpansion (projectiveLineVariety P) (pullbackBundle f.map L) (curvePull P f L B) where
  size := E.size
  left i := pullSection f.map (E.left i)
  right i := pullSection f.map (E.right i)
  equation := by
    conv_lhs => rw [E.equation]
    rw [curvePull_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact curvePull_product P f L (E.left i) (E.right i)

theorem curvePull_symmetric (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X)
    (L : LineBundle X.scheme) (B : ExternalSquareSections X L)
    (hB : IsSymmetricExternalSection X.structureMap L B) :
    IsSymmetricExternalSection P.structureMap (pullbackBundle f.map L) (curvePull P f L B) := by
  obtain ⟨E⟩ := externalExpansion_exists X L B
  let EP := pulledExpansion P f E
  let EQ := pulledExpansion P f (SymmetricDiagonalProof.exchangedSameExpansion E hB)
  let sigma := ExchangeAlgebraProof.swapSectionAddHom
    (chosenExternalExchange P.structureMap (pullbackBundle f.map L)).identification
  change sigma (curvePull P f L B) = curvePull P f L B
  have hs (i : Fin E.size) : sigma
      (externalProductSection P.structureMap (EP.left i) (EP.right i)) =
      externalProductSection P.structureMap (EQ.left i) (EQ.right i) :=
    (chosenExternalExchange P.structureMap (pullbackBundle f.map L)).onProducts _ _
  calc
    sigma (curvePull P f L B) = sigma
        (∑ i, externalProductSection P.structureMap (EP.left i) (EP.right i)) :=
      congrArg sigma EP.equation
    _ = ∑ i, sigma (externalProductSection P.structureMap (EP.left i) (EP.right i)) :=
      map_sum sigma _ _
    _ = ∑ i, externalProductSection P.structureMap (EQ.left i) (EQ.right i) :=
      Finset.sum_congr rfl (fun i _ => hs i)
    _ = curvePull P f L B := EQ.equation.symm

theorem curvePull_orderTwo (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X)
    (L : LineBundle X.scheme) (B : ExternalSquareSections X L)
    (hB : IsSymmetricExternalSection X.structureMap L B)
    (h2 : VanishesQuadraticallyAlongDiagonal X.structureMap
      (externalSquareLine X.structureMap L).sheaf B) :
    VanishesQuadraticallyAlongDiagonal P.structureMap
      (externalSquareLine P.structureMap (pullbackBundle f.map L)).sheaf (curvePull P f L B) := by
  apply SymmetricDiagonalProof.orderTwo_of_orderOne (projectiveLineVariety P)
    (pullbackBundle f.map L) (curvePull P f L B) (curvePull_symmetric P f L B hB)
  apply FullFamilyDiagonalProof.orderOne_of_diagonal_zero
  have hdiag := FullFamilyDiagonalProof.diagonal_zero_of_orderTwo X.structureMap B h2
  have hpull : pullSection (diagonal P.structureMap)
      (pullSection (curveSquareMap P f) B) = 0 := by
    apply (FullFamilyDiagonalProof.pullSection_comp_zero_iff
      (diagonal P.structureMap) (curveSquareMap P f) B).2
    rw [FullFamilyDiagonalProof.curveSquare_diagonal]
    apply (FullFamilyDiagonalProof.pullSection_comp_zero_iff
      f.map (diagonal X.structureMap) B).1
    rw [hdiag, FullFamilyDiagonalProof.pullSection_zero]
  simp only [curvePull, pullSection_naturality, hpull, zero_comp]

theorem curvePull_map (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X)
    (L M : LineBundle X.scheme) (q : L.sheaf ⟶ M.sheaf)
    (B : ExternalSquareSections X L) :
    curvePull P f M (B ≫ externalTensorMap X.structureMap q q) =
      curvePull P f L B ≫ externalTensorMap P.structureMap
        ((Scheme.Modules.pullback f.map).map q) ((Scheme.Modules.pullback f.map).map q) := by
  obtain ⟨E⟩ := externalExpansion_exists X L B
  rw [(pulledExpansion P f (SourceMixedSymbol.mappedExpansion E q)).equation,
    (pulledExpansion P f E).equation, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  change externalProductSection P.structureMap
      (pullSection f.map (E.left i ≫ q)) (pullSection f.map (E.right i ≫ q)) = _
  rw [pullSection_naturality, pullSection_naturality]
  exact (CurveExchangeProof.externalTensorMap_product P.structureMap
    (pullbackBundle f.map L) (pullbackBundle f.map M)
    ((Scheme.Modules.pullback f.map).map q)
    (pullSection f.map (E.left i)) (pullSection f.map (E.right i))).symm

theorem externalTensorMap_comp {Y : Scheme} (s : Y ⟶ ComplexBase)
    {E F G : OModule Y} (q : E ⟶ F) (r : F ⟶ G) :
    externalTensorMap s q q ≫ externalTensorMap s r r =
      externalTensorMap s (q ≫ r) (q ≫ r) := by
  simp only [externalTensorMap, Functor.map_comp, tensorMap_comp]


end SourceReparamProof
end LeBrunSalamon.Refinement
end
