import RecompileExtensionsPart01
import LSP1TangentSections
import LSP1SourceAlgebra

/-! Construction of the actual source bivector from three global vector
fields. The vanishing and symbol proofs are developed separately. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Core LeBrunSalamon.Skeleton
open LeBrunSalamon.P1TangentSections
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety

namespace LeBrunSalamon.P1BivectorConstruction

theorem externalProduct_neg_left {X : Scheme} (s : X ⟶ ComplexBase)
    {E F : X.Modules} (a : AlgebraicSection E) (b : AlgebraicSection F) :
    externalProductSection s (-a) b = -externalProductSection s a b := by
  have h : pullSection (firstProjection s) (-a) =
      -pullSection (firstProjection s) a := by
    simp only [pullSection, restrictSection, Functor.map_neg, Preadditive.comp_neg]
  rw [externalProductSection, h, tensorSection_neg_left]
  rfl

def pair (P : ProjectiveLineOverC) (i j : Fin 3) :
    ExternalSquareSections (projectiveLineVariety P) (identityCurveContact P).sequence.line :=
  externalProductSection P.structureMap (polynomialField P i) (polynomialField P j)

/-- The four-term additive form avoids any unproved scalar convention in
the external product. Its coefficient is z²+w²−zw−zw. -/
def bivector (P : ProjectiveLineOverC) :
    ExternalSquareSections (projectiveLineVariety P) (identityCurveContact P).sequence.line :=
  pair P 2 0 + pair P 0 2 - pair P 1 1 - pair P 1 1

theorem symmetric (P : ProjectiveLineOverC) :
    IsSymmetricExternalSection P.structureMap (identityCurveContact P).sequence.line
      (bivector P) := by
  let S := ExchangeAlgebraProof.swapSectionAddHom
    (chosenExternalExchange P.structureMap (identityCurveContact P).sequence.line).identification
  have hs (i j : Fin 3) : S (pair P i j) = pair P j i :=
    (chosenExternalExchange P.structureMap (identityCurveContact P).sequence.line).onProducts
      (polynomialField P i) (polynomialField P j)
  change S (pair P 2 0 + pair P 0 2 - pair P 1 1 - pair P 1 1) = _
  rw [map_sub, map_sub, map_add, hs, hs, hs]
  dsimp only [bivector]
  abel

def left (P : ProjectiveLineOverC) : Fin 4 →
    AlgebraicSection (tangentSheaf P.structureMap) :=
  Fin.cases (polynomialField P 2)
    (Fin.cases (polynomialField P 0) (fun _ => -polynomialField P 1))

def right (P : ProjectiveLineOverC) : Fin 4 →
    AlgebraicSection (tangentSheaf P.structureMap) :=
  Fin.cases (polynomialField P 0)
    (Fin.cases (polynomialField P 2) (fun _ => polynomialField P 1))

def expansion (P : ProjectiveLineOverC) :
    ExternalExpansion (projectiveLineVariety P) (identityCurveContact P).sequence.line
      (bivector P) where
  size := 4
  left := left P
  right := right P
  equation := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, left, right,
      Fin.cases_zero, Fin.cases_succ, add_zero]
    rw [externalProduct_neg_left]
    change pair P 2 0 + pair P 0 2 - pair P 1 1 - pair P 1 1 =
      pair P 2 0 + (pair P 0 2 + (-pair P 1 1 + -pair P 1 1))
    simp only [sub_eq_add_neg, add_assoc]

end LeBrunSalamon.P1BivectorConstruction

end
