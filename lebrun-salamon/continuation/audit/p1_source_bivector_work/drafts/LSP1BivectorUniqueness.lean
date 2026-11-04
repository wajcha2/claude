import LSP1CoordinatePolynomials
import LSP1TensorTaylor

/-! Uniqueness of the source bivector from the actual finite expansion,
the degree bound, and its three diagonal symbols. No source-bivector
existence or uniqueness theorem is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Core LeBrunSalamon.Core.ExternalTensorCoordinates
open LeBrunSalamon.Skeleton LeBrunSalamon.P1Charts LeBrunSalamon.LocalFrames
open LeBrunSalamon.P1TangentTranslation LeBrunSalamon.P1CoordinatePolynomials
open scoped TensorProduct
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety frame

namespace LeBrunSalamon.P1BivectorUniqueness

variable (P : ProjectiveLineOverC)
variable {B : ExternalSquareSections (projectiveLineVariety P)
  (identityCurveContact P).sequence.line}
variable (E : ExternalExpansion (projectiveLineVariety P)
  (identityCurveContact P).sequence.line B)

def left (i : Fin E.size) : Polynomial ℂ := polynomial P (E.left i)
def right (i : Fin E.size) : Polynomial ℂ := polynomial P (E.right i)

theorem polynomial_value
    (ho : VanishesQuadraticallyAlongDiagonal P.structureMap
      (externalSquareLine P.structureMap (identityCurveContact P).sequence.line).sheaf B) :
    ∑ i, left P E i * right P E i = 0 := by
  have h := congrArg (chartAlgebraEquiv P 0)
    (E.diagonalValue_zero_of_orderTwo ho (frame P 0))
  simpa only [ExternalExpansion.diagonalValue, map_sum, map_mul, map_zero,
    left, right, polynomial] using h

theorem polynomial_first
    (ho : VanishesQuadraticallyAlongDiagonal P.structureMap
      (externalSquareLine P.structureMap (identityCurveContact P).sequence.line).sheaf B) :
    ∑ i, left P E i * (right P E i).derivative = 0 := by
  have h := congrArg (chartAlgebraEquiv P 0)
    (E.secondSlotFirst_zero_of_orderTwo ho (frame P 0) (generator (derivativeFrame P 0)))
  simpa only [ExternalExpansion.secondSlotFirst, map_sum, map_mul, map_zero,
    generator_action, left, right, polynomial] using h

theorem polynomial_second
    (hn : ExpansionHasContactHessian (identityCurveContact P) E) :
    ∑ i, left P E i * (right P E i).derivative.derivative = 2 := by
  have h := congrArg (chartAlgebraEquiv P 0)
    (hn (frame P 0) (generator (derivativeFrame P 0)) (generator (derivativeFrame P 0)))
  change chartAlgebraEquiv P 0
      (∑ i, (frame P 0).localCoefficient (E.left i) *
        tangentActs P.structureMap (chartOpen 0) (generator (derivativeFrame P 0))
          (tangentActs P.structureMap (chartOpen 0) (generator (derivativeFrame P 0))
            ((frame P 0).localCoefficient (E.right i)))) =
    chartAlgebraEquiv P 0
      ((2 : RingSections ProjectiveLine (chartOpen 0)) * coordinates (derivativeFrame P 0) (generator (derivativeFrame P 0)) *
        coordinates (derivativeFrame P 0) (generator (derivativeFrame P 0))) at h
  simpa only [map_sum, map_mul, generator_action, coordinates_generator,
    map_one, map_ofNat, mul_one, left, right, polynomial] using h

/-- The image of the actual expansion tensor is the coefficient-one square. -/
theorem tensor_formula
    (ho : VanishesQuadraticallyAlongDiagonal P.structureMap
      (externalSquareLine P.structureMap (identityCurveContact P).sequence.line).sheaf B)
    (hn : ExpansionHasContactHessian (identityCurveContact P) E) :
    polynomialTensor P E.tensor = (P1SourceAlgebra.leftX - P1SourceAlgebra.rightX)^2 := by
  change TensorProduct.map (polynomialLinear P) (polynomialLinear P)
    (∑ i, sectionValue (E.left i) ⊗ₜ[ℂ] sectionValue (E.right i)) = _
  rw [map_sum]
  simp only [TensorProduct.map_tmul, polynomialLinear_sectionValue]
  exact P1SourceAlgebra.tensor_formula (left P E) (right P E)
    (fun i => polynomial_natDegree_le P (E.right i))
    (polynomial_value P E ho) (polynomial_first P E ho) (polynomial_second P E hn)

/-- Two sections with the required order and symbol are equal. Symmetry
is not needed for uniqueness. -/
theorem unique
    (C : ExternalSquareSections (projectiveLineVariety P)
      (identityCurveContact P).sequence.line)
    (hB : VanishesQuadraticallyAlongDiagonal P.structureMap
      (externalSquareLine P.structureMap (identityCurveContact P).sequence.line).sheaf B)
    (nB : HasNormalizedContactSymbol (identityCurveContact P) B)
    (hC : VanishesQuadraticallyAlongDiagonal P.structureMap
      (externalSquareLine P.structureMap (identityCurveContact P).sequence.line).sheaf C)
    (nC : HasNormalizedContactSymbol (identityCurveContact P) C) : B = C := by
  obtain ⟨E, hnE⟩ := nB
  obtain ⟨F, hnF⟩ := nC
  have hEF : E.tensor = F.tensor := by
    apply polynomialTensor_injective P
    rw [tensor_formula P E hB hnE, tensor_formula P F hC hnF]
  apply (sectionValue_bijective _).injective
  rw [← E.tensor_image, ← F.tensor_image, hEF]

end LeBrunSalamon.P1BivectorUniqueness

end
