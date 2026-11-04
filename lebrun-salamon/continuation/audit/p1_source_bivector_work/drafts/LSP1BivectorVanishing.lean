import LSP1BivectorConstruction
import LSP1TensorSquare
import LSExternalFrameCoefficients

/-! Order-two vanishing of the actual four-term source bivector. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Core LeBrunSalamon.Skeleton
open LeBrunSalamon.LocalFrames LeBrunSalamon.P1Charts LeBrunSalamon.P1TwistFrames
open LeBrunSalamon.P1TangentTranslation LeBrunSalamon.P1TangentSections
open LeBrunSalamon.ExternalFrameCoefficients
open scoped TensorProduct
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety

namespace LeBrunSalamon.P1BivectorVanishing

variable (P : ProjectiveLineOverC)

def coordinateFunction (i : Fin 2) :
    OpenProductCoordinates.Coefficients P.structureMap (chartOpen i) := coordinate i

theorem coefficient_zero (k : Fin 3) :
    coefficientLinear P.structureMap (derivativeFrame P 0)
      (sectionValue (polynomialField P k)) = coordinateFunction P 0 ^ k.val := by
  rw [coefficientLinear_sectionValue]
  apply (polynomialChartRingEquiv 0).injective
  rw [map_pow]
  change polynomialChartRingEquiv 0
      (coordinates (derivativeFrame P 0) (Scheme.Modules.Hom.app (polynomialField P k) (chartOpen 0) (1 : RingSections ProjectiveLine (chartOpen 0)))) =
    (polynomialChartRingEquiv 0 ((polynomialChartRingEquiv 0).symm Polynomial.X)) ^ k.val
  rw [RingEquiv.apply_symm_apply, ExternalFrameCoefficients.section_app_one]
  exact polynomialField_zero P k

theorem coefficient_one (k : Fin 3) :
    coefficientLinear P.structureMap (derivativeFrame P 1)
      (sectionValue (polynomialField P k)) = -(coordinateFunction P 1 ^ (2 - k.val)) := by
  rw [coefficientLinear_sectionValue]
  apply (polynomialChartRingEquiv 1).injective
  rw [map_neg, map_pow]
  change polynomialChartRingEquiv 1
      (coordinates (derivativeFrame P 1) (Scheme.Modules.Hom.app (polynomialField P k) (chartOpen 1) (1 : RingSections ProjectiveLine (chartOpen 1)))) =
    -((polynomialChartRingEquiv 1 ((polynomialChartRingEquiv 1).symm Polynomial.X)) ^
      (2 - k.val))
  rw [RingEquiv.apply_symm_apply, ExternalFrameCoefficients.section_app_one]
  exact polynomialField_one P k

theorem coefficient_tensor (i : Fin 2) :
    coefficientTensorMap P.structureMap (derivativeFrame P i) (derivativeFrame P i)
      (P1BivectorConstruction.expansion P).tensor =
      (coordinateFunction P i ^ 2) ⊗ₜ[ℂ] (1 : OpenProductCoordinates.Coefficients P.structureMap (chartOpen i)) +
      (1 : OpenProductCoordinates.Coefficients P.structureMap (chartOpen i)) ⊗ₜ[ℂ] (coordinateFunction P i ^ 2) -
      coordinateFunction P i ⊗ₜ[ℂ] coordinateFunction P i - coordinateFunction P i ⊗ₜ[ℂ] coordinateFunction P i := by
  have htwo : (2 : Fin 3).val = 2 := rfl
  fin_cases i
  · change coefficientTensorMap P.structureMap (derivativeFrame P 0) (derivativeFrame P 0)
      (∑ j : Fin 4, (sectionValue (P1BivectorConstruction.left P j) :
        KunnethDegreeZero.Sections P.structureMap (tangentSheaf P.structureMap)) ⊗ₜ[ℂ]
        (sectionValue (P1BivectorConstruction.right P j) :
        KunnethDegreeZero.Sections P.structureMap (tangentSheaf P.structureMap))) = _
    rw [map_sum]
    simp only [coefficientTensorMap_tmul, Fin.sum_univ_succ,
      Fin.sum_univ_zero, P1BivectorConstruction.left, P1BivectorConstruction.right,
      Fin.cases_zero, Fin.cases_succ, sectionValue_neg, map_neg, coefficient_zero,
      Fin.val_zero, Fin.val_one, htwo, Fin.reduceFinMk, pow_zero, pow_one, add_zero,
      TensorProduct.neg_tmul]
    abel
  · change coefficientTensorMap P.structureMap (derivativeFrame P 1) (derivativeFrame P 1)
      (∑ j : Fin 4, (sectionValue (P1BivectorConstruction.left P j) :
        KunnethDegreeZero.Sections P.structureMap (tangentSheaf P.structureMap)) ⊗ₜ[ℂ]
        (sectionValue (P1BivectorConstruction.right P j) :
        KunnethDegreeZero.Sections P.structureMap (tangentSheaf P.structureMap))) = _
    rw [map_sum]
    simp only [coefficientTensorMap_tmul, Fin.sum_univ_succ,
      Fin.sum_univ_zero, P1BivectorConstruction.left, P1BivectorConstruction.right,
      Fin.cases_zero, Fin.cases_succ, sectionValue_neg, map_neg, coefficient_one,
      Fin.val_zero, Fin.val_one, htwo, Fin.reduceFinMk, Nat.reduceSub,
      pow_zero, pow_one, add_zero, TensorProduct.neg_tmul, TensorProduct.tmul_neg,
      neg_neg]
    abel

theorem order_two :
    VanishesQuadraticallyAlongDiagonal P.structureMap
      (externalSquareLine P.structureMap (identityCurveContact P).sequence.line).sheaf
      (P1BivectorConstruction.bivector P) := by
  apply section_vanishes_of_cover_coefficients_mem P.structureMap chartOpen
    chartOpen_cover chartOpen_affine (derivativeFrame P) (derivativeFrame P)
    (P1BivectorConstruction.bivector P) (P1BivectorConstruction.expansion P).tensor
    (P1BivectorConstruction.expansion P).tensor_image.symm 2
  intro i
  rw [coefficient_tensor]
  exact P1SourceAlgebra.tensor_square_mem (K := ℂ)
    (coordinateFunction P i)

end LeBrunSalamon.P1BivectorVanishing

end
