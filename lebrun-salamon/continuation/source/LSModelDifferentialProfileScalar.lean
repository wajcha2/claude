import LSModelBivector

/-!
# The actual logarithmic source differential in the node frame

Every comparison in this file uses the original cotangent differential,
its canonical pullback maps, and the fixed normalized source bivector.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
set_option stderrAsMessages false
set_option profiler true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.Core.ExternalTensorCoordinates
open LeBrunSalamon.Refinement.Jets LeBrunSalamon.LocalFrames
open LeBrunSalamon.P1Charts LeBrunSalamon.P1TwistFrames
open scoped BigOperators


-- Diagnostic-only, ordered raw-stderr progress marker.
#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "MODEL_DIFFERENTIAL_PROFILE BEGIN_PREFIX"
  err.flush

namespace LeBrunSalamon.Construction.SourceBivectorCoordinates

open Smoothing.CoordinateCharts Smoothing.SourceAffineCharts

theorem quadratic_second (q : Polynomial ℂ) (hq : q.natDegree ≤ 2) :
    q.derivative.derivative = Polynomial.C (2 * q.coeff 2) := by
  have he : q = Polynomial.C (q.coeff 0) + Polynomial.C (q.coeff 1) * Polynomial.X +
      Polynomial.C (q.coeff 2) * Polynomial.X^2 := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, mul_one, pow_one] using
      q.as_sum_range_C_mul_X_pow' (show q.natDegree < 3 by omega)
  conv_lhs => rw [he]
  simp only [Polynomial.derivative_add, Polynomial.derivative_C,
    Polynomial.derivative_C_mul_X, Polynomial.derivative_C_mul_X_sq,
    Polynomial.derivative_zero, zero_add, add_zero]
  congr 1
  ring

/-- The second diagonal symbol constructs an actual global tangent
section whose canonical affine coefficient is one. -/
theorem constant_combination :
    (∑ i, Polynomial.C ((right i).coeff 2) * left i) = 1 := by
  have h : (2 : Polynomial ℂ) *
      (∑ i, Polynomial.C ((right i).coeff 2) * left i) = 2 := by
    calc
      _ = ∑ i, left i * (right i).derivative.derivative := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [quadratic_second (right i) (polynomial_natDegree_le (expansion.right i))]
        simp only [map_mul, map_ofNat]
        ring
      _ = 2 := polynomial_second
  apply mul_left_cancel₀ (show (2 : Polynomial ℂ) ≠ 0 by norm_num)
  simpa only [mul_one] using h

def coordinateSection : AlgebraicSection TangentLine.sheaf :=
  ∑ i, expansion.left i ≫ GlobalScalars.scalarEnd TangentLine.sheaf
    (constants P.structureMap ⊤ ((right i).coeff 2))


-- Diagnostic-only, ordered raw-stderr progress marker.
#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "MODEL_DIFFERENTIAL_PROFILE ENTER_polynomial_scalar"
  err.flush

theorem polynomial_scalar (s : AlgebraicSection TangentLine.sheaf) (c : ℂ) :
    polynomial (s ≫ GlobalScalars.scalarEnd TangentLine.sheaf
      (constants P.structureMap ⊤ c)) = Polynomial.C c * polynomial s := by
  let lc : SectionsOn TangentLine.sheaf U ≃ₗ[RingSections ProjectiveLine U]
      RingSections ProjectiveLine U := frame.coefficient
  change polynomialChartRingEquiv 0 (lc
    ((GlobalScalars.scalarEnd TangentLine.sheaf (constants P.structureMap ⊤ c)).app U
      (Scheme.Modules.Hom.app s U (1 : RingSections ProjectiveLine U)))) = _
  rw [GlobalScalars.scalarEnd_app, constants_restrict, map_smul, smul_eq_mul, map_mul]
  have hc : polynomialChartRingEquiv 0 (constants P.structureMap U c) = Polynomial.C c :=
    polynomialChartRingEquiv_canonical_constant 0 c
  exact congrArg (fun z : Polynomial ℂ => z * polynomial s) hc

-- Diagnostic-only, ordered raw-stderr progress marker.
#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "MODEL_DIFFERENTIAL_PROFILE EXIT_polynomial_scalar"
  err.flush

end LeBrunSalamon.Construction.SourceBivectorCoordinates

end
