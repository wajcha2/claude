import Mathlib

/-! Ring calculations for the normalized projective-line source bivector.
No geometric or published input occurs in this file. -/
noncomputable section
set_option autoImplicit false

namespace LeBrunSalamon.P1SourceAlgebra

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]

/-- The separated three-term polynomial is the square of the coordinate
difference, with the coefficient-one normalization. -/
theorem coefficient (z w : R) : z ^ 2 - 2 * z * w + w ^ 2 = (z - w) ^ 2 := by
  ring

theorem coefficient_symmetric (z w : R) : (z - w) ^ 2 = (w - z) ^ 2 := by
  ring

/-- This expression lies in the square of the diagonal ideal as soon as
the two coordinate values have equal diagonal restriction. -/
theorem coefficient_mem_square (I : Ideal R) (z w : R) (h : z - w ∈ I) :
    z ^ 2 - 2 * z * w + w ^ 2 ∈ I ^ 2 := by
  rw [coefficient, pow_two, pow_two]
  exact Ideal.mul_mem_mul h h

/-- The full undivided second symbol, in an arbitrary common gauge c.
The derivative-of-gauge terms cancel by the displayed three-term formula;
the two derivations need not commute. -/
theorem hessian_in_gauge (D E : Derivation K R R) (c z : R) :
    (c * z ^ 2) * D (E c) - (2 * c * z) * D (E (c * z)) +
        c * D (E (c * z ^ 2)) =
      2 * c ^ 2 * D z * E z := by
  simp only [pow_two, Derivation.leibniz, map_add, smul_eq_mul]
  ring

/-- The contact normalization after the actual frame/action comparison. -/
theorem normalized_hessian (D E : Derivation K R R) (c z a b : R)
    (ha : a = c * D z) (hb : b = c * E z) :
    (c * z ^ 2) * D (E c) - (2 * c * z) * D (E (c * z)) +
        c * D (E (c * z ^ 2)) = 2 * a * b := by
  rw [hessian_in_gauge, ha, hb]
  ring


/-- The four-term undivided Hessian of the explicit global expansion. -/
def fourHessian (D E : Derivation K R R) (a0 a1 a2 : R) : R :=
  a2 * D (E a0) + a0 * D (E a2) - a1 * D (E a1) - a1 * D (E a1)

theorem fourHessian_gauge_zero (D E : Derivation K R R) (c z : R) :
    fourHessian D E c (c*z) (c*z^2) = 2*c^2*D z*E z := by
  have h := hessian_in_gauge D E c z
  unfold fourHessian
  linear_combination h

theorem fourHessian_gauge_one (D E : Derivation K R R) (c z : R) :
    fourHessian D E (-(c*z^2)) (-(c*z)) (-c) = 2*c^2*D z*E z := by
  unfold fourHessian
  simp only [map_neg]
  have h := hessian_in_gauge D E c z
  linear_combination h

/-- Literal Taylor expansion of a polynomial of degree at most two.
The coefficient ring of the test point is arbitrary. -/
theorem taylor_two {R : Type*} [CommRing R] [Algebra ℂ R]
    (q : Polynomial ℂ) (hq : q.natDegree ≤ 2) (z w : R) :
    Polynomial.aeval w q = Polynomial.aeval z q +
      Polynomial.aeval z q.derivative * (w - z) +
      (algebraMap ℂ R (1 / 2)) * Polynomial.aeval z q.derivative.derivative * (w - z)^2 := by
  have he : q = Polynomial.C (q.coeff 0) + Polynomial.C (q.coeff 1) * Polynomial.X +
      Polynomial.C (q.coeff 2) * Polynomial.X^2 := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, mul_one, pow_one] using
      q.as_sum_range_C_mul_X_pow' (show q.natDegree < 3 by omega)
  have hd2 : Polynomial.derivative (2 : Polynomial ℂ) = 0 :=
    Polynomial.derivative_C
  conv_lhs => rw [he]
  conv_rhs => rw [he]
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.derivative_X_sq,
    Polynomial.derivative_zero, Polynomial.derivative_one, hd2,
    map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
    zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_one, pow_one,
    Nat.reduceSub, Nat.cast_ofNat, map_ofNat, pow_zero]
  have hhalf : (algebraMap ℂ R (1 / 2)) * 2 = 1 := by
    have h := congrArg (algebraMap ℂ R) (show (1 / 2 : ℂ) * 2 = 1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using h
  linear_combination
    -((algebraMap ℂ R (q.coeff 2)) * (w - z)^2) * hhalf


end LeBrunSalamon.P1SourceAlgebra

end
