import LSPlaneQuadratic

/-! Extract the six distinct degree-two coefficients from the literal
homogeneous polynomial. In particular, a primitive quadratic remains
nonzero over every field receiving the base ring. No admission. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LeBrunSalamon.QuadraticPolynomial

def exponent : Fin 6 → (Fin 3 →₀ ℕ) :=
  ![Finsupp.single 0 2, Finsupp.single 1 2, Finsupp.single 2 2,
    Finsupp.single 1 1 + Finsupp.single 2 1,
    Finsupp.single 2 1 + Finsupp.single 0 1,
    Finsupp.single 0 1 + Finsupp.single 1 1]

theorem coefficient (R : Type) [CommRing R] (q : PlaneQuadratic.Coefficients R) (i : Fin 6) :
    (PlaneQuadratic.polynomial R q).coeff (exponent i) = q i := by
  fin_cases i <;>
    simp only [PlaneQuadratic.polynomial, pow_two, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.X, MvPolynomial.C_apply, MvPolynomial.monomial_mul_monomial,
      AddMonoidAlgebra.coeff_add, MvPolynomial.coeff_monomial, zero_add, mul_one] <;>
    norm_num [exponent, Finsupp.ext_iff, Fin.forall_fin_succ]

theorem polynomial_zero (R : Type) [CommRing R] :
    PlaneQuadratic.polynomial R 0 = 0 := by
  simp [PlaneQuadratic.polynomial]

theorem injective (R : Type) [CommRing R] :
    Function.Injective (PlaneQuadratic.polynomial R) := by
  intro q q' h
  funext i
  simpa only [coefficient] using congrArg (fun f : MvPolynomial (Fin 3) R => f.coeff (exponent i)) h

theorem polynomial_ne_zero (R : Type) [CommRing R]
    (q : PlaneQuadratic.Coefficients R) (hq : q ≠ 0) :
    PlaneQuadratic.polynomial R q ≠ 0 := by
  intro h
  apply hq
  apply injective R
  rw [h, polynomial_zero]

theorem mapped_coefficients_ne_zero
    {R K : Type} [CommRing R] [Field K] (φ : R →+* K)
    (q : PlaneQuadratic.Coefficients R) (hq : PlaneQuadratic.Primitive R q) :
    (fun i => φ (q i)) ≠ 0 := by
  obtain ⟨i, hi⟩ := hq
  intro h
  exact (hi.map φ).ne_zero (congrFun h i)

theorem mapped_polynomial_ne_zero
    {R K : Type} [CommRing R] [Field K] (φ : R →+* K)
    (q : PlaneQuadratic.Coefficients R) (hq : PlaneQuadratic.Primitive R q) :
    PlaneQuadratic.polynomial K (fun i => φ (q i)) ≠ 0 :=
  polynomial_ne_zero K _ (mapped_coefficients_ne_zero φ q hq)

end LeBrunSalamon.QuadraticPolynomial
end
