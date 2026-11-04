import Mathlib

/-!
# The polynomial and unit calculations for the three conic charts

These are algebraic identities only. The chosen chart and line-frame
transports still have to be connected to them in the standard-conic module.
This off-graph draft contains no admission and awaits native checking.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LeBrunSalamon.ConicLogAlgebra

variable (R : Type*) [CommRing R]

abbrev PlaneRing := MvPolynomial (Fin 2) R

/-- The node chart has parameter uv; the outer charts have parameter a. -/
def parameter (k : Fin 3) : PlaneRing R :=
  if k = 0 then MvPolynomial.X 0 * MvPolynomial.X 1 else MvPolynomial.X 0

/-- The actual intended coefficients are (u,-v), (0,-1), and (0,1). -/
def coefficient (k : Fin 3) (i : Fin 2) : PlaneRing R :=
  if k = 0 then
    if i = 0 then MvPolynomial.X 0 else -MvPolynomial.X 1
  else if i = 0 then 0 else if k = 1 then -1 else 1

def derivation (k : Fin 3) : Derivation R (PlaneRing R) (PlaneRing R) :=
  MvPolynomial.mkDerivation R (coefficient R k)

@[simp] theorem derivation_variable (k : Fin 3) (i : Fin 2) :
    derivation R k (MvPolynomial.X i) = coefficient R k i :=
  MvPolynomial.mkDerivation_X _ _ i

@[simp] theorem derivation_constant (k : Fin 3) (r : R) :
    derivation R k (MvPolynomial.C r) = 0 := by
  exact (derivation R k).map_algebraMap r

/-- Each displayed vector is relative to the actual polynomial parameter. -/
theorem derivation_parameter (k : Fin 3) :
    derivation R k (parameter R k) = 0 := by
  fin_cases k <;> simp [parameter, coefficient, Derivation.leibniz, smul_eq_mul] <;> ring

/-- Relative vanishing holds for every polynomial in the base coordinate. -/
theorem derivation_base_polynomial (k : Fin 3) (p : Polynomial R) :
    derivation R k (Polynomial.aeval (parameter R k) p) = 0 := by
  rw [Derivation.map_aeval, derivation_parameter, smul_zero]

section Units

variable {R} {A : Type*} [CommRing A] [Algebra R A]

/-- Differentiating an inverse coordinate retains the exact sign. -/
theorem inverse_eigenvector (D : Derivation R A A) (u : Aˣ) (c : A)
    (h : D (u : A) = c * (u : A)) :
    D (↑u⁻¹ : A) = -c * (↑u⁻¹ : A) := by
  change D u.inv = -c * u.inv
  rw [D.leibniz_of_mul_eq_one u.inv_val, h, smul_eq_mul]
  have hvu : (↑u⁻¹ : A) * (u : A) = 1 := u.inv_val
  calc
    -(↑u⁻¹ : A) ^ 2 * (c * (u : A)) =
        -c * (↑u⁻¹ : A) * ((↑u⁻¹ : A) * (u : A)) := by ring
    _ = -c * (↑u⁻¹ : A) := by rw [hvu, mul_one]

/-- Rescaling by the line-frame transition gives the constant outer
coefficient. This is the source of the signs -1 and +1. -/
theorem rescaled_inverse_eigenvector (D : Derivation R A A) (u : Aˣ) (c : A)
    (h : D (u : A) = c * (u : A)) :
    (u : A) * D (↑u⁻¹ : A) = -c := by
  rw [inverse_eigenvector D u c h]
  have huv : (u : A) * (↑u⁻¹ : A) = 1 := u.val_inv
  calc
    (u : A) * (-c * (↑u⁻¹ : A)) = -c * ((u : A) * (↑u⁻¹ : A)) := by ring
    _ = -c := by rw [huv, mul_one]

theorem left_outer_coefficient (D : Derivation R A A) (u : Aˣ)
    (h : D (u : A) = (u : A)) :
    (u : A) * D (↑u⁻¹ : A) = -1 :=
  rescaled_inverse_eigenvector D u 1 (by simpa using h)

theorem right_outer_coefficient (D : Derivation R A A) (v : Aˣ)
    (h : D (v : A) = -(v : A)) :
    (v : A) * D (↑v⁻¹ : A) = 1 := by
  simpa using rescaled_inverse_eigenvector D v (-1) (by simpa using h)

end Units
end LeBrunSalamon.ConicLogAlgebra
end
