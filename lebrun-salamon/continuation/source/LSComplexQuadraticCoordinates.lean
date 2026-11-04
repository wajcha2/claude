import Mathlib

/-! The explicit complex-linear coordinate change after Tanaka's diagonal
ternary quadratic normal form. It is an actual invertible linear map over any
complex algebra, and preserves the smoothing coefficient without taking an
unspecified square root or discarding a unit factor. No admission. -/

noncomputable section
set_option autoImplicit false

namespace LeBrunSalamon.ComplexQuadraticCoordinates

variable (A : Type*) [CommRing A] [Algebra ℂ A]

def imaginary : A := algebraMap ℂ A Complex.I

def half : A := algebraMap ℂ A (1 / 2 : ℂ)

theorem imaginary_sq : imaginary A ^ 2 = -1 := by
  rw [imaginary, ← map_pow, Complex.I_sq, map_neg, map_one]

theorem two_mul_half : (2 : A) * half A = 1 := by
  have h : (2 : ℂ) * (1 / 2 : ℂ) = 1 := by norm_num
  have hm := congrArg (algebraMap ℂ A) h
  simpa only [map_mul, map_ofNat, map_one, half] using hm

/-- (x,y,z) ↦ (x+i*y,x-i*y,z), with its explicit inverse. -/
def split : (Fin 3 → A) ≃ₗ[A] (Fin 3 → A) where
  toFun v := ![v 0 + imaginary A * v 1, v 0 - imaginary A * v 1, v 2]
  invFun v := ![half A * (v 0 + v 1),
    -(imaginary A * half A) * (v 0 - v 1), v 2]
  left_inv v := by
    ext i
    fin_cases i
    · change half A * ((v 0 + imaginary A * v 1) +
        (v 0 - imaginary A * v 1)) = v 0
      calc
        _ = ((2 : A) * half A) * v 0 := by ring
        _ = v 0 := by rw [two_mul_half, one_mul]
    · change -(imaginary A * half A) * ((v 0 + imaginary A * v 1) -
        (v 0 - imaginary A * v 1)) = v 1
      calc
        _ = -(imaginary A ^ 2) * ((2 : A) * half A) * v 1 := by ring
        _ = v 1 := by rw [imaginary_sq, two_mul_half]; ring
    · rfl
  right_inv v := by
    ext i
    fin_cases i
    · change half A * (v 0 + v 1) +
        imaginary A * (-(imaginary A * half A) * (v 0 - v 1)) = v 0
      linear_combination -(half A * (v 0 - v 1)) * imaginary_sq A +
        v 0 * two_mul_half A
    · change half A * (v 0 + v 1) -
        imaginary A * (-(imaginary A * half A) * (v 0 - v 1)) = v 1
      linear_combination (half A * (v 0 - v 1)) * imaginary_sq A +
        v 1 * two_mul_half A
    · rfl
  map_add' v w := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r v := by
    ext i
    fin_cases i <;> simp [smul_eq_mul] <;> ring

@[simp] theorem split_zero (v : Fin 3 → A) :
    split A v 0 = v 0 + imaginary A * v 1 := rfl

@[simp] theorem split_one (v : Fin 3 → A) :
    split A v 1 = v 0 - imaginary A * v 1 := rfl

@[simp] theorem split_two (v : Fin 3 → A) : split A v 2 = v 2 := rfl

theorem split_product (v : Fin 3 → A) :
    split A v 0 * split A v 1 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [split_zero, split_one]
  calc
    _ = v 0 ^ 2 - imaginary A ^ 2 * v 1 ^ 2 := by ring
    _ = v 0 ^ 2 + v 1 ^ 2 := by rw [imaginary_sq]; ring

/-- The displayed normal form becomes u*v=delta*w² with delta=-c.
This is an identity over the entire coefficient ring, including nilpotents. -/
theorem split_equation (c : A) (v : Fin 3 → A) :
    split A v 0 * split A v 1 = (-c) * split A v 2 ^ 2 ↔
      v 0 ^ 2 + v 1 ^ 2 + c * v 2 ^ 2 = 0 := by
  rw [split_product, split_two]
  constructor <;> intro h <;> linear_combination h

end LeBrunSalamon.ComplexQuadraticCoordinates
end
