import LSComplexQuadraticCoordinates
import LSPlaneQuadratic

/-! The explicit GL₃ substitution taking xy+c*z² to x²+y²+c*z².
Both matrices and their inverse identities are actual coefficient-ring
calculations.  This supplies the polynomial identity consumed by the
separate projective-action/zero-scheme transport proof. No admission. -/

noncomputable section
set_option autoImplicit false

namespace LeBrunSalamon.ComplexQuadraticMatrix

open ComplexQuadraticCoordinates

variable (A : Type) [CommRing A] [Algebra ℂ A]

def matrix : Matrix (Fin 3) (Fin 3) A :=
  ![![1, imaginary A, 0], ![1, -imaginary A, 0], ![0, 0, 1]]

def inverse : Matrix (Fin 3) (Fin 3) A :=
  ![![half A, half A, 0],
    ![-(imaginary A * half A), imaginary A * half A, 0], ![0, 0, 1]]

theorem matrix_mul_inverse : matrix A * inverse A = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [matrix, inverse, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  all_goals solve
    | ring
    | linear_combination -(half A) * imaginary_sq A + two_mul_half A
    | linear_combination (half A) * imaginary_sq A

theorem inverse_mul_matrix : inverse A * matrix A = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [matrix, inverse, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  all_goals solve
    | ring
    | linear_combination two_mul_half A
    | linear_combination -(2 * half A) * imaginary_sq A + two_mul_half A

/-- The literal change (x,y,z) ↦ (x+i*y,x-i*y,z), as a unit of the
matrix ring rather than an unrecorded choice of projective automorphism. -/
def unit : (Matrix (Fin 3) (Fin 3) A)ˣ where
  val := matrix A
  inv := inverse A
  val_inv := matrix_mul_inverse A
  inv_val := inverse_mul_matrix A

theorem linear_zero : PlaneQuadratic.linearCoordinate A (unit A) 0 =
    MvPolynomial.X 0 + MvPolynomial.C (imaginary A) * MvPolynomial.X 1 := by
  simp [PlaneQuadratic.linearCoordinate, unit, matrix, Fin.sum_univ_succ]

theorem linear_one : PlaneQuadratic.linearCoordinate A (unit A) 1 =
    MvPolynomial.X 0 - MvPolynomial.C (imaginary A) * MvPolynomial.X 1 := by
  simp [PlaneQuadratic.linearCoordinate, unit, matrix, Fin.sum_univ_succ,
    sub_eq_add_neg]

theorem linear_two : PlaneQuadratic.linearCoordinate A (unit A) 2 =
    MvPolynomial.X 2 := by
  simp [PlaneQuadratic.linearCoordinate, unit, matrix, Fin.sum_univ_succ]

/-- Exact normalized polynomial identity.  The coefficient is δ=-c,
without a unit rescaling or a choice of square root. -/
theorem transformed_split (c : A) :
    PlaneQuadratic.transformed A (PlaneQuadratic.split A (-c)) (unit A) =
      PlaneQuadratic.polynomial A (PlaneQuadratic.diagonal A c) := by
  have hi : (MvPolynomial.C (imaginary A) : MvPolynomial (Fin 3) A) ^ 2 = -1 := by
    simpa only [map_pow, map_neg, map_one] using
      congrArg (MvPolynomial.C : A →+* MvPolynomial (Fin 3) A) (imaginary_sq A)
  simp [PlaneQuadratic.transformed, PlaneQuadratic.polynomial,
    PlaneQuadratic.split, PlaneQuadratic.diagonal, MvPolynomial.bind₁_C_right,
    linear_zero, linear_one, linear_two]
  linear_combination -(MvPolynomial.X 1 ^ 2) * hi

def veroneseMatrix : Matrix (Fin 3) (Fin 3) A :=
  ![![half A, 0, half A],
    ![-(imaginary A * half A), 0, imaginary A * half A],
    ![0, imaginary A, 0]]

def veroneseInverse : Matrix (Fin 3) (Fin 3) A :=
  ![![1, imaginary A, 0], ![0, 0, -imaginary A], ![1, -imaginary A, 0]]

theorem veronese_mul_inverse : veroneseMatrix A * veroneseInverse A = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [veroneseMatrix, veroneseInverse, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_apply]
  all_goals solve
    | ring
    | linear_combination two_mul_half A
    | linear_combination -(2 * half A) * imaginary_sq A + two_mul_half A
    | linear_combination -imaginary_sq A

theorem veronese_inverse_mul : veroneseInverse A * veroneseMatrix A = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [veroneseMatrix, veroneseInverse, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_apply]
  all_goals solve
    | ring
    | linear_combination -(half A) * imaginary_sq A + two_mul_half A
    | linear_combination (half A) * imaginary_sq A
    | linear_combination -imaginary_sq A

/-- The literal substitution
(x,y,z)=((u+w)/2,-i*(u-w)/2,i*v). -/
def veroneseUnit : (Matrix (Fin 3) (Fin 3) A)ˣ where
  val := veroneseMatrix A
  inv := veroneseInverse A
  val_inv := veronese_mul_inverse A
  inv_val := veronese_inverse_mul A

def veroneseCoefficients : PlaneQuadratic.Coefficients A := ![0, -1, 0, 0, 1, 0]

/-- The smooth diagonal conic is carried to the exact equation zx-y²
used by the normalized Veronese embedding, with no unit scalar discarded. -/
theorem transformed_veronese :
    PlaneQuadratic.transformed A (PlaneQuadratic.diagonal A 1) (veroneseUnit A) =
      PlaneQuadratic.polynomial A (veroneseCoefficients A) := by
  have hi : (MvPolynomial.C (imaginary A) : MvPolynomial (Fin 3) A) ^ 2 = -1 := by
    simpa only [map_pow, map_neg, map_one] using
      congrArg (MvPolynomial.C : A →+* MvPolynomial (Fin 3) A) (imaginary_sq A)
  have hh : (2 : MvPolynomial (Fin 3) A) * MvPolynomial.C (half A) = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using
      congrArg (MvPolynomial.C : A →+* MvPolynomial (Fin 3) A) (two_mul_half A)
  simp [PlaneQuadratic.transformed, PlaneQuadratic.polynomial,
    PlaneQuadratic.diagonal, veroneseCoefficients, PlaneQuadratic.linearCoordinate,
    veroneseUnit, veroneseMatrix, Fin.sum_univ_succ, MvPolynomial.bind₁_C_right]
  linear_combination
    (MvPolynomial.C (half A) ^ 2 * (MvPolynomial.X 0 - MvPolynomial.X 2) ^ 2 +
      MvPolynomial.X 1 ^ 2) * hi +
    ((2 * MvPolynomial.C (half A) + 1) * MvPolynomial.X 0 * MvPolynomial.X 2) * hh

end LeBrunSalamon.ComplexQuadraticMatrix
end
