import Mathlib

/-! The exact diagonal-ideal calculation for the source tensor. -/
noncomputable section
set_option autoImplicit false
open scoped TensorProduct

namespace LeBrunSalamon.P1SourceAlgebra

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]

theorem tensor_square (z : R) :
    (z ^ 2) ⊗ₜ[K] (1 : R) + (1 : R) ⊗ₜ[K] (z ^ 2) -
      z ⊗ₜ[K] z - z ⊗ₜ[K] z =
        (z ⊗ₜ[K] (1 : R) - (1 : R) ⊗ₜ[K] z) ^ 2 := by
  simp only [pow_two, sub_mul, mul_sub, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, mul_one]
  abel

theorem tensor_square_mem (z : R) :
    (z ^ 2) ⊗ₜ[K] (1 : R) + (1 : R) ⊗ₜ[K] (z ^ 2) -
      z ⊗ₜ[K] z - z ⊗ₜ[K] z ∈ (KaehlerDifferential.ideal K R) ^ 2 := by
  rw [tensor_square, pow_two, pow_two]
  have h : z ⊗ₜ[K] (1 : R) - (1 : R) ⊗ₜ[K] z ∈
      KaehlerDifferential.ideal K R := by
    simpa only [neg_sub] using (KaehlerDifferential.ideal K R).neg_mem
      (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal K z)
  exact Ideal.mul_mem_mul h h

end LeBrunSalamon.P1SourceAlgebra

end
