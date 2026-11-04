import LSP1SourceAlgebra

/-! Taylor reconstruction in the actual polynomial tensor algebra. -/
noncomputable section
set_option autoImplicit false
open scoped TensorProduct

namespace LeBrunSalamon.P1SourceAlgebra

/-- The three diagonal scalar equations determine every separated
polynomial of right degree at most two over every complex algebra. -/
theorem separated_formula {ι : Type*} [Fintype ι] (p q : ι → Polynomial ℂ)
    (hq : ∀ i, (q i).natDegree ≤ 2)
    (h0 : ∑ i, p i * q i = 0)
    (h1 : ∑ i, p i * (q i).derivative = 0)
    (h2 : ∑ i, p i * (q i).derivative.derivative = 2)
    {R : Type*} [CommRing R] [Algebra ℂ R] (z w : R) :
    ∑ i, Polynomial.aeval z (p i) * Polynomial.aeval w (q i) = (z - w)^2 := by
  have h₀ := congrArg (Polynomial.aeval z) h0
  have h₁ := congrArg (Polynomial.aeval z) h1
  have h₂ := congrArg (Polynomial.aeval z) h2
  simp only [map_sum, map_mul, map_zero, map_ofNat] at h₀ h₁ h₂
  have ht (i : ι) := taylor_two (q i) (hq i) z w
  simp_rw [ht, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hs₁ : (∑ i, Polynomial.aeval z (p i) *
      (Polynomial.aeval z (q i).derivative * (w - z))) =
      (∑ i, Polynomial.aeval z (p i) * Polynomial.aeval z (q i).derivative) *
        (w - z) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hs₂ : (∑ i, Polynomial.aeval z (p i) *
      ((algebraMap ℂ R (1 / 2)) * Polynomial.aeval z (q i).derivative.derivative *
        (w - z)^2)) =
      (algebraMap ℂ R (1 / 2)) *
        (∑ i, Polynomial.aeval z (p i) *
          Polynomial.aeval z (q i).derivative.derivative) * (w - z)^2 := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hs₁, hs₂, h₀, h₁, h₂, zero_mul, zero_add, zero_add]
  have hhalf : (algebraMap ℂ R (1 / 2)) * 2 = 1 := by
    have h := congrArg (algebraMap ℂ R) (show (1 / 2 : ℂ) * 2 = 1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using h
  rw [hhalf, one_mul]
  ring

abbrev PolynomialTensor := Polynomial ℂ ⊗[ℂ] Polynomial ℂ

def leftX : PolynomialTensor := Polynomial.X ⊗ₜ[ℂ] 1

def rightX : PolynomialTensor := 1 ⊗ₜ[ℂ] Polynomial.X

theorem left_aeval (p : Polynomial ℂ) :
    Polynomial.aeval leftX p = p ⊗ₜ[ℂ] (1 : Polynomial ℂ) := by
  have h : Polynomial.aeval leftX =
      (Algebra.TensorProduct.includeLeft : Polynomial ℂ →ₐ[ℂ] PolynomialTensor) := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X]
    rfl
  rw [h]
  rfl

theorem right_aeval (p : Polynomial ℂ) :
    Polynomial.aeval rightX p = (1 : Polynomial ℂ) ⊗ₜ[ℂ] p := by
  have h : Polynomial.aeval rightX =
      (Algebra.TensorProduct.includeRight : Polynomial ℂ →ₐ[ℂ] PolynomialTensor) := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X]
    rfl
  rw [h]
  rfl

/-- Reconstruction inside the tensor product itself, so no polynomial
identity or dense-open principle is substituted for a sheaf comparison. -/
theorem tensor_formula {ι : Type*} [Fintype ι] (p q : ι → Polynomial ℂ)
    (hq : ∀ i, (q i).natDegree ≤ 2)
    (h0 : ∑ i, p i * q i = 0)
    (h1 : ∑ i, p i * (q i).derivative = 0)
    (h2 : ∑ i, p i * (q i).derivative.derivative = 2) :
    ∑ i, p i ⊗ₜ[ℂ] q i = (leftX - rightX)^2 := by
  have h := separated_formula p q hq h0 h1 h2 leftX rightX
  simpa only [left_aeval, right_aeval, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul] using h

end LeBrunSalamon.P1SourceAlgebra

end
