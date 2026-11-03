import RecompileExtensionsPart02

/-!
# The algebra of an affine dual-number base change

The basis is the original quotient classes of `1` and `X`.  In particular,
the following equivalence does not rescale or otherwise choose epsilon.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.Construction
open scoped TensorProduct

namespace LeBrunSalamon.DualBaseChangeAlgebra

open Infinitesimal

def dualCoefficients : Dual ≃ₗ[ℂ] ℂ × ℂ where
  toFun z := (residue z, linearCoefficient z)
  invFun ab := algebraMap ℂ Dual ab.1 + epsilon * algebraMap ℂ Dual ab.2
  left_inv z := (dual_normalForm_reconstruct z).symm
  right_inv ab := by
    exact Prod.ext (residue_normalForm ab.1 ab.2)
      (linearCoefficient_normalForm ab.1 ab.2)
  map_add' z w := Prod.ext (map_add residue z w) (linearCoefficient_add z w)
  map_smul' c z := Prod.ext (map_smul residue c z) (linearCoefficient_smul c z)

@[simp] theorem dualCoefficients_one : dualCoefficients 1 = (1, 0) := by
  have h : (1 : Dual) = algebraMap ℂ Dual 1 + epsilon * algebraMap ℂ Dual 0 := by simp
  rw [h]
  exact Prod.ext (residue_normalForm 1 0) (linearCoefficient_normalForm 1 0)

@[simp] theorem dualCoefficients_epsilon : dualCoefficients epsilon = (0, 1) := by
  have h : epsilon = algebraMap ℂ Dual 0 + epsilon * algebraMap ℂ Dual 1 := by simp
  rw [h]
  exact Prod.ext (residue_normalForm 0 1) (linearCoefficient_normalForm 0 1)

variable (A : Type*) [CommRing A] [Algebra ℂ A]

def tensorCoefficients : A ⊗[ℂ] Dual ≃ₗ[ℂ] A × A :=
  (TensorProduct.congr (LinearEquiv.refl ℂ A) dualCoefficients).trans
    ((TensorProduct.prodRight ℂ ℂ A ℂ ℂ).trans
      (LinearEquiv.prodCongr (TensorProduct.rid ℂ A) (TensorProduct.rid ℂ A)))

@[simp] theorem tensorCoefficients_normalForm (a b : A) :
    tensorCoefficients A (a ⊗ₜ[ℂ] (1 : Dual) + b ⊗ₜ[ℂ] epsilon) = (a, b) := by
  simp [tensorCoefficients]

/-- The tensor-product algebra has unique coefficients over its arbitrary
base algebra, normalized by the actual quotient epsilon. -/
theorem tensor_normalForm (z : A ⊗[ℂ] Dual) :
    ∃! ab : A × A, z = ab.1 ⊗ₜ[ℂ] (1 : Dual) + ab.2 ⊗ₜ[ℂ] epsilon := by
  refine ⟨tensorCoefficients A z, ?_, ?_⟩
  · apply (tensorCoefficients A).injective
    rw [tensorCoefficients_normalForm]
  · intro ab hab
    rw [hab, tensorCoefficients_normalForm]

end LeBrunSalamon.DualBaseChangeAlgebra

end
