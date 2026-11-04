import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin

set_option autoImplicit false
open scoped BigOperators

namespace LeBrunSalamon.Construction.FamilyBivectors.AdditiveExpansion

theorem eq_of_sum {A D : Type*} [AddCommMonoid A] [AddCommMonoid D]
    (L R : A → D) {N : ℕ} (a : Fin N → A) (B : A)
    (hB : B = ∑ i, a i)
    (hL : L (∑ i, a i) = ∑ i, L (a i))
    (hR : R (∑ i, a i) = ∑ i, R (a i))
    (h : ∀ i, L (a i) = R (a i)) : L B = R B := by
  rw [hB, hL, hR]
  exact Finset.sum_congr rfl (fun i _ => h i)

end LeBrunSalamon.Construction.FamilyBivectors.AdditiveExpansion
