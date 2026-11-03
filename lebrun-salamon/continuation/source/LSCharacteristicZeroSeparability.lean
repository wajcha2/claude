import Mathlib

/-!
Characteristic-zero support for the differential publication boundary.
Only algebraic extensions are quantified here; there is no assertion that
an arbitrary transcendental extension is algebraic or algebraically separable.
-/

noncomputable section
set_option autoImplicit false

namespace LeBrunSalamon.CharacteristicZeroSeparability

theorem algebraic_extension_separable (K L : Type*) [Field K] [Field L]
    [Algebra K L] [CharZero K] [Algebra.IsAlgebraic K L] :
    Algebra.IsSeparable K L := by
  infer_instance

theorem complex_algebraic_extension_separable (L : Type*) [Field L]
    [Algebra ℂ L] [Algebra.IsAlgebraic ℂ L] : Algebra.IsSeparable ℂ L := by
  exact algebraic_extension_separable ℂ L

end LeBrunSalamon.CharacteristicZeroSeparability

#print axioms LeBrunSalamon.CharacteristicZeroSeparability.algebraic_extension_separable
#print axioms LeBrunSalamon.CharacteristicZeroSeparability.complex_algebraic_extension_separable

end
