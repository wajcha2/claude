import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Kaehler.JacobiZariski

/-!
## Characteristic-zero field differentials

An element of a characteristic-zero field extension with zero universal
Kähler differential is algebraic over the base field. The public theorem
retains its original namespace and statement from the cone-pairing proof.

This assertion was formerly the literature admission FD-01, the singleton
case of Matsumura, Commutative Ring Theory, Theorem 26.5. It is proved here
from mathlib: a transcendental element gives an injective polynomial
evaluation map, formal smoothness makes the Jacobi--Zariski map injective,
and the polynomial derivation detects the nonzero differential of X.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace LeBrunSalamon.Construction.StandardInputs.FieldDifferentials

private theorem formallySmooth_charZero_field
    (k K : Type*) [Field k] [CharZero k] [Field K] [Algebra k K] :
    Algebra.FormallySmooth k K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K
  letI : Algebra.IsAlgebraic
      (IntermediateField.adjoin k (Set.range (Subtype.val : s → K))) K :=
    hs.isAlgebraic_field
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

private theorem formallySmooth_field_of_faithful
    (R K : Type*) [CommRing R] [IsDomain R] [CharZero R]
    [Field K] [Algebra R K] [FaithfulSMul R K] :
    Algebra.FormallySmooth R K := by
  letI : Algebra (FractionRing R) K := FractionRing.liftAlgebra R K
  letI : IsScalarTower R (FractionRing R) K :=
    FractionRing.isScalarTower_liftAlgebra R K
  letI : Algebra.FormallySmooth R (FractionRing R) :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors R)
  letI : Algebra.FormallySmooth (FractionRing R) K :=
    formallySmooth_charZero_field (FractionRing R) K
  exact Algebra.FormallySmooth.comp R (FractionRing R) K

/-- The polynomial variable retains nonzero universal differential after
formally smooth base change to a field. -/
private theorem polynomial_variable_differential_ne_zero
    (k K : Type*) [Field k] [Field K] [Algebra k K]
    [Algebra (Polynomial k) K] [IsScalarTower k (Polynomial k) K]
    [Algebra.FormallySmooth (Polynomial k) K] :
    KaehlerDifferential.D k K
      (algebraMap (Polynomial k) K Polynomial.X) ≠ 0 := by
  intro h
  have ht :
      (1 : K) ⊗ₜ[Polynomial k]
        KaehlerDifferential.D k (Polynomial k) Polynomial.X = 0 := by
    have hmap : KaehlerDifferential.mapBaseChange k (Polynomial k) K
        ((1 : K) ⊗ₜ[Polynomial k]
          KaehlerDifferential.D k (Polynomial k) Polynomial.X) = 0 := by
      simpa only [KaehlerDifferential.mapBaseChange_tmul, one_smul,
        KaehlerDifferential.map_D] using h
    obtain ⟨x, hx⟩ :=
      (Algebra.H1Cotangent.exact_δ_mapBaseChange k (Polynomial k) K _).mp hmap
    rw [Subsingleton.elim x 0, map_zero] at hx
    exact hx.symm
  have heval := congrArg
    ((Polynomial.mkDerivation k (1 : K)).liftKaehlerDifferential.liftBaseChange K) ht
  have h10 : (1 : K) = 0 := by
    simpa only [LinearMap.liftBaseChange_tmul, one_smul,
      Derivation.liftKaehlerDifferential_comp_D, Polynomial.mkDerivation_X,
      map_zero] using heval
  exact one_ne_zero h10

/-- In characteristic zero, a field element with zero universal differential
is algebraic over the base field.
This was formerly admitted as FD-01, the singleton case of Matsumura,
Commutative Ring Theory, Theorem 26.5; the argument below is now a proof. -/
theorem isAlgebraic_of_universalDifferential_zero
    (k K : Type*) [Field k] [CharZero k] [Field K] [Algebra k K]
    (a : K) (ha : KaehlerDifferential.D k K a = 0) : IsAlgebraic k a := by
  by_contra htrans
  letI : Algebra (Polynomial k) K := (Polynomial.aeval a).toRingHom.toAlgebra
  letI : IsScalarTower k (Polynomial k) K :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap k K r = Polynomial.aeval a (Polynomial.C r)
      simp
  letI : FaithfulSMul (Polynomial k) K :=
    (faithfulSMul_iff_algebraMap_injective (Polynomial k) K).2
      (transcendental_iff_injective.mp htrans)
  letI : Algebra.FormallySmooth (Polynomial k) K :=
    formallySmooth_field_of_faithful (Polynomial k) K
  apply polynomial_variable_differential_ne_zero k K
  change KaehlerDifferential.D k K (Polynomial.aeval a Polynomial.X) = 0
  simpa only [Polynomial.aeval_X] using ha

end LeBrunSalamon.Construction.StandardInputs.FieldDifferentials

end
