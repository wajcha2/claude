import Mathlib

/-!
The actual map m ↦ 1 tensor m is surjective after a surjective scalar
extension.  In particular this applies to a local ring's residue field.
The final lemmas retain a supplied restriction map and its proved equality
with a tensor base-change map, then lift any specified finite section tuple.

No geometric statement and no theorem is admitted in this file.
Off-graph candidate: native checking is pending.
-/

noncomputable section
set_option autoImplicit false
open scoped TensorProduct

namespace LeBrunSalamon.ResidueTensorLift

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- The actual scalar-extension unit, not a chosen map with the same rank. -/
def unit (S : Type*) [CommRing S] [Algebra R S] (M : Type*)
    [AddCommGroup M] [Module R M] : M →ₗ[R] S ⊗[R] M :=
  TensorProduct.mk R S M (1 : S)

@[simp] theorem unit_apply (m : M) : unit (R := R) S M m = (1 : S) ⊗ₜ[R] m := rfl

theorem unit_surjective (h : Function.Surjective (algebraMap R S)) :
    Function.Surjective (unit (R := R) S M) := by
  intro z
  refine TensorProduct.inductionOn z ?_ ?_
  · intro s m
    obtain ⟨r, rfl⟩ := h s
    refine ⟨r • m, ?_⟩
    change (1 : S) ⊗ₜ[R] (r • m) = (algebraMap R S r) ⊗ₜ[R] m
    simpa only [Algebra.smul_def, mul_one] using
      (TensorProduct.smul_tmul (R := R) r (1 : S) m).symm
  · intro x y hx hy
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    exact ⟨m + n, by rw [map_add, hm, hn]⟩

/-- Specialization to the literal residue field and its quotient map. -/
theorem residue_unit_surjective [IsLocalRing R] :
    Function.Surjective (unit (R := R) (IsLocalRing.ResidueField R) M) := by
  apply unit_surjective
  simpa only [IsLocalRing.ResidueField.algebraMap_eq] using
    (IsLocalRing.residue_surjective (R := R))

/-- The conventional right-sided H0 scalar-extension unit m ↦ m tensor 1. -/
def unitRight (S : Type*) [CommRing S] [Algebra R S] (M : Type*)
    [AddCommGroup M] [Module R M] : M →ₗ[R] M ⊗[R] S :=
  (TensorProduct.mk R M S).flip (1 : S)

@[simp] theorem unitRight_apply (m : M) :
    unitRight (R := R) S M m = m ⊗ₜ[R] (1 : S) := rfl

theorem unitRight_surjective (h : Function.Surjective (algebraMap R S)) :
    Function.Surjective (unitRight (R := R) S M) := by
  intro z
  refine TensorProduct.inductionOn z ?_ ?_
  · intro m s
    obtain ⟨r, rfl⟩ := h s
    refine ⟨r • m, ?_⟩
    change (r • m) ⊗ₜ[R] (1 : S) = m ⊗ₜ[R] (algebraMap R S r)
    simpa only [Algebra.smul_def, mul_one] using
      (TensorProduct.smul_tmul (R := R) r m (1 : S))
  · intro x y hx hy
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    exact ⟨m + n, by rw [map_add, hm, hn]⟩

theorem residue_unitRight_surjective [IsLocalRing R] :
    Function.Surjective (unitRight (R := R) (IsLocalRing.ResidueField R) M) := by
  apply unitRight_surjective
  simpa only [IsLocalRing.ResidueField.algebraMap_eq] using
    (IsLocalRing.residue_surjective (R := R))

/-- Transport tensor base-change surjectivity to the specified original
restriction map.  The required normalization is displayed explicitly. -/
theorem restriction_surjective {N : Type*}
    (h : Function.Surjective (algebraMap R S))
    (beta : S ⊗[R] M → N) (hbeta : Function.Surjective beta)
    (restriction : M → N)
    (hnorm : ∀ m, beta ((1 : S) ⊗ₜ[R] m) = restriction m) :
    Function.Surjective restriction := by
  intro n
  obtain ⟨t, ht⟩ := hbeta n
  obtain ⟨m, hm⟩ := unit_surjective (M := M) h t
  refine ⟨m, ?_⟩
  rw [← hnorm m]
  change beta (unit (R := R) S M m) = n
  rw [hm, ht]

theorem residue_restriction_surjective [IsLocalRing R] {N : Type*}
    (beta : IsLocalRing.ResidueField R ⊗[R] M → N)
    (hbeta : Function.Surjective beta) (restriction : M → N)
    (hnorm : ∀ m, beta ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] m) = restriction m) :
    Function.Surjective restriction := by
  apply restriction_surjective (S := IsLocalRing.ResidueField R) _ beta hbeta restriction hnorm
  simpa only [IsLocalRing.ResidueField.algebraMap_eq] using
    (IsLocalRing.residue_surjective (R := R))

/-- The supplied finite tuple is lifted entry by entry through the actual
restriction, so its length and its chosen entries are preserved. -/
theorem lift_finite_tuple [IsLocalRing R] {N : Type*}
    (beta : IsLocalRing.ResidueField R ⊗[R] M → N)
    (hbeta : Function.Surjective beta) (restriction : M → N)
    (hnorm : ∀ m, beta ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] m) = restriction m)
    (n : ℕ) (a : Fin n → N) :
    ∃ b : Fin n → M, ∀ i, restriction (b i) = a i := by
  classical
  let hs := residue_restriction_surjective beta hbeta restriction hnorm
  choose b hb using fun i : Fin n => hs (a i)
  exact ⟨b, hb⟩

theorem residue_restrictionRight_surjective [IsLocalRing R] {N : Type*}
    (beta : M ⊗[R] IsLocalRing.ResidueField R → N)
    (hbeta : Function.Surjective beta) (restriction : M → N)
    (hnorm : ∀ m, beta (m ⊗ₜ[R] (1 : IsLocalRing.ResidueField R)) = restriction m) :
    Function.Surjective restriction := by
  intro n
  obtain ⟨t, ht⟩ := hbeta n
  obtain ⟨m, hm⟩ := residue_unitRight_surjective (R := R) (M := M) t
  refine ⟨m, ?_⟩
  rw [← hnorm m]
  change beta (unitRight (R := R) (IsLocalRing.ResidueField R) M m) = n
  rw [hm, ht]

/-- The same tuple lifting for the conventional H0(E) tensor k orientation. -/
theorem lift_finite_tuple_right [IsLocalRing R] {N : Type*}
    (beta : M ⊗[R] IsLocalRing.ResidueField R → N)
    (hbeta : Function.Surjective beta) (restriction : M → N)
    (hnorm : ∀ m, beta (m ⊗ₜ[R] (1 : IsLocalRing.ResidueField R)) = restriction m)
    (n : ℕ) (a : Fin n → N) :
    ∃ b : Fin n → M, ∀ i, restriction (b i) = a i := by
  classical
  let hs := residue_restrictionRight_surjective beta hbeta restriction hnorm
  choose b hb using fun i : Fin n => hs (a i)
  exact ⟨b, hb⟩

end LeBrunSalamon.ResidueTensorLift

end
