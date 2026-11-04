import Mathlib

/-! The literal length-one kernel of a small extension.
These are ordinary commutative-algebra comparisons, with no geometric
lifting assertion and no new published input. -/

noncomputable section
set_option autoImplicit false

namespace LeBrunSalamon.Next3i.SmallExtensionKernel

universe u v

/-- A length-one module over a local ring is the actual residue field
as a module over that original ring. -/
theorem residueLinearEquiv_of_length_one
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (hlen : Module.length R M = 1) :
    Nonempty (M ≃ₗ[R] IsLocalRing.ResidueField R) := by
  have hs : IsSimpleModule R M := (Module.length_eq_one_iff (R := R) (M := M)).mp hlen
  obtain ⟨J, hJ, ⟨e⟩⟩ :=
    (isSimpleModule_iff_quot_maximal (R := R) (M := M)).mp hs
  have hJ' : J = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hJ
  subst J
  exact ⟨e⟩

/-- The annihilator is exactly the maximal ideal, not just an unspecified
ideal acting by zero. -/
theorem annihilator_eq_maximalIdeal_of_length_one
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (hlen : Module.length R M = 1) :
    Module.annihilator R M = IsLocalRing.maximalIdeal R := by
  letI : IsSimpleModule R M := (Module.length_eq_one_iff (R := R) (M := M)).mp hlen
  exact IsLocalRing.eq_maximalIdeal (IsSimpleModule.annihilator_isMaximal (R := R) (M := M))

theorem maximalIdeal_smul_eq_zero_of_length_one
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (hlen : Module.length R M = 1)
    {r : R} (hr : r ∈ IsLocalRing.maximalIdeal R) (m : M) : r • m = 0 := by
  have hmem : r ∈ Module.annihilator R M := by
    rw [annihilator_eq_maximalIdeal_of_length_one hlen]
    exact hr
  exact (Module.mem_annihilator.mp hmem) m

/-- A map into a nonzero ring has a proper kernel. -/
theorem kernel_ne_top {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Nontrivial S] (φ : R →+* S) :
    RingHom.ker φ ≠ ⊤ := by
  intro h
  have hmem : (1 : R) ∈ RingHom.ker φ := by rw [h]; trivial
  have hz : φ 1 = 0 := hmem
  simpa using hz

/-- The actual kernel is identified with the original local ring's residue
field. No scalar action on the kernel is silently replaced. -/
theorem kernel_residueLinearEquiv
    {R : Type u} [CommRing R] [IsLocalRing R]
    {S : Type v} [CommRing S] (φ : R →+* S)
    (hlen : Module.length R (RingHom.ker φ) = 1) :
    Nonempty ((RingHom.ker φ) ≃ₗ[R] IsLocalRing.ResidueField R) :=
  residueLinearEquiv_of_length_one hlen

/-- Products of any two actual kernel elements vanish. -/
theorem kernel_mul_eq_zero
    {R : Type u} [CommRing R] [IsLocalRing R]
    {S : Type v} [CommRing S] [Nontrivial S] (φ : R →+* S)
    (hlen : Module.length R (RingHom.ker φ) = 1)
    {a b : R} (ha : a ∈ RingHom.ker φ) (hb : b ∈ RingHom.ker φ) : a * b = 0 := by
  have hle : RingHom.ker φ ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (kernel_ne_top φ)
  have h := maximalIdeal_smul_eq_zero_of_length_one hlen (hle ha)
    (⟨b, hb⟩ : RingHom.ker φ)
  exact congrArg Subtype.val h

/-- The precise square-zero ideal equality needed for a first-order
lifting theorem follows from the length-one small-extension hypothesis. -/
theorem kernel_sq_eq_bot
    {R : Type u} [CommRing R] [IsLocalRing R]
    {S : Type v} [CommRing S] [Nontrivial S] (φ : R →+* S)
    (hlen : Module.length R (RingHom.ker φ) = 1) :
    (RingHom.ker φ) ^ 2 = ⊥ := by
  rw [pow_two]
  apply le_antisymm _ bot_le
  apply Ideal.mul_le.mpr
  intro a ha b hb
  exact kernel_mul_eq_zero φ hlen ha hb

end LeBrunSalamon.Next3i.SmallExtensionKernel

#print axioms LeBrunSalamon.Next3i.SmallExtensionKernel.residueLinearEquiv_of_length_one
#print axioms LeBrunSalamon.Next3i.SmallExtensionKernel.annihilator_eq_maximalIdeal_of_length_one
#print axioms LeBrunSalamon.Next3i.SmallExtensionKernel.kernel_residueLinearEquiv
#print axioms LeBrunSalamon.Next3i.SmallExtensionKernel.kernel_sq_eq_bot

end
