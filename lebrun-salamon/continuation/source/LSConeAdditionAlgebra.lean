import LSConeOpen
import LSSuitableLinear
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Actual addition dominance for linear cones and the secant comparison

SOURCE ONLY; UNCOMPILED.  Prepared against Foundation105 on 2026-10-29.
No Lean, Lake, or other compiler has been run for this file.

This file proves algebraic portions of the proposed published-secant route.
In particular, the linear-cone theorem PROVES dominance of the existing
`DirectionCones.additionMorphism`: dominance is not an input to it.

The nonlinear comparison uses the explicit polynomial-vanishing formulation
of affine secant density.  Obtaining that formulation from the published
Legendrian secant theorem still requires the actual projective VMRT and its
cone to be constructed and compared.  No such geometric existence is asserted
here, and none of the original geometry admissions is claimed discharged.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace LeBrunSalamon.Construction.Lines.ConeAdditionAlgebra

open DirectionCones

section PolynomialComparison

variable {I : Type}

/-- Sums of actual coordinate points, with both summands retained. -/
def sumPoints (S T : Set (I → ℂ)) : Set (I → ℂ) :=
  {v | ∃ a ∈ S, ∃ b ∈ T, a + b = v}

/-- Evaluation of the existing tensor-ring comorphism is ordinary
polynomial evaluation at the sum. -/
theorem productEvaluation_addition_apply (S T : Set (I → ℂ))
    (a b : I → ℂ) (ha : a ∈ S) (hb : b ∈ T)
    (p : CoordinatePolynomial I) :
    productEvaluation S T a b ha hb (additionComorphism S T p) =
      MvPolynomial.eval (a + b) p := by
  exact congrArg (fun f : CoordinatePolynomial I →ₐ[ℂ] ℂ => f p)
    (productEvaluation_addition S T a b ha hb)

/-- Kernel elements of the actual comorphism vanish on all actual sums.
This is a concrete comparison, with no supplied scheme-dominance premise. -/
theorem additionComorphism_kernel_le_sumVanishing (S T : Set (I → ℂ)) :
    RingHom.ker (additionComorphism S T).toRingHom ≤
      vanishingIdeal (sumPoints S T) := by
  intro p hp v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := hv
  change additionComorphism S T p = 0 at hp
  rw [← productEvaluation_addition_apply S T a b ha hb p, hp, map_zero]

/-- The exact polynomial consequence needed from a projective secant theorem
implies injectivity of the actual addition comorphism. -/
theorem additionComorphism_injective_of_sumVanishing_eq_bot
    (S T : Set (I → ℂ)) (h : vanishingIdeal (sumPoints S T) = ⊥) :
    Function.Injective (additionComorphism S T) := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  apply le_antisymm _ bot_le
  rw [← h]
  exact additionComorphism_kernel_le_sumVanishing S T

set_option backward.isDefEq.respectTransparency false in
/-- `Spec` converts that injectivity to dominance of the actual existing map.
The conclusion is about all prime points, not just complex-valued points. -/
theorem additionMorphism_denseRange_of_sumVanishing_eq_bot
    (S T : Set (I → ℂ)) (h : vanishingIdeal (sumPoints S T) = ⊥) :
    DenseRange (fun z => additionMorphism S T z) := by
  change DenseRange (PrimeSpectrum.comap
    (R := CoordinatePolynomial I) (S := ProductRing S T)
    (additionComorphism S T).toRingHom)
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
    (R := CoordinatePolynomial I) (S := ProductRing S T)
    (additionComorphism S T).toRingHom).mpr
  rw [(RingHom.injective_iff_ker_eq_bot (additionComorphism S T).toRingHom).mp
    (additionComorphism_injective_of_sumVanishing_eq_bot S T h)]
  exact bot_le

/-- Over the infinite field C, a polynomial vanishing at every coordinate
point is zero.  No Nullstellensatz admission is needed for this direction. -/
theorem vanishingIdeal_univ :
    vanishingIdeal (Set.univ : Set (I → ℂ)) = ⊥ := by
  apply le_antisymm _ bot_le
  intro p hp
  change p = 0
  apply MvPolynomial.funext
  intro v
  simpa only [map_zero] using hp v (Set.mem_univ v)

/-- If every vector is an actual sum, the sum-vanishing ideal is zero. -/
theorem sumVanishing_eq_bot_of_surjective (S T : Set (I → ℂ))
    (h : ∀ v : I → ℂ, ∃ a ∈ S, ∃ b ∈ T, a + b = v) :
    vanishingIdeal (sumPoints S T) = ⊥ := by
  have hs : sumPoints S T = Set.univ := by
    apply Set.eq_univ_of_forall
    exact h
  rw [hs, vanishingIdeal_univ]

end PolynomialComparison

section LinearCones

variable {I : Type}

/-- Complementarity supplies actual summands for every coordinate vector. -/
theorem sumPoints_linear_eq_univ (U V : Submodule ℂ (I → ℂ))
    (hUV : U ⊔ V = ⊤) :
    sumPoints (U : Set (I → ℂ)) (V : Set (I → ℂ)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro v
  apply Submodule.mem_sup.mp
  rw [hUV]
  trivial

/-- Dominance in the complementary linear-component branch is ordinary
polynomial algebra, rather than a new geometric admission. -/
theorem linear_additionMorphism_denseRange (U V : Submodule ℂ (I → ℂ))
    (hUV : U ⊔ V = ⊤) :
    DenseRange (fun z =>
      additionMorphism (U : Set (I → ℂ)) (V : Set (I → ℂ)) z) := by
  apply additionMorphism_denseRange_of_sumVanishing_eq_bot
  rw [sumPoints_linear_eq_univ U V hUV, vanishingIdeal_univ]

/-- Disjoint projective linear components give disjoint vector subspaces;
the half-dimensional hypothesis then supplies complementarity. -/
theorem halfDimensional_disjoint_sup_eq_top [Fintype I]
    (U V : Submodule ℂ (I → ℂ)) (n : ℕ)
    (hambient : Module.finrank ℂ (I → ℂ) = 2 * n)
    (hU : Module.finrank ℂ U = n) (hV : Module.finrank ℂ V = n)
    (hdisjoint : Disjoint U V) : U ⊔ V = ⊤ := by
  apply Submodule.eq_top_of_disjoint U V _ hdisjoint
  rw [hambient, hU, hV]
  omega

/-- The actual addition morphism is dominant for two disjoint linear cones
of the required Legendrian dimension. -/
theorem halfDimensional_linear_additionMorphism_denseRange [Fintype I]
    (U V : Submodule ℂ (I → ℂ)) (n : ℕ)
    (hambient : Module.finrank ℂ (I → ℂ) = 2 * n)
    (hU : Module.finrank ℂ U = n) (hV : Module.finrank ℂ V = n)
    (hdisjoint : Disjoint U V) :
    DenseRange (fun z =>
      additionMorphism (U : Set (I → ℂ)) (V : Set (I → ℂ)) z) :=
  linear_additionMorphism_denseRange U V
    (halfDimensional_disjoint_sup_eq_top U V n hambient hU hV hdisjoint)

end LinearCones

section SamePairNonorthogonality

variable {K V W : Type*} [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- For a nonzero vector in an isotropic summand, nondegeneracy finds a
nonorthogonal vector in the OTHER summand of the SAME complementary pair.
There is no change of component after dominance has been established. -/
theorem exists_nonorthogonal_in_complement
    (ω : V →ₗ[K] V →ₗ[K] W)
    (hnd : ∀ a : V, (∀ b : V, ω a b = 0) → a = 0)
    (U Z : Submodule K V) (hUZ : U ⊔ Z = ⊤)
    (hisotropic : ∀ a ∈ U, ∀ b ∈ U, ω a b = 0)
    (a : V) (ha : a ∈ U) (ha0 : a ≠ 0) :
    ∃ b ∈ Z, ω a b ≠ 0 := by
  classical
  by_contra h
  apply ha0
  apply hnd a
  intro w
  have hw : w ∈ U ⊔ Z := by rw [hUZ]; trivial
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
  have hz0 : ω a z = 0 := by
    by_contra hn
    exact h ⟨z, hz, hn⟩
  rw [map_add, hisotropic a ha u hu, hz0, add_zero]

/-- A positive-dimensional isotropic summand therefore supplies an actual
nonorthogonality witness on that same pair of complementary linear cones. -/
theorem exists_nonorthogonal_complementary_linear
    [FiniteDimensional K V] (ω : V →ₗ[K] V →ₗ[K] W)
    (hnd : ∀ a : V, (∀ b : V, ω a b = 0) → a = 0)
    (U Z : Submodule K V) (hUZ : U ⊔ Z = ⊤)
    (hisotropic : ∀ a ∈ U, ∀ b ∈ U, ω a b = 0)
    (hU : 0 < Module.finrank K U) :
    ∃ a ∈ U, ∃ b ∈ Z, ω a b ≠ 0 := by
  have hne : U ≠ ⊥ := by
    intro h
    exact (ne_of_gt hU) ((Submodule.finrank_eq_zero (S := U)).mpr h)
  obtain ⟨a, ha, ha0⟩ := U.ne_bot_iff.mp hne
  obtain ⟨b, hb, hab⟩ :=
    exists_nonorthogonal_in_complement ω hnd U Z hUZ hisotropic a ha ha0
  exact ⟨a, ha, b, hb, hab⟩

end SamePairNonorthogonality

end LeBrunSalamon.Construction.Lines.ConeAdditionAlgebra

end
