import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Second derivatives detect the quadratic diagonal class

This module proves the algebraic Step 3c detector. It uses the actual definition
of Kähler differentials as `I/I²`, a finite projective splitting of this module,
and an explicit quadratic reconstruction. No regular-diagonal or associated
graded statement is admitted. The factor `2` is retained throughout.

The initial candidate is subject to a pinned-compiler replay before acceptance.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

open scoped TensorProduct BigOperators

namespace LeBrunSalamon.SecondDiagonalAlgebra

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- Differentiate the right factor of the actual tensor product. -/
def rightDerivation (D : Derivation ℂ A A) :
    Derivation ℂ (A ⊗[ℂ] A) (A ⊗[ℂ] A) where
  toLinearMap := TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) D.toLinearMap
  map_one_eq_zero' := by
    simp [Algebra.TensorProduct.one_def, D.map_one_eq_zero]
  leibniz' := by
    intro x y
    change TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) D.toLinearMap (x * y) =
      x * TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) D.toLinearMap y +
      y * TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) D.toLinearMap x
    refine TensorProduct.inductionOn x ?_ ?_
    · intro a b
      refine TensorProduct.inductionOn y ?_ ?_
      · intro c d
        simp [Algebra.TensorProduct.tmul_mul_tmul, Derivation.leibniz,
          smul_eq_mul, TensorProduct.tmul_add, mul_comm c a]
      · intro y z hy hz
        simp only [mul_add, add_mul, map_add, hy, hz]
        abel
    · intro x z hx hz
      simp only [mul_add, add_mul, map_add, hx, hz]
      abel

@[simp] theorem rightDerivation_tmul (D : Derivation ℂ A A) (a b : A) :
    rightDerivation D (a ⊗ₜ[ℂ] b) = a ⊗ₜ[ℂ] D b := rfl

/-- The undivided second derivative; its order agrees with the project API. -/
def second (D E : Derivation ℂ A A) : (A ⊗[ℂ] A) →ₗ[ℂ] A :=
  (D.tensorProductTo.restrictScalars ℂ).comp (rightDerivation E).toLinearMap

@[simp] theorem second_tmul (D E : Derivation ℂ A A) (a b : A) :
    second D E (a ⊗ₜ[ℂ] b) = a * D (E b) := rfl

theorem multiplication_rightDerivation (D : Derivation ℂ A A) (t : A ⊗[ℂ] A) :
    Algebra.TensorProduct.lmul' ℂ (rightDerivation D t) = D.tensorProductTo t := by
  refine TensorProduct.inductionOn t ?_ ?_
  · intro a b
    simp only [rightDerivation_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
      Derivation.tensorProductTo_tmul, smul_eq_mul]
  · intro x y hx hy
    simpa only [map_add, hx, hy]

theorem second_mul_of_mem (D E : Derivation ℂ A A)
    (x y : A ⊗[ℂ] A) (hx : x ∈ KaehlerDifferential.ideal ℂ A)
    (hy : y ∈ KaehlerDifferential.ideal ℂ A) :
    second D E (x * y) =
      D.tensorProductTo x * E.tensorProductTo y +
      D.tensorProductTo y * E.tensorProductTo x := by
  change Algebra.TensorProduct.lmul' ℂ x = 0 at hx
  change Algebra.TensorProduct.lmul' ℂ y = 0 at hy
  change D.tensorProductTo (rightDerivation E (x * y)) = _
  rw [(rightDerivation E).leibniz]
  simp only [smul_eq_mul, map_add, Derivation.tensorProductTo_mul,
    multiplication_rightDerivation, hx, hy, zero_mul, zero_add]
  ring

/-- A finite dual frame of the conormal module, lifted to the actual ideal.
The error of this linear reconstruction is in the square of the ideal. -/
theorem exists_first_order_frame
    [Module.Finite A Ω[A⁄ℂ]] [Module.Projective A Ω[A⁄ℂ]] :
    ∃ (n : ℕ) (D : Fin n → Derivation ℂ A A)
      (e : Fin n → KaehlerDifferential.ideal ℂ A),
      ∀ x : KaehlerDifferential.ideal ℂ A,
        (x : A ⊗[ℂ] A) - ∑ i, (D i).tensorProductTo x • (e i : A ⊗[ℂ] A)
          ∈ (KaehlerDifferential.ideal ℂ A) ^ 2 := by
  classical
  obtain ⟨n, f, g, _, _, hfg⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective A Ω[A⁄ℂ]
  let φ (i : Fin n) : Ω[A⁄ℂ] →ₗ[A] A := (LinearMap.proj i).comp g
  let D (i : Fin n) : Derivation ℂ A A :=
    KaehlerDifferential.linearMapEquivDerivation ℂ A (φ i)
  choose e he using fun i : Fin n =>
    KaehlerDifferential.fromIdeal_surjective ℂ A (f (Pi.single i 1))
  have hdual (w : Ω[A⁄ℂ]) : ∑ i, φ i w • f (Pi.single i 1) = w := by
    calc
      ∑ i, φ i w • f (Pi.single i 1) =
          f (∑ i, g w i • Pi.single i 1) := by simp [φ]
      _ = f (g w) := by
        congr 1
        ext i
        simp [Pi.single_apply]
      _ = w := LinearMap.congr_fun hfg w
  have hcoeff (i : Fin n) (x : KaehlerDifferential.ideal ℂ A) :
      (D i).tensorProductTo x = φ i (KaehlerDifferential.fromIdeal ℂ A x) := by
    have hlift : (D i).liftKaehlerDifferential = φ i :=
      (KaehlerDifferential.linearMapEquivDerivation ℂ A).symm_apply_apply (φ i)
    rw [← Derivation.liftKaehlerDifferential_apply, hlift]
    rfl
  refine ⟨n, D, e, ?_⟩
  intro x
  let q : KaehlerDifferential.ideal ℂ A →ₗ[A] Ω[A⁄ℂ] :=
    (KaehlerDifferential.fromIdeal ℂ A).restrictScalars A
  have heq : q x = q (∑ i, (D i).tensorProductTo x • e i) := by
    simp only [map_sum, map_smul]
    change q x = ∑ i, (D i).tensorProductTo x • KaehlerDifferential.fromIdeal ℂ A (e i)
    simp_rw [he, hcoeff]
    exact (hdual (q x)).symm
  have hmem := (Ideal.toCotangent_eq (KaehlerDifferential.ideal ℂ A)).mp heq
  simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using hmem

/-- The quadratic reconstruction modulo the cube. This is the full missing
translation from the displayed Hessians to membership in the diagonal cube. -/
theorem detect_of_first_order_frame
    (n : ℕ) (D : Fin n → Derivation ℂ A A)
    (e : Fin n → KaehlerDifferential.ideal ℂ A)
    (hframe : ∀ x : KaehlerDifferential.ideal ℂ A,
      (x : A ⊗[ℂ] A) - ∑ i, (D i).tensorProductTo x • (e i : A ⊗[ℂ] A)
        ∈ (KaehlerDifferential.ideal ℂ A) ^ 2)
    (t : A ⊗[ℂ] A) (ht : t ∈ (KaehlerDifferential.ideal ℂ A) ^ 2)
    (h : ∀ i j, second (D i) (D j) t = 0) :
    t ∈ (KaehlerDifferential.ideal ℂ A) ^ 3 := by
  classical
  let B := A ⊗[ℂ] A
  let I : Ideal B := KaehlerDifferential.ideal ℂ A
  let Q := B ⧸ I ^ 3
  let q : B →+* Q := Ideal.Quotient.mk (I ^ 3)
  let a : A →+* Q := q.comp (algebraMap A B)
  let v (i : Fin n) : Q := q (e i : B)
  let s (x : I) : B := ∑ i, (D i).tensorProductTo x • (e i : B)
  have hs (x : I) : s x ∈ I := by
    apply Submodule.sum_mem
    intro i _
    exact ((I.restrictScalars A).smul_mem ((D i).tensorProductTo x) (e i).property)
  have hprod (x y : I) :
      q ((x : B) * (y : B)) =
        ∑ i, ∑ j, a ((D i).tensorProductTo x * (D j).tensorProductTo y) * v i * v j := by
    have hdiff : (x : B) * (y : B) - s x * s y ∈ I ^ 3 := by
      have hx : ((x : B) - s x) * (y : B) ∈ I ^ 3 := by
        simpa only [pow_succ] using Ideal.mul_mem_mul (hframe x) y.property
      have hy : s x * ((y : B) - s y) ∈ I ^ 3 := by
        simpa only [pow_succ, mul_comm] using Ideal.mul_mem_mul (hframe y) (hs x)
      convert (I ^ 3).add_mem hx hy using 1 <;> ring
    have heq : q ((x : B) * (y : B)) = q (s x * s y) :=
      Ideal.Quotient.eq.mpr hdiff
    rw [heq]
    simp only [s, Algebra.smul_def, Finset.sum_mul, Finset.mul_sum, map_sum,
      map_mul, RingHom.comp_apply, a, v]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hreconstruct : ∀ u ∈ I ^ 2,
      q (2 * u) = ∑ i, ∑ j, a (second (D i) (D j) u) * v i * v j := by
    intro u hu
    rw [pow_two] at hu
    refine Submodule.mul_induction_on hu ?_ ?_
    · intro x hx y hy
      have hxy := hprod ⟨x, hx⟩ ⟨y, hy⟩
      have hswap :
          (∑ i, ∑ j, a ((D i).tensorProductTo y * (D j).tensorProductTo x) * v i * v j) =
          ∑ i, ∑ j, a ((D i).tensorProductTo x * (D j).tensorProductTo y) * v i * v j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [mul_comm ((D j).tensorProductTo y)]
        ring
      simp_rw [second_mul_of_mem _ _ x y hx hy, map_add, add_mul,
        Finset.sum_add_distrib]
      rw [hswap, ← hxy]
      simp only [map_mul, map_ofNat]
      ring
    · intro x y hx hy
      simp only [mul_add, map_add, add_mul, Finset.sum_add_distrib, hx, hy]
  have htwo : (2 : B) * t ∈ I ^ 3 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (2 * t) = 0
    rw [hreconstruct t ht]
    simp [h]
  have hinv : algebraMap ℂ B ((2 : ℂ)⁻¹) * (2 : B) = 1 := by
    calc
      algebraMap ℂ B ((2 : ℂ)⁻¹) * 2 =
          algebraMap ℂ B ((2 : ℂ)⁻¹ * 2) := by rw [map_mul, map_ofNat]
      _ = 1 := by norm_num
  simpa only [← mul_assoc, hinv, one_mul] using
    (I ^ 3).mul_mem_left (algebraMap ℂ B ((2 : ℂ)⁻¹)) htwo

/-- Smoothness is used only through finite projectivity of differentials. -/
theorem smooth_second_derivatives_detect [Algebra.Smooth ℂ A]
    (t : A ⊗[ℂ] A) (ht : t ∈ (KaehlerDifferential.ideal ℂ A) ^ 2)
    (h : ∀ D E : Derivation ℂ A A, second D E t = 0) :
    t ∈ (KaehlerDifferential.ideal ℂ A) ^ 3 := by
  obtain ⟨n, D, e, hframe⟩ := exists_first_order_frame (A := A)
  exact detect_of_first_order_frame n D e hframe t ht (fun i j => h (D i) (D j))

end LeBrunSalamon.SecondDiagonalAlgebra

end
