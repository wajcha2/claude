import Mathlib

/-!
## The cubic diagonal vanishing in `lines:cone-addition`

This is algebra on the actual diagonal ideal of `Spec A`, not a substitute
definition of the desired order of vanishing.  A skew tensor whose radial
Kahler one-form vanishes belongs to the cube of that diagonal ideal.

The geometric application still has to prove the radial one-form identity
on a smooth affine neighborhood of a nonzero point of the actual cone.
That identity is first-order horizontality, not the cubic conclusion.
The proof below needs neither a choice of local parameters nor a Taylor
expansion: interchange of the two factors acts by minus one on `I / I^2`
and by plus one on `I^2 / I^3`.

UNCOMPILED continuation, according to the user's 35,000-line build gate.
-/

noncomputable section
set_option autoImplicit false

open scoped TensorProduct BigOperators

namespace LeBrunSalamon.Construction.Lines.ConeDiagonal

variable (A : Type*) [CommRing A] [Algebra ℂ A]

/-- The actual ideal of the diagonal in the affine product. -/
abbrev diagonalIdeal : Ideal (A ⊗[ℂ] A) := KaehlerDifferential.ideal ℂ A

/-- Pullback by interchange of the two factors of the affine product. -/
abbrev swap : A ⊗[ℂ] A ≃ₐ[ℂ] A ⊗[ℂ] A :=
  Algebra.TensorProduct.comm ℂ A A

/-- Restriction of a function on the product to its diagonal. -/
abbrev multiply : A ⊗[ℂ] A →ₐ[ℂ] A :=
  Algebra.TensorProduct.lmul' ℂ

/-- The difference of the second and first pullbacks of an actual function. -/
def difference (a : A) : A ⊗[ℂ] A :=
  (1 : A) ⊗ₜ[ℂ] a - a ⊗ₜ[ℂ] (1 : A)

theorem difference_mem (a : A) : difference A a ∈ diagonalIdeal A :=
  KaehlerDifferential.one_smul_sub_smul_one_mem_ideal ℂ a

/-- These coordinate differences generate the full diagonal ideal. -/
theorem diagonalIdeal_eq_span_differences :
    diagonalIdeal A = Ideal.span (Set.range (difference A)) :=
  (KaehlerDifferential.span_range_eq_ideal ℂ A).symm

theorem multiply_swap (z : A ⊗[ℂ] A) :
    multiply A (swap A z) = multiply A z := by
  refine TensorProduct.inductionOn z ?_ ?_
  · intro a b
    simp only [swap, Algebra.TensorProduct.comm_tmul, multiply,
      Algebra.TensorProduct.lmul'_apply_tmul]
    exact mul_comm b a
  · intro u v hu hv
    simp only [map_add, hu, hv]

theorem swap_mem_diagonal {z : A ⊗[ℂ] A} (hz : z ∈ diagonalIdeal A) :
    swap A z ∈ diagonalIdeal A := by
  change multiply A (swap A z) = 0
  rw [multiply_swap]
  exact hz

/-- A pure-tensor identity proves the first-order sign of interchange.
The correction by the two diagonal pullbacks makes the assertion additive
in `z`, so it holds for every tensor and not only pure tensors. -/
theorem swap_add_sub_diagonal_mem_square (z : A ⊗[ℂ] A) :
    swap A z + z -
      ((1 : A) ⊗ₜ[ℂ] multiply A z + multiply A z ⊗ₜ[ℂ] (1 : A)) ∈
        diagonalIdeal A ^ 2 := by
  refine TensorProduct.inductionOn z ?_ ?_
  · intro a b
    have hp : difference A a * difference A b ∈ diagonalIdeal A ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (difference_mem A a) (difference_mem A b)
    have hid :
        swap A (a ⊗ₜ[ℂ] b) + a ⊗ₜ[ℂ] b -
          ((1 : A) ⊗ₜ[ℂ] multiply A (a ⊗ₜ[ℂ] b) +
            multiply A (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (1 : A)) =
        -(difference A a * difference A b) := by
      simp only [swap, Algebra.TensorProduct.comm_tmul, multiply,
        Algebra.TensorProduct.lmul'_apply_tmul, difference,
        sub_mul, mul_sub, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      abel
    rw [hid]
    exact (diagonalIdeal A ^ 2).neg_mem hp
  · intro u v hu hv
    convert (diagonalIdeal A ^ 2).add_mem hu hv using 1 <;>
      simp only [map_add, TensorProduct.tmul_add, TensorProduct.add_tmul] <;>
      abel

/-- Interchange acts by minus one on the conormal module `I / I^2`. -/
theorem swap_add_mem_square {z : A ⊗[ℂ] A} (hz : z ∈ diagonalIdeal A) :
    swap A z + z ∈ diagonalIdeal A ^ 2 := by
  have hdiag : multiply A z = 0 := hz
  simpa only [hdiag, TensorProduct.tmul_zero, TensorProduct.zero_tmul,
    add_zero, sub_zero] using swap_add_sub_diagonal_mem_square A z

/-- Interchange acts by plus one on `I^2 / I^3`.  Multiplicative
generators suffice, including all their finite sums. -/
theorem swap_sub_mem_cube {z : A ⊗[ℂ] A} (hz : z ∈ diagonalIdeal A ^ 2) :
    swap A z - z ∈ diagonalIdeal A ^ 3 := by
  rw [pow_two] at hz
  refine Submodule.mul_induction_on hz ?_ ?_
  · intro u hu v hv
    have hleft : (swap A u + u) * swap A v ∈ diagonalIdeal A ^ 3 := by
      rw [pow_succ]
      exact Ideal.mul_mem_mul (swap_add_mem_square A hu) (swap_mem_diagonal A hv)
    have hright : u * (swap A v + v) ∈ diagonalIdeal A ^ 3 := by
      rw [pow_succ']
      exact Ideal.mul_mem_mul hu (swap_add_mem_square A hv)
    convert (diagonalIdeal A ^ 3).sub_mem hleft hright using 1 <;>
      rw [map_mul] <;> ring
  · intro u v hu hv
    convert (diagonalIdeal A ^ 3).add_mem hu hv using 1 <;>
      simp only [map_add] <;> abel

/-- A skew tensor already vanishes on the diagonal.  Division by two
is performed in the base field, so no reducedness assumption on `A`
is hidden here. -/
theorem skew_mem_diagonal (z : A ⊗[ℂ] A) (hskew : swap A z = -z) :
    z ∈ diagonalIdeal A := by
  change multiply A z = 0
  have hneg : multiply A z = -(multiply A z) := by
    calc
      multiply A z = multiply A (swap A z) := (multiply_swap A z).symm
      _ = -(multiply A z) := by rw [hskew, map_neg]
  have hsum : multiply A z + multiply A z = 0 := by
    calc
      multiply A z + multiply A z = -(multiply A z) + multiply A z :=
        congrArg (fun t : A => t + multiply A z) hneg
      _ = 0 := neg_add_cancel _
  have htwo : (2 : ℂ) • multiply A z = 0 := by
    simpa only [two_smul] using hsum
  have hscaled := congrArg (fun t : A => (2 : ℂ)⁻¹ • t) htwo
  have htwo_ne : (2 : ℂ) ≠ 0 := by norm_num
  simpa only [smul_smul, inv_mul_cancel₀ htwo_ne, one_smul, smul_zero] using hscaled

/-- A skew element in the square of the diagonal ideal has no quadratic
symbol.  This is the source of the third, rather than second, order. -/
theorem skew_mem_cube_of_mem_square (z : A ⊗[ℂ] A)
    (hz : z ∈ diagonalIdeal A ^ 2) (hskew : swap A z = -z) :
    z ∈ diagonalIdeal A ^ 3 := by
  have h := swap_sub_mem_cube A hz
  have hsum : z + z ∈ diagonalIdeal A ^ 3 := by
    simpa only [hskew, neg_sub, sub_neg_eq_add] using (diagonalIdeal A ^ 3).neg_mem h
  have hscaled := ((diagonalIdeal A ^ 3).restrictScalars ℂ).smul_mem
    ((2 : ℂ)⁻¹) hsum
  change (2 : ℂ)⁻¹ • (z + z) ∈ diagonalIdeal A ^ 3 at hscaled
  have htwo_ne : (2 : ℂ) ≠ 0 := by norm_num
  rw [← two_smul ℂ z, smul_smul, inv_mul_cancel₀ htwo_ne, one_smul] at hscaled
  exact hscaled

/-- The universal first derivative is exactly the conormal class, so
first-order vanishing gives membership in `I^2`. -/
theorem mem_square_of_firstDerivative_zero (z : A ⊗[ℂ] A)
    (hz : z ∈ diagonalIdeal A)
    (hderiv : (KaehlerDifferential.D ℂ A).tensorProductTo z = 0) :
    z ∈ diagonalIdeal A ^ 2 := by
  apply ((diagonalIdeal A).toCotangent_eq_zero ⟨z, hz⟩).mp
  rw [← KaehlerDifferential.D_tensorProductTo]
  exact hderiv

/-- The algebraic core of the cubic diagonal assertion.  The input is
the actual first derivative and actual interchange map; the conclusion
is membership in the actual third power of the diagonal ideal. -/
theorem skew_mem_cube_of_firstDerivative_zero (z : A ⊗[ℂ] A)
    (hskew : swap A z = -z)
    (hderiv : (KaehlerDifferential.D ℂ A).tensorProductTo z = 0) :
    z ∈ diagonalIdeal A ^ 3 :=
  skew_mem_cube_of_mem_square A z
    (mem_square_of_firstDerivative_zero A z (skew_mem_diagonal A z hskew) hderiv)
    hskew

section Coordinates

variable {A} {ι : Type*} [Fintype ι]

/-- The actual function `omega(r(p),r(q))` on an affine chart product,
written using its restricted ambient coordinate functions. -/
def coordinatePairing (r : ι → A) (ω : ι → ι → ℂ) : A ⊗[ℂ] A :=
  ∑ i, ∑ j, (ω i j) • (r i ⊗ₜ[ℂ] r j)

/-- The radial contraction `omega(r,dr)` as an actual Kahler one-form. -/
def radialForm (r : ι → A) (ω : ι → ι → ℂ) : KaehlerDifferential ℂ A :=
  ∑ i, ∑ j, (ω i j) • (r i • KaehlerDifferential.D ℂ A (r j))

theorem swap_coordinatePairing (r : ι → A) (ω : ι → ι → ℂ)
    (hskew : ∀ i j, ω j i = -ω i j) :
    swap A (coordinatePairing r ω) = -coordinatePairing r ω := by
  unfold coordinatePairing
  simp only [map_sum, map_smul, swap, Algebra.TensorProduct.comm_tmul]
  rw [Finset.sum_comm]
  trans ∑ i, ∑ j, (-ω i j) • (r i ⊗ₜ[ℂ] r j)
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hskew i j]
  · simp only [neg_smul, Finset.sum_neg_distrib]

theorem firstDerivative_coordinatePairing (r : ι → A) (ω : ι → ι → ℂ) :
    (KaehlerDifferential.D ℂ A).tensorProductTo (coordinatePairing r ω) =
      radialForm r ω := by
  unfold coordinatePairing radialForm
  simp only [map_sum, LinearMap.map_smul_of_tower,
    Derivation.tensorProductTo_tmul]

/-- A skew ambient form and radial horizontality on the chart imply
the cubic diagonal vanishing used in `lines:cone-addition`.  Deriving
`hradial` from the geometric conical Lagrangian tangent spaces remains
a separately visible geometric obligation. -/
theorem coordinatePairing_mem_cube (r : ι → A) (ω : ι → ι → ℂ)
    (hskew : ∀ i j, ω j i = -ω i j) (hradial : radialForm r ω = 0) :
    coordinatePairing r ω ∈ diagonalIdeal A ^ 3 := by
  apply skew_mem_cube_of_firstDerivative_zero A
    (coordinatePairing r ω) (swap_coordinatePairing r ω hskew)
  rw [firstDerivative_coordinatePairing, hradial]

end Coordinates

section Evaluation

variable {A} {B : Type*} [CommRing B] [Algebra ℂ B]

/-- Pullback along two actual `B`-valued points of the affine chart. -/
def pairEvaluation (p q : A →ₐ[ℂ] B) : A ⊗[ℂ] A →ₐ[ℂ] B :=
  Algebra.TensorProduct.lift p q (fun _ _ => Commute.all _ _)

theorem pairEvaluation_tmul (p q : A →ₐ[ℂ] B) (a b : A) :
    pairEvaluation p q (a ⊗ₜ[ℂ] b) = p a * q b :=
  Algebra.TensorProduct.lift_tmul _ _ _ a b

theorem pairEvaluation_difference (p q : A →ₐ[ℂ] B) (a : A) :
    pairEvaluation p q (difference A a) = q a - p a := by
  simp only [difference, map_sub, pairEvaluation_tmul, map_one, one_mul, mul_one]

theorem pairEvaluation_coordinatePairing {ι : Type*} [Fintype ι]
    (p q : A →ₐ[ℂ] B) (r : ι → A) (ω : ι → ι → ℂ) :
    pairEvaluation p q (coordinatePairing r ω) =
      ∑ i, ∑ j, (ω i j) • (p (r i) * q (r j)) := by
  simp only [coordinatePairing, map_sum, map_smul, pairEvaluation_tmul]

end Evaluation

end LeBrunSalamon.Construction.Lines.ConeDiagonal

end
