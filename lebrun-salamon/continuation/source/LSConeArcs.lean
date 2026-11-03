import LSConeDiagonal
import LSConePole

/-!
## From the actual diagonal ideal to the rescaled-arc contradiction

SOURCE: `lines:cone-addition`. This joins the diagonal calculation to the
power-series calculation through the actual tensor-product evaluation of
two arcs. In particular the cubic ideal is not replaced by a pointwise
predicate, and agreement of the two arcs is tested on the nonreduced
quotient `C[[t]]/(t^k)`, not only on their common closed point.

The later geometric proof must construct the smooth cone chart and the
two regular arcs, establish the radial Kahler one-form identity on that
chart, and establish their agreement modulo the full `t^k`.

STATUS: new source; compilation deferred by the 35,000-line gate.
-/

noncomputable section
set_option autoImplicit false

open scoped TensorProduct BigOperators

namespace LeBrunSalamon.Construction.Lines.ConeArcs

open ConeDiagonal ConePole

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- Actual order-k infinitesimal neighborhood of the special point of
the formal disc. The zero-order quotient is allowed in this definition. -/
abbrev TruncatedDisc (k : ℕ) := Series ⧸ orderIdeal k

/-- A formal arc restricted to this nonreduced test algebra. -/
def reduction (k : ℕ) (p : A →ₐ[ℂ] Series) : A →ₐ[ℂ] TruncatedDisc k :=
  (Ideal.Quotient.mkₐ ℂ (orderIdeal k)).comp p

/-- Equality of truncated arcs is precisely congruence of every regular
function, with the sign chosen to match `ConeDiagonal.difference`. -/
theorem reduction_eq_iff (k : ℕ) (p q : A →ₐ[ℂ] Series) :
    reduction k p = reduction k q ↔
      ∀ a : A, q a - p a ∈ orderIdeal k := by
  constructor
  · intro h a
    have ha := congrArg (fun f : A →ₐ[ℂ] TruncatedDisc k => f a) h
    change Ideal.Quotient.mk (orderIdeal k) (p a) =
      Ideal.Quotient.mk (orderIdeal k) (q a) at ha
    exact Ideal.Quotient.eq.mp ha.symm
  · intro h
    ext a
    change Ideal.Quotient.mk (orderIdeal k) (p a) =
      Ideal.Quotient.mk (orderIdeal k) (q a)
    exact (Ideal.Quotient.eq.mpr (h a)).symm

/-- Agreement of arcs modulo `t^k` bounds the image of the full diagonal
ideal, using its actual generators `1⊗a-a⊗1`. -/
theorem diagonal_pullback_mem (k : ℕ) (p q : A →ₐ[ℂ] Series)
    (hclose : ∀ a : A, q a - p a ∈ orderIdeal k) :
    ∀ z ∈ diagonalIdeal A, pairEvaluation p q z ∈ orderIdeal k := by
  have hI : diagonalIdeal A ≤
      (orderIdeal k).comap (pairEvaluation p q).toRingHom := by
    rw [diagonalIdeal_eq_span_differences]
    apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change pairEvaluation p q (difference A a) ∈ orderIdeal k
    rw [pairEvaluation_difference]
    exact hclose a
  exact hI

theorem diagonal_pullback_mem_of_reduction_eq (k : ℕ)
    (p q : A →ₐ[ℂ] Series) (hclose : reduction k p = reduction k q) :
    ∀ z ∈ diagonalIdeal A, pairEvaluation p q z ∈ orderIdeal k :=
  diagonal_pullback_mem k p q ((reduction_eq_iff k p q).mp hclose)

/-- The tensor-pairing function and the coordinate expression for the
scalar-extended symplectic form agree under the actual arc maps. -/
theorem pairEvaluation_eq_coordinatePairing {ι : Type*} [Fintype ι]
    (p q : A →ₐ[ℂ] Series) (r : ι → A) (ω : ι → ι → ℂ) :
    pairEvaluation p q (coordinatePairing r ω) =
      ConePairing.pairing ω (fun i => p (r i)) (fun i => q (r i)) := by
  rw [pairEvaluation_coordinatePairing]
  unfold ConePairing.pairing
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Algebra.smul_def]
  ring

/-- Cubic diagonal vanishing pulls back to order at least `3*k` when
both arguments vary. This is the step for which merely vanishing to
second order, or merely having the same closed point, would not suffice. -/
theorem pairing_mem_triple_order {ι : Type*} [Fintype ι]
    (p q : A →ₐ[ℂ] Series) (r : ι → A) (ω : ι → ι → ℂ)
    (hskew : ∀ i j, ω j i = -ω i j) (hradial : radialForm r ω = 0)
    (k : ℕ) (hclose : reduction k p = reduction k q) :
    ConePairing.pairing ω (fun i => p (r i)) (fun i => q (r i)) ∈
      orderIdeal (3 * k) := by
  have h := pullback_power_mem (diagonalIdeal A)
    (pairEvaluation p q).toRingHom k 3
    (diagonal_pullback_mem_of_reduction_eq k p q hclose)
    (coordinatePairing_mem_cube r ω hskew hradial)
  change pairEvaluation p q (coordinatePairing r ω) ∈ orderIdeal (k * 3) at h
  rw [pairEvaluation_eq_coordinatePairing] at h
  simpa only [Nat.mul_comm] using h

/-- The connected algebraic core of the cone-addition contradiction:
the two arcs agree to order k on the actual affine cone chart, the radial
form vanishes there, and their meromorphic antecedents have a nonzero
constant pairing. Their rescalings cannot satisfy all these facts.

This is not yet the dominance theorem: extracting this data from a
positive-dimensional addition fiber is the next geometric obligation. -/
theorem rescaled_nonorthogonal_arcs_impossible
    {ι : Type*} [Fintype ι] {K : Type*} [CommRing K] [Algebra ℂ K]
    (p q : A →ₐ[ℂ] Series) (r : ι → A) (ω : ι → ι → ℂ)
    (hskew : ∀ i j, ω j i = -ω i j) (hradial : radialForm r ω = 0)
    (k : ℕ) (hk : 0 < k) (hclose : reduction k p = reduction k q)
    (j : Series →ₐ[ℂ] K) (hj : Function.Injective j)
    (a b : ι → K) (c : ℂ) (hc : c ≠ 0)
    (hp : ∀ i, j (p (r i)) = j (PowerSeries.X : Series) ^ k * a i)
    (hq : ∀ i, j (q (r i)) = -(j (PowerSeries.X : Series) ^ k * b i))
    (hpair : ConePairing.pairing ω a b = algebraMap ℂ K c) : False := by
  have horder := pairing_mem_triple_order p q r ω hskew hradial k hclose
  rw [ConePairing.regular_rescaling_pairing j hj ω a b
    (fun i => p (r i)) (fun i => q (r i)) k c hp hq hpair] at horder
  exact double_order_not_triple k hk c hc horder

end LeBrunSalamon.Construction.Lines.ConeArcs

end
