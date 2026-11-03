import LSPublishedPicard
import LSAffineDerivations
import RecompileBase

noncomputable section

set_option autoImplicit false
open Bundle
open scoped Bundle ContDiff ENNReal
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing
open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.Limits

/- BEGIN UNCOMPILED continuation cech_normal_form.lean.txt -/
/-!
Explicit normal forms for the polynomial two-chart Cech complex.

Continuation draft: no Lean invocation has been made for this file. The maps
below concern the actual polynomial/Laurent complex already defined in
P1Overlap. They do not identify this complex with sheaf cohomology.
-/

noncomputable section
set_option autoImplicit false

namespace LeBrunSalamon.P1Overlap

open Polynomial
open scoped LaurentPolynomial BigOperators

variable {K : Type*} [Field K]

/-- Extend prescribed values of Laurent monomials by finite linear combination. -/
def laurentLinearLift {V : Type*} [AddCommGroup V] [Module K V]
    (v : ℤ → V) : K[T;T⁻¹] →ₗ[K] V :=
  (Finsupp.linearCombination K v).comp
    (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

@[simp]
theorem laurentLinearLift_single {V : Type*} [AddCommGroup V] [Module K V]
    (v : ℤ → V) (n : ℤ) (c : K) :
    laurentLinearLift v (AddMonoidAlgebra.single n c) = c • v n := by
  change (Finsupp.linearCombination K v) (Finsupp.single n c) = c • v n
  exact Finsupp.linearCombination_single K c n

theorem laurentLinearLift_C_mul_T {V : Type*} [AddCommGroup V] [Module K V]
    (v : ℤ → V) (n : ℤ) (c : K) :
    laurentLinearLift v (LaurentPolynomial.C c * LaurentPolynomial.T n) = c • v n := by
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  exact laurentLinearLift_single v n c

/-- The canonical representative of a Laurent coboundary class: retain exactly
the exponents strictly between `d` and `0`. No splitting choice is involved. -/
def cechNormalForm (d : ℤ) : K[T;T⁻¹] →ₗ[K] K[T;T⁻¹] where
  toFun f := AddMonoidAlgebra.ofCoeff (f.coeff.filter (fun n => d < n ∧ n < 0))
  map_add' f g := by
    apply LaurentPolynomial.ext
    intro n
    by_cases hn : d < n ∧ n < 0 <;> simp [Finsupp.filter_apply, hn]
  map_smul' c f := by
    apply LaurentPolynomial.ext
    intro n
    by_cases hn : d < n ∧ n < 0 <;> simp [Finsupp.filter_apply, hn]

theorem cechNormalForm_coeff (d n : ℤ) (f : K[T;T⁻¹]) :
    (cechNormalForm d f).coeff n = if d < n ∧ n < 0 then f.coeff n else 0 := by
  simp [cechNormalForm, Finsupp.filter_apply]

theorem cechNormalForm_single (d n : ℤ) (c : K) :
    cechNormalForm d (AddMonoidAlgebra.single n c) =
      if d < n ∧ n < 0 then AddMonoidAlgebra.single n c else 0 := by
  apply LaurentPolynomial.ext
  intro m
  by_cases hnm : n = m
  · subst m
    by_cases hn : d < n ∧ n < 0 <;>
      simp [cechNormalForm_coeff, hn, -LaurentPolynomial.single_eq_C_mul_T]
  · by_cases hn : d < n ∧ n < 0 <;>
      simp [cechNormalForm_coeff, hn, AddMonoidAlgebra.coeff_single,
        Finsupp.single_apply, hnm, -LaurentPolynomial.single_eq_C_mul_T]

theorem cechNormalForm_C_mul_T (d n : ℤ) (c : K) :
    cechNormalForm d (LaurentPolynomial.C c * LaurentPolynomial.T n) =
      if d < n ∧ n < 0 then LaurentPolynomial.C c * LaurentPolynomial.T n else 0 := by
  simpa only [LaurentPolynomial.single_eq_C_mul_T] using cechNormalForm_single d n c

@[simp]
theorem cechNormalForm_idempotent (d : ℤ) (f : K[T;T⁻¹]) :
    cechNormalForm d (cechNormalForm d f) = cechNormalForm d f := by
  apply LaurentPolynomial.ext
  intro n
  by_cases hn : d < n ∧ n < 0 <;> simp [cechNormalForm_coeff, hn]

@[simp]
theorem gapProjection_normalForm (d : ℤ) (f : K[T;T⁻¹]) :
    gapProjection d (cechNormalForm d f) = gapProjection d f := by
  funext i
  change (cechNormalForm d f).coeff (-(i.val : ℤ) - 1) =
    f.coeff (-(i.val : ℤ) - 1)
  have hi := i.isLt
  have hgap : d < -(i.val : ℤ) - 1 ∧ -(i.val : ℤ) - 1 < 0 := by
    constructor <;> omega
  rw [cechNormalForm_coeff, if_pos hgap]

theorem cechNormalForm_eq_zero_iff (d : ℤ) (f : K[T;T⁻¹]) :
    cechNormalForm d f = 0 ↔ gapProjection d f = 0 := by
  constructor
  · intro hf
    rw [← gapProjection_normalForm d f, hf, map_zero]
  · intro hf
    apply LaurentPolynomial.ext
    intro n
    rw [cechNormalForm_coeff]
    by_cases hn : d < n ∧ n < 0
    · rw [if_pos hn]
      let i : Fin (-d - 1).toNat := ⟨(-n - 1).toNat, by omega⟩
      have hi := congrFun hf i
      change f.coeff (-(i.val : ℤ) - 1) = 0 at hi
      have he : -(i.val : ℤ) - 1 = n := by dsimp [i]; omega
      simpa only [he, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hi
    · simp only [if_neg hn, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

theorem mem_cechRange_iff_normalForm_zero (d : ℤ) (f : K[T;T⁻¹]) :
    f ∈ LinearMap.range (cechDifference d) ↔ cechNormalForm d f = 0 := by
  rw [← gapProjection_kernel]
  exact (cechNormalForm_eq_zero_iff d f).symm

@[simp]
theorem cechNormalForm_difference (d : ℤ) (pq : K[X] × K[X]) :
    cechNormalForm d (cechDifference d pq) = 0 :=
  (mem_cechRange_iff_normalForm_zero d _).mp ⟨pq, rfl⟩

theorem same_normalForm_iff (d : ℤ) (f g : K[T;T⁻¹]) :
    cechNormalForm d f = cechNormalForm d g ↔
      f - g ∈ LinearMap.range (cechDifference d) := by
  rw [mem_cechRange_iff_normalForm_zero, map_sub, sub_eq_zero]

/-- A preferred primitive for a single Laurent basis element. Nonnegative
exponents go to the first chart, negative exponents at most `d` to the second.
The minus sign agrees with `cechDifference = first - second`. -/
def cechPrimitiveMonomial (d n : ℤ) : K[X] × K[X] :=
  if 0 ≤ n then (Polynomial.monomial n.toNat 1, 0)
  else if n ≤ d then (0, Polynomial.monomial (d - n).toNat (-1))
  else 0

/-- A concrete linear solver modulo the finite-dimensional obstruction space. -/
def cechHomotopy (d : ℤ) : K[T;T⁻¹] →ₗ[K] (K[X] × K[X]) :=
  laurentLinearLift (cechPrimitiveMonomial d)

theorem cechPrimitiveMonomial_difference (d n : ℤ) :
    cechDifference d (cechPrimitiveMonomial (K := K) d n) =
      if 0 ≤ n ∨ n ≤ d then LaurentPolynomial.T n else 0 := by
  by_cases hn : 0 ≤ n
  · rw [cechPrimitiveMonomial, if_pos hn, if_pos (Or.inl hn)]
    change (Polynomial.monomial n.toNat (1 : K)).toLaurent -
      LaurentPolynomial.invert (0 : K[X]).toLaurent * LaurentPolynomial.T d = _
    simp only [Polynomial.toLaurent_C_mul_T, map_one, one_mul,
      map_zero, zero_mul, sub_zero]
    rw [Int.toNat_of_nonneg hn]
  · by_cases hnd : n ≤ d
    · rw [cechPrimitiveMonomial, if_neg hn, if_pos hnd,
        if_pos (Or.inr hnd)]
      change 0 - LaurentPolynomial.invert
        ((Polynomial.monomial (d - n).toNat (-1 : K)).toLaurent) *
          LaurentPolynomial.T d = _
      rw [Polynomial.toLaurent_C_mul_T, map_mul, LaurentPolynomial.invert_C,
        LaurentPolynomial.invert_T, LaurentPolynomial.mul_T_assoc,
        Int.toNat_of_nonneg (sub_nonneg.mpr hnd)]
      have he : -(d - n) + d = n := by omega
      rw [he]
      simp only [map_neg, map_one, neg_one_mul, zero_sub, neg_neg]
    · rw [cechPrimitiveMonomial, if_neg hn, if_neg hnd,
        if_neg (not_or.mpr ⟨hn, hnd⟩), map_zero]

theorem scalar_smul_T (c : K) (n : ℤ) :
    c • (LaurentPolynomial.T n : K[T;T⁻¹]) =
      LaurentPolynomial.C c * LaurentPolynomial.T n := by
  change c • AddMonoidAlgebra.single n (1 : K) = _
  rw [AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  exact LaurentPolynomial.single_eq_C_mul_T c n

theorem cechHomotopy_difference_monomial (d n : ℤ) (c : K) :
    cechDifference d (cechHomotopy d
      (LaurentPolynomial.C c * LaurentPolynomial.T n)) =
      if 0 ≤ n ∨ n ≤ d then LaurentPolynomial.C c * LaurentPolynomial.T n else 0 := by
  rw [cechHomotopy, laurentLinearLift_C_mul_T, map_smul,
    cechPrimitiveMonomial_difference]
  by_cases hn : 0 ≤ n ∨ n ≤ d
  · simp only [if_pos hn, scalar_smul_T]
  · simp only [if_neg hn, smul_zero]

/-- The explicit decomposition into a polynomial coboundary and its gap terms. -/
theorem cechHomotopy_decomposition (d : ℤ) (f : K[T;T⁻¹]) :
    cechDifference d (cechHomotopy d f) + cechNormalForm d f = f := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
    rw [map_add, map_add, map_add]
    calc
      cechDifference d (cechHomotopy d f) + cechDifference d (cechHomotopy d g) +
          (cechNormalForm d f + cechNormalForm d g) =
        (cechDifference d (cechHomotopy d f) + cechNormalForm d f) +
          (cechDifference d (cechHomotopy d g) + cechNormalForm d g) := by abel
      _ = f + g := by rw [hf, hg]
  | C_mul_T n c =>
    rw [cechHomotopy_difference_monomial, cechNormalForm_C_mul_T]
    by_cases hn : 0 ≤ n ∨ n ≤ d
    · have hgap : ¬ (d < n ∧ n < 0) := by omega
      simp only [if_pos hn, if_neg hgap, add_zero]
    · have hgap : d < n ∧ n < 0 := by omega
      simp only [if_neg hn, if_pos hgap, zero_add]

theorem cechHomotopy_difference (d : ℤ) (f : K[T;T⁻¹]) :
    cechDifference d (cechHomotopy d f) = f - cechNormalForm d f := by
  exact eq_sub_iff_add_eq.mpr (cechHomotopy_decomposition d f)

theorem cechHomotopy_solves (d : ℤ) (f : K[T;T⁻¹])
    (hf : cechNormalForm d f = 0) : cechDifference d (cechHomotopy d f) = f := by
  rw [cechHomotopy_difference, hf, sub_zero]

theorem cechNormalForm_zero_of_ge_neg_one (d : ℤ) (hd : -1 ≤ d)
    (f : K[T;T⁻¹]) : cechNormalForm d f = 0 := by
  apply LaurentPolynomial.ext
  intro n
  have hn : ¬ (d < n ∧ n < 0) := by omega
  simp only [cechNormalForm_coeff, if_neg hn, AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply]

/-- In the vanishing range this is a specified linear right inverse, stronger
than the previous existential surjectivity statement. -/
theorem cechHomotopy_rightInverse (d : ℤ) (hd : -1 ≤ d) :
    Function.RightInverse (cechHomotopy (K := K) d) (cechDifference d) := by
  intro f
  exact cechHomotopy_solves d f (cechNormalForm_zero_of_ge_neg_one d hd f)

theorem cechHomotopy_rightInverse_linear (d : ℤ) (hd : -1 ≤ d) :
    (cechDifference (K := K) d).comp (cechHomotopy d) = LinearMap.id := by
  apply LinearMap.ext
  intro f
  exact cechHomotopy_rightInverse (K := K) d hd f

/-- A matching pair is precisely a zero coboundary, with the original convention. -/
theorem matchingSpace_difference_zero (d : ℤ) (s : matchingSpace (K := K) d) :
    cechDifference d s.val = 0 := by
  have hs : s.val ∈ LinearMap.ker (cechDifference d) := by
    rw [cechDifference_kernel]
    exact s.property
  exact hs

/-- Any two solutions differ by a matching pair; this is the affine freedom in
choosing local splittings, not a new geometric extension assertion. -/
theorem cech_solutions_difference (d : ℤ) (f : K[T;T⁻¹])
    (pq rs : K[X] × K[X]) (hpq : cechDifference d pq = f)
    (hrs : cechDifference d rs = f) : pq - rs ∈ matchingSpace d := by
  rw [← cechDifference_kernel]
  change cechDifference d (pq - rs) = 0
  rw [map_sub, hpq, hrs, sub_self]

/-- The complete solution set of a solvable Cech equation is an affine copy of
the already computed matching space, with a concrete selected origin. -/
def cechSolutionEquiv (d : ℤ) (f : K[T;T⁻¹]) (hf : cechNormalForm d f = 0) :
    {pq : K[X] × K[X] // cechDifference d pq = f} ≃ matchingSpace (K := K) d where
  toFun s := ⟨s.val - cechHomotopy d f,
    cech_solutions_difference d f s.val (cechHomotopy d f) s.property
      (cechHomotopy_solves d f hf)⟩
  invFun s := ⟨cechHomotopy d f + s.val, by
    rw [map_add, cechHomotopy_solves d f hf, matchingSpace_difference_zero, add_zero]⟩
  left_inv s := by
    apply Subtype.ext
    change cechHomotopy d f + (s.val - cechHomotopy d f) = s.val
    abel
  right_inv s := by
    apply Subtype.ext
    change cechHomotopy d f + s.val - cechHomotopy d f = s.val
    abel

/-- Reinsert the missing coefficients as a finite Laurent sum. -/
def gapRepresentative (d : ℤ) :
    (Fin (-d - 1).toNat → K) →ₗ[K] K[T;T⁻¹] where
  toFun v := ∑ i, AddMonoidAlgebra.single (-(i.val : ℤ) - 1) (v i)
  map_add' v w := by
    simp only [Pi.add_apply, AddMonoidAlgebra.single_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, Finset.smul_sum, AddMonoidAlgebra.smul_single,
      RingHom.id_apply]

@[simp]
theorem gapProjection_representative (d : ℤ) (v : Fin (-d - 1).toNat → K) :
    gapProjection d (gapRepresentative d v) = v := by
  funext i
  change (∑ j : Fin (-d - 1).toNat,
    AddMonoidAlgebra.single (-(j.val : ℤ) - 1) (v j)).coeff (-(i.val : ℤ) - 1) = v i
  simp only [AddMonoidAlgebra.coeff_sum, Finset.sum_apply',
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : -(j.val : ℤ) - 1 ≠ -(i.val : ℤ) - 1 := by
      intro he
      apply hji
      apply Fin.ext
      omega
    simp only [hne, ite_false]
  · simp

theorem gapRepresentative_injective (d : ℤ) :
    Function.Injective (gapRepresentative (K := K) d) := by
  intro v w hvw
  simpa only [gapProjection_representative] using congrArg (gapProjection d) hvw

@[simp]
theorem cechNormalForm_representative (d : ℤ) (v : Fin (-d - 1).toNat → K) :
    cechNormalForm d (gapRepresentative d v) = gapRepresentative d v := by
  change cechNormalForm d (∑ i : Fin (-d - 1).toNat,
    AddMonoidAlgebra.single (-(i.val : ℤ) - 1) (v i)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi := i.isLt
  have hgap : d < -(i.val : ℤ) - 1 ∧ -(i.val : ℤ) - 1 < 0 := by
    constructor <;> omega
  rw [cechNormalForm_single, if_pos hgap]

theorem cechNormalForm_fixed_injective (d : ℤ) (f g : K[T;T⁻¹])
    (hf : cechNormalForm d f = f) (hg : cechNormalForm d g = g)
    (h : gapProjection d f = gapProjection d g) : f = g := by
  have hz : cechNormalForm d (f - g) = 0 := by
    apply (cechNormalForm_eq_zero_iff d _).mpr
    rw [map_sub, h, sub_self]
  rw [map_sub, hf, hg] at hz
  exact sub_eq_zero.mp hz

@[simp]
theorem gapRepresentative_projection (d : ℤ) (f : K[T;T⁻¹]) :
    gapRepresentative d (gapProjection d f) = cechNormalForm d f := by
  apply cechNormalForm_fixed_injective d
  · exact cechNormalForm_representative d _
  · exact cechNormalForm_idempotent d f
  · rw [gapProjection_representative, gapProjection_normalForm]

/-- The zero class is detected by the gap coefficients, and every class has
exactly one representative with support in the gap. -/
theorem cech_class_has_unique_normal_form (d : ℤ) (f : K[T;T⁻¹]) :
    ∃! g : K[T;T⁻¹], cechNormalForm d g = g ∧
      f - g ∈ LinearMap.range (cechDifference d) := by
  refine ⟨cechNormalForm d f, ⟨cechNormalForm_idempotent d f, ?_⟩, ?_⟩
  · apply (same_normalForm_iff d _ _).mp
    exact (cechNormalForm_idempotent d f).symm
  · intro g hg
    have he := (same_normalForm_iff d f g).mpr hg.2
    exact hg.1.symm.trans he.symm

theorem gapRepresentative_mem_cechRange_iff (d : ℤ) (v : Fin (-d - 1).toNat → K) :
    gapRepresentative d v ∈ LinearMap.range (cechDifference d) ↔ v = 0 := by
  rw [← gapProjection_kernel]
  change gapProjection d (gapRepresentative d v) = 0 ↔ v = 0
  rw [gapProjection_representative]

/-- A concrete nonzero obstruction in each missing degree. This is a statement
about the Laurent complex; constructing the corresponding sheaf extension is
a separate required comparison. -/
theorem gapMonomial_not_mem_cechRange (d n : ℤ) (hn : d < n ∧ n < 0) :
    (LaurentPolynomial.T n : K[T;T⁻¹]) ∉ LinearMap.range (cechDifference d) := by
  intro hf
  have hz := (mem_cechRange_iff_normalForm_zero d _).mp hf
  have he : cechNormalForm d (LaurentPolynomial.T n : K[T;T⁻¹]) =
      LaurentPolynomial.T n := by
    simpa only [map_one, one_mul, if_pos hn] using cechNormalForm_C_mul_T d n (1 : K)
  rw [he] at hz
  exact (LaurentPolynomial.isUnit_T n).ne_zero hz

/-- The full Laurent module splits into actual coboundaries and the finite
obstruction coordinates, with an explicit inverse and no basis choice. -/
def cechRangeGapEquiv (d : ℤ) :
    K[T;T⁻¹] ≃ₗ[K]
      LinearMap.range (cechDifference (K := K) d) × (Fin (-d - 1).toNat → K) where
  toFun f := (⟨f - cechNormalForm d f, by
      exact ⟨cechHomotopy d f, cechHomotopy_difference d f⟩⟩, gapProjection d f)
  invFun v := v.1.val + gapRepresentative d v.2
  left_inv f := by
    change f - cechNormalForm d f + gapRepresentative d (gapProjection d f) = f
    rw [gapRepresentative_projection]
    exact sub_add_cancel _ _
  right_inv v := by
    apply Prod.ext
    · apply Subtype.ext
      change v.1.val + gapRepresentative d v.2 -
        cechNormalForm d (v.1.val + gapRepresentative d v.2) = v.1.val
      rw [map_add, (mem_cechRange_iff_normalForm_zero d _).mp v.1.property,
        cechNormalForm_representative, zero_add, add_sub_cancel_right]
    · change gapProjection d (v.1.val + gapRepresentative d v.2) = v.2
      have hv : gapProjection d v.1.val = 0 := by
        apply (cechNormalForm_eq_zero_iff d _).mp
        exact (mem_cechRange_iff_normalForm_zero d _).mp v.1.property
      rw [map_add, hv, gapProjection_representative, zero_add]
  map_add' f g := by
    apply Prod.ext
    · apply Subtype.ext
      change f + g - cechNormalForm d (f + g) =
        (f - cechNormalForm d f) + (g - cechNormalForm d g)
      rw [map_add]
      abel
    · exact (gapProjection d).map_add f g
  map_smul' c f := by
    apply Prod.ext
    · apply Subtype.ext
      change c • f - cechNormalForm d (c • f) = c • (f - cechNormalForm d f)
      rw [map_smul, smul_sub]
    · exact (gapProjection d).map_smul c f

end LeBrunSalamon.P1Overlap

end
/- END UNCOMPILED continuation cech_normal_form.lean.txt -/


/- BEGIN UNCOMPILED continuation coefficient_transport.lean.txt -/
/-!
Coefficient transport for the Laurent matching complex.

Uncompiled continuation. A change of the complex-base identification may
induce a nontrivial field automorphism. These maps retain that automorphism
explicitly instead of declaring canonical coordinates complex-linear.
-/

noncomputable section
set_option autoImplicit false

namespace LeBrunSalamon.P1Overlap

open Polynomial
open scoped LaurentPolynomial BigOperators

variable {K : Type*} [Field K]

/-- Apply a field automorphism coefficientwise, fixing the Laurent variable. -/
def laurentCoefficientEquiv (σ : K ≃+* K) : K[T;T⁻¹] ≃+* K[T;T⁻¹] :=
  AddMonoidAlgebra.mapRingEquiv ℤ σ

@[simp]
theorem laurentCoefficientEquiv_coeff (σ : K ≃+* K) (f : K[T;T⁻¹]) (n : ℤ) :
    (laurentCoefficientEquiv σ f).coeff n = σ (f.coeff n) :=
  AddMonoidAlgebra.coeff_mapRingEquiv σ f n

@[simp]
theorem polynomialCoefficientEquiv_coeff (σ : K ≃+* K) (p : K[X]) (n : ℕ) :
    (Polynomial.mapEquiv σ p).coeff n = σ (p.coeff n) := by
  change (p.map σ.toRingHom).coeff n = σ (p.coeff n)
  exact Polynomial.coeff_map _ _

@[simp]
theorem laurentCoefficientEquiv_T (σ : K ≃+* K) (n : ℤ) :
    laurentCoefficientEquiv σ (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
  simpa only [laurentCoefficientEquiv, LaurentPolynomial.T, map_one] using
    (AddMonoidAlgebra.mapRingEquiv_single σ (1 : K) n)

@[simp]
theorem laurentCoefficientEquiv_C (σ : K ≃+* K) (c : K) :
    laurentCoefficientEquiv σ (LaurentPolynomial.C c) = LaurentPolynomial.C (σ c) := by
  rw [← LaurentPolynomial.single_eq_C, ← LaurentPolynomial.single_eq_C]
  exact AddMonoidAlgebra.mapRingEquiv_single σ c 0

@[simp]
theorem laurentCoefficientEquiv_invert (σ : K ≃+* K) (f : K[T;T⁻¹]) :
    laurentCoefficientEquiv σ (LaurentPolynomial.invert f) =
      LaurentPolynomial.invert (laurentCoefficientEquiv σ f) := by
  apply LaurentPolynomial.ext
  intro n
  simp only [laurentCoefficientEquiv_coeff, LaurentPolynomial.invert_apply]

@[simp]
theorem laurentCoefficientEquiv_toLaurent (σ : K ≃+* K) (p : K[X]) :
    laurentCoefficientEquiv σ p.toLaurent = (Polynomial.mapEquiv σ p).toLaurent := by
  apply LaurentPolynomial.ext
  intro n
  rw [laurentCoefficientEquiv_coeff]
  cases n with
  | ofNat n =>
    change σ (p.toLaurent.coeff (n : ℤ)) =
      (Polynomial.mapEquiv σ p).toLaurent.coeff (n : ℤ)
    rw [coeff_toLaurent_nat p n, coeff_toLaurent_nat (Polynomial.mapEquiv σ p) n,
      polynomialCoefficientEquiv_coeff]
  | negSucc n =>
    rw [coeff_toLaurent_neg p (by omega),
      coeff_toLaurent_neg (Polynomial.mapEquiv σ p) (by omega), map_zero]

theorem laurentCoefficientEquiv_smul (σ : K ≃+* K) (c : K) (f : K[T;T⁻¹]) :
    laurentCoefficientEquiv σ (c • f) = σ c • laurentCoefficientEquiv σ f := by
  apply LaurentPolynomial.ext
  intro n
  simp only [laurentCoefficientEquiv_coeff, AddMonoidAlgebra.coeff_smul,
    Finsupp.smul_apply, smul_eq_mul, map_mul]

theorem polynomialCoefficientEquiv_smul (σ : K ≃+* K) (c : K) (p : K[X]) :
    Polynomial.mapEquiv σ (c • p) = σ c • Polynomial.mapEquiv σ p := by
  ext n
  simp only [polynomialCoefficientEquiv_coeff, Polynomial.coeff_smul,
    smul_eq_mul, map_mul]

theorem matching_mapCoefficients (σ : K ≃+* K) (d : ℤ) (p q : K[X])
    (h : Matching d p q) :
    Matching d (Polynomial.mapEquiv σ p) (Polynomial.mapEquiv σ q) := by
  have he := congrArg (laurentCoefficientEquiv σ) h
  change laurentCoefficientEquiv σ p.toLaurent =
    laurentCoefficientEquiv σ (LaurentPolynomial.invert q.toLaurent *
      LaurentPolynomial.T d) at he
  simpa only [Matching, map_mul, laurentCoefficientEquiv_toLaurent,
    laurentCoefficientEquiv_invert, laurentCoefficientEquiv_T] using he

theorem matching_mapCoefficients_iff (σ : K ≃+* K) (d : ℤ) (p q : K[X]) :
    Matching d (Polynomial.mapEquiv σ p) (Polynomial.mapEquiv σ q) ↔
      Matching d p q := by
  constructor
  · intro h
    have he := matching_mapCoefficients σ.symm d _ _ h
    have hp : Polynomial.mapEquiv σ.symm (Polynomial.mapEquiv σ p) = p := by
      ext n
      simp only [polynomialCoefficientEquiv_coeff, RingEquiv.symm_apply_apply]
    have hq : Polynomial.mapEquiv σ.symm (Polynomial.mapEquiv σ q) = q := by
      ext n
      simp only [polynomialCoefficientEquiv_coeff, RingEquiv.symm_apply_apply]
    simpa only [hp, hq] using he
  · exact matching_mapCoefficients σ d p q

/-- The coordinate change is additive and semilinear with respect to `σ`. -/
def matchingCoefficientEquiv (σ : K ≃+* K) (d : ℤ) :
    matchingSpace (K := K) d ≃+ matchingSpace (K := K) d where
  toFun s := ⟨(Polynomial.mapEquiv σ s.val.1, Polynomial.mapEquiv σ s.val.2),
    matching_mapCoefficients σ d _ _ s.property⟩
  invFun s := ⟨(Polynomial.mapEquiv σ.symm s.val.1, Polynomial.mapEquiv σ.symm s.val.2),
    matching_mapCoefficients σ.symm d _ _ s.property⟩
  left_inv s := by
    apply Subtype.ext
    apply Prod.ext <;> ext n <;>
      simp only [polynomialCoefficientEquiv_coeff, RingEquiv.symm_apply_apply]
  right_inv s := by
    apply Subtype.ext
    apply Prod.ext <;> ext n <;>
      simp only [polynomialCoefficientEquiv_coeff, RingEquiv.apply_symm_apply]
  map_add' s t := by
    apply Subtype.ext
    apply Prod.ext <;> exact map_add (Polynomial.mapEquiv σ) _ _

@[simp]
theorem matchingCoefficientEquiv_fst (σ : K ≃+* K) (d : ℤ)
    (s : matchingSpace (K := K) d) :
    (matchingCoefficientEquiv σ d s).val.1 = Polynomial.mapEquiv σ s.val.1 := rfl

@[simp]
theorem matchingCoefficientEquiv_snd (σ : K ≃+* K) (d : ℤ)
    (s : matchingSpace (K := K) d) :
    (matchingCoefficientEquiv σ d s).val.2 = Polynomial.mapEquiv σ s.val.2 := rfl

theorem matchingCoefficientEquiv_smul (σ : K ≃+* K) (d : ℤ)
    (c : K) (s : matchingSpace (K := K) d) :
    matchingCoefficientEquiv σ d (c • s) = σ c • matchingCoefficientEquiv σ d s := by
  apply Subtype.ext
  apply Prod.ext <;> exact polynomialCoefficientEquiv_smul σ c _

/-- The coefficient change commutes with the actual two-chart differential. -/
theorem cechDifference_mapCoefficients (σ : K ≃+* K) (d : ℤ) (pq : K[X] × K[X]) :
    cechDifference d (Polynomial.mapEquiv σ pq.1, Polynomial.mapEquiv σ pq.2) =
      laurentCoefficientEquiv σ (cechDifference d pq) := by
  change (Polynomial.mapEquiv σ pq.1).toLaurent -
      LaurentPolynomial.invert (Polynomial.mapEquiv σ pq.2).toLaurent *
        LaurentPolynomial.T d =
    laurentCoefficientEquiv σ (pq.1.toLaurent -
      LaurentPolynomial.invert pq.2.toLaurent * LaurentPolynomial.T d)
  rw [map_sub, map_mul, laurentCoefficientEquiv_toLaurent,
    laurentCoefficientEquiv_invert, laurentCoefficientEquiv_toLaurent,
    laurentCoefficientEquiv_T]

theorem cechNormalForm_mapCoefficients (σ : K ≃+* K) (d : ℤ) (f : K[T;T⁻¹]) :
    cechNormalForm d (laurentCoefficientEquiv σ f) =
      laurentCoefficientEquiv σ (cechNormalForm d f) := by
  apply LaurentPolynomial.ext
  intro n
  by_cases hn : d < n ∧ n < 0 <;>
    simp [cechNormalForm_coeff, laurentCoefficientEquiv_coeff, hn]

theorem gapProjection_mapCoefficients (σ : K ≃+* K) (d : ℤ) (f : K[T;T⁻¹]) :
    gapProjection d (laurentCoefficientEquiv σ f) =
      fun i => σ (gapProjection d f i) := by
  funext i
  exact laurentCoefficientEquiv_coeff σ f _

theorem mem_cechRange_mapCoefficients_iff (σ : K ≃+* K) (d : ℤ)
    (f : K[T;T⁻¹]) :
    laurentCoefficientEquiv σ f ∈ LinearMap.range (cechDifference d) ↔
      f ∈ LinearMap.range (cechDifference d) := by
  rw [mem_cechRange_iff_normalForm_zero, mem_cechRange_iff_normalForm_zero,
    cechNormalForm_mapCoefficients]
  exact (laurentCoefficientEquiv σ).map_eq_zero_iff

/-- Correct semilinear raw coordinates by applying the inverse coefficient
automorphism. The scalar law is an explicit obligation of the geometric map. -/
def untwistMatchingCoordinates {V : Type*} [AddCommGroup V] [Module K V]
    (σ : K ≃+* K) (d : ℤ) (raw : V ≃+ matchingSpace (K := K) d)
    (hraw : ∀ (c : K) (s : V), raw (c • s) = σ c • raw s) :
    V ≃ₗ[K] matchingSpace (K := K) d where
  toAddEquiv := raw.trans (matchingCoefficientEquiv σ.symm d)
  map_smul' c s := by
    change matchingCoefficientEquiv σ.symm d (raw (c • s)) =
      c • matchingCoefficientEquiv σ.symm d (raw s)
    rw [hraw, matchingCoefficientEquiv_smul, RingEquiv.symm_apply_apply]

/-- Once the actual scalar law is proved, dimensions transfer without a
canonical-base assumption. This theorem does not construct `raw` or `hraw`. -/
theorem finrank_of_semilinearMatchingCoordinates {V : Type*}
    [AddCommGroup V] [Module K V] (σ : K ≃+* K) (d : ℤ)
    (raw : V ≃+ matchingSpace (K := K) d)
    (hraw : ∀ (c : K) (s : V), raw (c • s) = σ c • raw s) :
    Module.finrank K V = (d + 1).toNat := by
  rw [(untwistMatchingCoordinates σ d raw hraw).finrank_eq]
  exact matchingSpace_finrank_all d

theorem polynomialCoefficientEquiv_eval (σ : K ≃+* K) (p : K[X]) (x : K) :
    (Polynomial.mapEquiv σ p).eval (σ x) = σ (p.eval x) := by
  change (p.map σ.toRingHom).eval (σ.toRingHom x) = σ.toRingHom (p.eval x)
  exact Polynomial.eval_map_apply _ _

/-- Finite point coordinates change by the same automorphism as coefficients. -/
theorem finitePointEvaluation_mapCoefficients (σ : K ≃+* K) (d : ℤ) (x : K)
    (s : matchingSpace (K := K) d) :
    finitePointEvaluation d (σ x) (matchingCoefficientEquiv σ d s) =
      σ (finitePointEvaluation d x s) :=
  polynomialCoefficientEquiv_eval σ s.val.1 x

theorem markedEvaluation_mapCoefficients (σ : K ≃+* K) (d : ℤ)
    (s : matchingSpace (K := K) d) :
    markedEvaluation d (matchingCoefficientEquiv σ d s) =
      (σ (markedEvaluation d s).1, σ (markedEvaluation d s).2) := by
  apply Prod.ext
  · change (Polynomial.mapEquiv σ s.val.1).eval 0 = σ (s.val.1.eval 0)
    simpa only [map_zero] using polynomialCoefficientEquiv_eval σ s.val.1 0
  · change (Polynomial.mapEquiv σ s.val.2).eval 0 = σ (s.val.2.eval 0)
    simpa only [map_zero] using polynomialCoefficientEquiv_eval σ s.val.2 0

end LeBrunSalamon.P1Overlap

end
/- END UNCOMPILED continuation coefficient_transport.lean.txt -/


/- BEGIN UNCOMPILED continuation cech_sections.lean.txt -/
/-!
Two-chart sections of actual module sheaves.

Source continuation, deliberately not compiled in this run. The constructions
below use the actual sheaf condition. Polynomial/Laurent coordinates enter only
through explicitly supplied additive equivalences and their restriction
equations. No existence of those coordinate equations is postulated.

Integration: after the current P1Overlap and P1Ideal local-Hom/gluing APIs,
before PhaseThirtyTwo. No dependencies on the new twist-frame continuation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.TwoChartSections

/-- Restriction of actual sections, retaining its additive structure. -/
def restrictValue {X : Scheme} (E : OModule X) {U V : X.Opens}
    (h : U ≤ V) : SectionsOn E V →+ SectionsOn E U :=
  (E.presheaf.map (homOfLE h).op).hom

@[simp]
theorem restrictValue_refl {X : Scheme} (E : OModule X) (U : X.Opens)
    (s : SectionsOn E U) : restrictValue E (le_refl U) s = s := by
  change E.presheaf.map (𝟙 (op U)) s = s
  simp

@[simp]
theorem restrictValue_comp {X : Scheme} (E : OModule X) {U V W : X.Opens}
    (hUV : U ≤ V) (hVW : V ≤ W) (s : SectionsOn E W) :
    restrictValue E hUV (restrictValue E hVW s) =
      restrictValue E (hUV.trans hVW) s := by
  change E.presheaf.map (homOfLE hUV).op
      (E.presheaf.map (homOfLE hVW).op s) =
    E.presheaf.map (homOfLE (hUV.trans hVW)).op s
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction commutes with an actual module-sheaf morphism. -/
theorem restrictValue_map {X : Scheme} {E F : OModule X}
    (f : E ⟶ F) {U V : X.Opens} (h : U ≤ V) (s : SectionsOn E V) :
    restrictValue F h (f.app V s) = f.app U (restrictValue E h s) :=
  sheafHom_naturality f (homOfLE h) s

/-- The additive sheaf underlying the given module sheaf. -/
def sectionSheaf {X : Scheme} (E : OModule X) : TopCat.Sheaf AddCommGrpCat X :=
  ⟨E.presheaf, E.isSheaf⟩

/-- Compatibility is equality on the entire intersection of the two opens. -/
def PairCompatible {X : Scheme} (E : OModule X) (U V : X.Opens)
    (s : SectionsOn E U) (t : SectionsOn E V) : Prop :=
  restrictValue E (inf_le_left : U ⊓ V ≤ U) s =
    restrictValue E (inf_le_right : U ⊓ V ≤ V) t

/-- Reverse an overlap equation with an explicit restriction through
`V ∩ U = U ∩ V`, avoiding an implicit dependent rewrite of section types. -/
theorem pairCompatible_symm {X : Scheme} {E : OModule X} {U V : X.Opens}
    {s : SectionsOn E U} {t : SectionsOn E V} (h : PairCompatible E U V s t) :
    PairCompatible E V U t s := by
  have he := congrArg
    (restrictValue E (le_of_eq (inf_comm V U))) h.symm
  simpa only [PairCompatible, restrictValue_comp] using he

/-- The two-open equalizer as an actual additive subgroup of local sections. -/
def matchingPairs {X : Scheme} (E : OModule X) (U V : X.Opens) :
    AddSubgroup (SectionsOn E U × SectionsOn E V) where
  carrier := {st | PairCompatible E U V st.1 st.2}
  zero_mem' := by simp [PairCompatible]
  add_mem' := by
    intro a b ha hb
    change restrictValue E (inf_le_left : U ⊓ V ≤ U) (a.1 + b.1) =
      restrictValue E (inf_le_right : U ⊓ V ≤ V) (a.2 + b.2)
    rw [map_add, map_add, ha, hb]
  neg_mem' := by
    intro a ha
    change restrictValue E (inf_le_left : U ⊓ V ≤ U) (-a.1) =
      restrictValue E (inf_le_right : U ⊓ V ≤ V) (-a.2)
    rw [map_neg, map_neg, ha]

@[simp]
theorem mem_matchingPairs {X : Scheme} (E : OModule X) (U V : X.Opens)
    (s : SectionsOn E U) (t : SectionsOn E V) :
    (s, t) ∈ matchingPairs E U V ↔ PairCompatible E U V s t := Iff.rfl

/-- The actual degree-zero Cech differential, before any coordinate choices. -/
def pairDifference {X : Scheme} (E : OModule X) (U V : X.Opens) :
    (SectionsOn E U × SectionsOn E V) →+ SectionsOn E (U ⊓ V) where
  toFun st := restrictValue E (inf_le_left : U ⊓ V ≤ U) st.1 -
    restrictValue E (inf_le_right : U ⊓ V ≤ V) st.2
  map_zero' := by simp
  map_add' st ab := by
    change restrictValue E (inf_le_left : U ⊓ V ≤ U) (st.1 + ab.1) -
        restrictValue E (inf_le_right : U ⊓ V ≤ V) (st.2 + ab.2) = _
    rw [map_add, map_add]
    exact (sub_add_sub_comm _ _ _ _).symm

theorem pairDifference_kernel {X : Scheme} (E : OModule X) (U V : X.Opens) :
    (pairDifference E U V).ker = matchingPairs E U V := by
  ext st
  change restrictValue E (inf_le_left : U ⊓ V ≤ U) st.1 -
      restrictValue E (inf_le_right : U ⊓ V ≤ V) st.2 = 0 ↔ _
  exact sub_eq_zero

/-- Restriction from genuine global sections to the two actual opens. -/
def pairRestriction {X : Scheme} (E : OModule X) (U V : X.Opens) :
    GlobalSections E →+ matchingPairs E U V where
  toFun s := ⟨(restrictValue E le_top s, restrictValue E le_top s), by
    change restrictValue E (inf_le_left : U ⊓ V ≤ U)
        (restrictValue E le_top s) =
      restrictValue E (inf_le_right : U ⊓ V ≤ V)
        (restrictValue E le_top s)
    simp only [restrictValue_comp]⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' s t := by apply Subtype.ext; simp

@[simp]
theorem pairRestriction_fst {X : Scheme} (E : OModule X) (U V : X.Opens)
    (s : GlobalSections E) :
    (pairRestriction E U V s).val.1 = restrictValue E (show U ≤ ⊤ from le_top) s := rfl

@[simp]
theorem pairRestriction_snd {X : Scheme} (E : OModule X) (U V : X.Opens)
    (s : GlobalSections E) :
    (pairRestriction E U V s).val.2 = restrictValue E (show V ≤ ⊤ from le_top) s := rfl

/-- A covering pair detects equality of actual global sections. -/
theorem globalSection_ext {X : Scheme} (E : OModule X) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (s t : GlobalSections E)
    (hU : restrictValue E (show U ≤ ⊤ from le_top) s =
      restrictValue E (show U ≤ ⊤ from le_top) t)
    (hV : restrictValue E (show V ≤ ⊤ from le_top) s =
      restrictValue E (show V ≤ ⊤ from le_top) t) : s = t := by
  exact (sectionSheaf E).eq_of_locally_eq₂
    (homOfLE (show U ≤ ⊤ from le_top))
    (homOfLE (show V ≤ ⊤ from le_top)) (by rw [hcover]) s t hU hV

theorem pairRestriction_injective {X : Scheme} (E : OModule X) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) : Function.Injective (pairRestriction E U V) := by
  intro s t h
  exact globalSection_ext E U V hcover s t
    (congrArg (fun a : matchingPairs E U V => a.val.1) h)
    (congrArg (fun a : matchingPairs E U V => a.val.2) h)

/-- Compatible sections on two covering opens have a unique actual global gluing. -/
theorem existsUnique_pairGluing {X : Scheme} (E : OModule X) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (s : SectionsOn E U) (t : SectionsOn E V)
    (h : PairCompatible E U V s t) :
    ∃! a : GlobalSections E,
      restrictValue E (show U ≤ ⊤ from le_top) a = s ∧
        restrictValue E (show V ≤ ⊤ from le_top) a = t := by
  let O : Fin 2 → X.Opens := Fin.cases U (fun _ => V)
  let sf : ∀ i, SectionsOn E (O i) := Fin.cases s (fun _ => t)
  have hc : (⊤ : X.Opens) ≤ iSup O := by
    rw [← hcover]
    exact sup_le (le_iSup O 0) (le_iSup O 1)
  have hs : TopCat.Presheaf.IsCompatible E.presheaf O sf := by
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact h
    · exact pairCompatible_symm h
    · rfl
  obtain ⟨a, ha, _⟩ := (sectionSheaf E).existsUnique_gluing' O ⊤
    (fun i => homOfLE (show O i ≤ ⊤ from le_top)) hc sf hs
  refine ⟨a, ⟨ha 0, ha 1⟩, ?_⟩
  intro b hb
  exact globalSection_ext E U V hcover b a
    (hb.1.trans (ha 0).symm) (hb.2.trans (ha 1).symm)

theorem pairRestriction_surjective {X : Scheme} (E : OModule X) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) : Function.Surjective (pairRestriction E U V) := by
  intro st
  obtain ⟨a, ha, _⟩ := existsUnique_pairGluing E U V hcover
    st.val.1 st.val.2 st.property
  refine ⟨a, ?_⟩
  apply Subtype.ext
  exact Prod.ext ha.1 ha.2

/-- The actual sheaf condition gives an additive equalizer equivalence. -/
def pairRestrictionEquiv {X : Scheme} (E : OModule X) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) : GlobalSections E ≃+ matchingPairs E U V :=
  AddEquiv.ofBijective (pairRestriction E U V)
    ⟨pairRestriction_injective E U V hcover,
      pairRestriction_surjective E U V hcover⟩

/-- Gluing is the inverse of restriction, so its additivity is not a new assumption. -/
def gluePair {X : Scheme} (E : OModule X) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) : matchingPairs E U V →+ GlobalSections E :=
  (pairRestrictionEquiv E U V hcover).symm.toAddMonoidHom

@[simp]
theorem restrict_gluePair {X : Scheme} (E : OModule X) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (st : matchingPairs E U V) :
    pairRestriction E U V (gluePair E U V hcover st) = st :=
  (pairRestrictionEquiv E U V hcover).apply_symm_apply st

@[simp]
theorem gluePair_restrict {X : Scheme} (E : OModule X) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (s : GlobalSections E) :
    gluePair E U V hcover (pairRestriction E U V s) = s :=
  (pairRestrictionEquiv E U V hcover).symm_apply_apply s

@[simp]
theorem gluePair_fst {X : Scheme} (E : OModule X) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (st : matchingPairs E U V) :
    restrictValue E (show U ≤ ⊤ from le_top) (gluePair E U V hcover st) = st.val.1 :=
  congrArg (fun a : matchingPairs E U V => a.val.1) (restrict_gluePair E U V hcover st)

@[simp]
theorem gluePair_snd {X : Scheme} (E : OModule X) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (st : matchingPairs E U V) :
    restrictValue E (show V ≤ ⊤ from le_top) (gluePair E U V hcover st) = st.val.2 :=
  congrArg (fun a : matchingPairs E U V => a.val.2) (restrict_gluePair E U V hcover st)

/-- The equalizer comparison for the project's original `O_X → E` sections. -/
def algebraicSectionsEquiv {X : Scheme} (E : OModule X) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) : AlgebraicSection E ≃+ matchingPairs E U V :=
  (sectionAddEquiv E).trans (pairRestrictionEquiv E U V hcover)

theorem algebraicSection_eq_zero_iff {X : Scheme} (E : OModule X) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (s : AlgebraicSection E) :
    s = 0 ↔
      restrictValue E (show U ≤ ⊤ from le_top) (sectionValue s) = 0 ∧
        restrictValue E (show V ≤ ⊤ from le_top) (sectionValue s) = 0 := by
  constructor
  · rintro rfl
    simp
  · intro hs
    apply (sectionValue_bijective E).injective
    apply globalSection_ext E U V hcover
    · simpa using hs.1
    · simpa using hs.2

/-- A sheaf morphism acts on compatible local values, not just on global sections. -/
def mapMatchingPairs {X : Scheme} {E F : OModule X} (f : E ⟶ F) (U V : X.Opens) :
    matchingPairs E U V →+ matchingPairs F U V where
  toFun st := ⟨(f.app U st.val.1, f.app V st.val.2), by
    change restrictValue F (inf_le_left : U ⊓ V ≤ U) (f.app U st.val.1) =
      restrictValue F (inf_le_right : U ⊓ V ≤ V) (f.app V st.val.2)
    rw [restrictValue_map, restrictValue_map, st.property]⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' s t := by apply Subtype.ext; simp

theorem pairRestriction_naturality {X : Scheme} {E F : OModule X}
    (f : E ⟶ F) (U V : X.Opens) (s : GlobalSections E) :
    pairRestriction F U V (f.app ⊤ s) =
      mapMatchingPairs f U V (pairRestriction E U V s) := by
  apply Subtype.ext
  apply Prod.ext <;> exact restrictValue_map f le_top s

/-- Gluing commutes with actual module-sheaf maps. -/
theorem gluePair_naturality {X : Scheme} {E F : OModule X}
    (f : E ⟶ F) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (st : matchingPairs E U V) :
    f.app ⊤ (gluePair E U V hcover st) =
      gluePair F U V hcover (mapMatchingPairs f U V st) := by
  apply pairRestriction_injective F U V hcover
  rw [pairRestriction_naturality, restrict_gluePair, restrict_gluePair]

/-- The whole-space restriction has image exactly the actual Cech kernel. -/
theorem localPair_glues_iff {X : Scheme} (E : OModule X) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (st : SectionsOn E U × SectionsOn E V) :
    (∃ a : GlobalSections E,
      restrictValue E (show U ≤ ⊤ from le_top) a = st.1 ∧
        restrictValue E (show V ≤ ⊤ from le_top) a = st.2) ↔
      pairDifference E U V st = 0 := by
  constructor
  · rintro ⟨a, ha, hb⟩
    change restrictValue E (inf_le_left : U ⊓ V ≤ U) st.1 -
      restrictValue E (inf_le_right : U ⊓ V ≤ V) st.2 = 0
    rw [← ha, ← hb, restrictValue_comp, restrictValue_comp, sub_self]
  · intro h
    have hc : PairCompatible E U V st.1 st.2 := sub_eq_zero.mp h
    exact (existsUnique_pairGluing E U V hcover st.1 st.2 hc).exists

/-- Two local choices with the same Cech difference differ by a unique
genuine global section. This is the ambiguity in a primitive, expressed
before any chart coordinates are selected. -/
theorem existsUnique_differenceGluing {X : Scheme} (E : OModule X) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (st ab : SectionsOn E U × SectionsOn E V)
    (h : pairDifference E U V st = pairDifference E U V ab) :
    ∃! s : GlobalSections E,
      restrictValue E (show U ≤ ⊤ from le_top) s = st.1 - ab.1 ∧
        restrictValue E (show V ≤ ⊤ from le_top) s = st.2 - ab.2 := by
  have hz : pairDifference E U V (st - ab) = 0 := by
    rw [map_sub, h, sub_self]
  have hc : PairCompatible E U V (st.1 - ab.1) (st.2 - ab.2) :=
    sub_eq_zero.mp hz
  exact existsUnique_pairGluing E U V hcover _ _ hc

/-- Adding the restrictions of a global section does not change a local
primitive's difference on the overlap. -/
theorem pairDifference_add_global {X : Scheme} (E : OModule X) (U V : X.Opens)
    (st : SectionsOn E U × SectionsOn E V) (s : GlobalSections E) :
    pairDifference E U V
        (st + (pairRestriction E U V s).val) = pairDifference E U V st := by
  rw [map_add]
  have hz : pairDifference E U V (pairRestriction E U V s).val = 0 :=
    sub_eq_zero.mpr (pairRestriction E U V s).property
  rw [hz, add_zero]

/-- The solution fiber of the actual two-open differential. -/
def Primitive {X : Scheme} (E : OModule X) (U V : X.Opens)
    (w : SectionsOn E (U ⊓ V)) :=
  {st : SectionsOn E U × SectionsOn E V // pairDifference E U V st = w}

/-- Relative to one primitive, all other primitives are parametrized by
genuine global sections. This is an affine equivalence, not an arbitrary
choice of an additive structure on a nonzero fiber. -/
def primitiveEquiv {X : Scheme} (E : OModule X) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (w : SectionsOn E (U ⊓ V))
    (p : Primitive E U V w) : GlobalSections E ≃ Primitive E U V w where
  toFun s := ⟨p.val + (pairRestriction E U V s).val, by
    rw [pairDifference_add_global, p.property]⟩
  invFun q := gluePair E U V hcover ⟨q.val - p.val, by
    have hz : pairDifference E U V (q.val - p.val) = 0 := by
      rw [map_sub, q.property, p.property, sub_self]
    exact sub_eq_zero.mp hz⟩
  left_inv s := by
    apply pairRestriction_injective E U V hcover
    rw [restrict_gluePair]
    apply Subtype.ext
    change p.val + (pairRestriction E U V s).val - p.val =
      (pairRestriction E U V s).val
    abel
  right_inv q := by
    apply Subtype.ext
    change p.val + (pairRestriction E U V (gluePair E U V hcover _)).val = q.val
    rw [restrict_gluePair]
    change p.val + (q.val - p.val) = q.val
    abel

section LaurentCoordinates

open Polynomial
open scoped LaurentPolynomial

variable {K : Type*} [Field K]
variable {X : Scheme} (E : OModule X) (U V : X.Opens) (d : ℤ)
variable (cU : SectionsOn E U ≃+ K[X])
variable (cV : SectionsOn E V ≃+ K[X])
variable (cW : SectionsOn E (U ⊓ V) ≃+ K[T;T⁻¹])
variable (hU : ∀ s : SectionsOn E U,
  cW (restrictValue E (inf_le_left : U ⊓ V ≤ U) s) = (cU s).toLaurent)
variable (hV : ∀ s : SectionsOn E V,
  cW (restrictValue E (inf_le_right : U ⊓ V ≤ V) s) =
    LaurentPolynomial.invert (cV s).toLaurent * LaurentPolynomial.T d)

include hU hV

/-- Actual compatibility becomes Laurent matching when the two restriction
formulas are proved for the specified coordinate maps. -/
theorem compatible_iff_laurent (s : SectionsOn E U) (t : SectionsOn E V) :
    PairCompatible E U V s t ↔ P1Overlap.Matching d (cU s) (cV t) := by
  constructor
  · intro h
    exact (hU s).symm.trans ((congrArg cW h).trans (hV t))
  · intro h
    apply cW.injective
    rw [hU, hV]
    exact h

/-- Conjugating the actual two-open difference gives the existing Laurent
Cech difference, including the sign and the exponent of its second term. -/
theorem difference_coordinates (st : SectionsOn E U × SectionsOn E V) :
    cW (pairDifference E U V st) =
      P1Overlap.cechDifference d (cU st.1, cV st.2) := by
  change cW (restrictValue E (inf_le_left : U ⊓ V ≤ U) st.1 -
    restrictValue E (inf_le_right : U ⊓ V ≤ V) st.2) = _
  rw [map_sub, hU, hV]
  rfl

/-- Coordinate change identifies the actual equalizer with the computed
Laurent matching group. This theorem supplies no unproved coordinate data. -/
def laurentPairEquiv :
    matchingPairs E U V ≃+ P1Overlap.matchingSpace (K := K) d where
  toFun st := ⟨(cU st.val.1, cV st.val.2),
    (compatible_iff_laurent E U V d cU cV cW hU hV _ _).mp st.property⟩
  invFun pq := ⟨(cU.symm pq.val.1, cV.symm pq.val.2), by
    apply (compatible_iff_laurent E U V d cU cV cW hU hV _ _).mpr
    have hpq : P1Overlap.Matching d pq.val.1 pq.val.2 := pq.property
    simpa only [AddEquiv.apply_symm_apply] using hpq⟩
  left_inv st := by
    apply Subtype.ext
    exact Prod.ext (cU.symm_apply_apply st.val.1) (cV.symm_apply_apply st.val.2)
  right_inv pq := by
    apply Subtype.ext
    exact Prod.ext (cU.apply_symm_apply pq.val.1) (cV.apply_symm_apply pq.val.2)
  map_add' st ab := by
    apply Subtype.ext
    exact Prod.ext (cU.map_add st.val.1 ab.val.1) (cV.map_add st.val.2 ab.val.2)

/-- The additive comparison from genuine algebraic sections to Laurent pairs.
For a noncanonical complex base identification this is intentionally additive;
linearity requires the corresponding coefficient automorphism. -/
def algebraicSectionsLaurentEquiv (hcover : U ⊔ V = ⊤) :
    AlgebraicSection E ≃+ P1Overlap.matchingSpace (K := K) d :=
  (algebraicSectionsEquiv E U V hcover).trans
    (laurentPairEquiv E U V d cU cV cW hU hV)

@[simp]
theorem algebraicSectionsLaurentEquiv_fst (hcover : U ⊔ V = ⊤)
    (s : AlgebraicSection E) :
    (algebraicSectionsLaurentEquiv E U V d cU cV cW hU hV hcover s).val.1 =
      cU (restrictValue E (show U ≤ ⊤ from le_top) (sectionValue s)) := rfl

@[simp]
theorem algebraicSectionsLaurentEquiv_snd (hcover : U ⊔ V = ⊤)
    (s : AlgebraicSection E) :
    (algebraicSectionsLaurentEquiv E U V d cU cV cW hU hV hcover s).val.2 =
      cV (restrictValue E (show V ≤ ⊤ from le_top) (sectionValue s)) := rfl

/-- A matching polynomial pair determines a unique original algebraic section,
once actual local coordinates and their transition have been constructed. -/
theorem existsUnique_section_of_laurent (hcover : U ⊔ V = ⊤)
    (pq : P1Overlap.matchingSpace (K := K) d) :
    ∃! s : AlgebraicSection E,
      cU (restrictValue E (show U ≤ ⊤ from le_top) (sectionValue s)) = pq.val.1 ∧
        cV (restrictValue E (show V ≤ ⊤ from le_top) (sectionValue s)) = pq.val.2 := by
  let e := algebraicSectionsLaurentEquiv E U V d cU cV cW hU hV hcover
  refine ⟨e.symm pq, ?_, ?_⟩
  · have he := e.apply_symm_apply pq
    exact ⟨congrArg (fun a : P1Overlap.matchingSpace (K := K) d => a.val.1) he,
      congrArg (fun a : P1Overlap.matchingSpace (K := K) d => a.val.2) he⟩
  · intro s hs
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    exact Prod.ext hs.1 hs.2

/-- Negative twists have no sections as soon as the genuine restriction
coordinates are available. The remaining geometric input is explicit. -/
theorem algebraicSection_eq_zero_of_negative_coordinates
    (hcover : U ⊔ V = ⊤) (hd : d < 0) (s : AlgebraicSection E) : s = 0 := by
  letI := P1Overlap.matchingSpace_subsingleton_of_negative (K := K) hd
  apply (algebraicSectionsLaurentEquiv E U V d cU cV cW hU hV hcover).injective
  exact Subsingleton.elim _ _

/-- Surjectivity of the actual additive Cech differential is transported by
the explicit coordinates; this is not a statement about Yoneda Ext yet. -/
theorem pairDifference_surjective_iff_laurent :
    Function.Surjective (pairDifference E U V) ↔ -1 ≤ d := by
  rw [← P1Overlap.cechDifference_surjective_iff (K := K) d]
  constructor
  · intro hs f
    obtain ⟨st, hst⟩ := hs (cW.symm f)
    refine ⟨(cU st.1, cV st.2), ?_⟩
    rw [← difference_coordinates E U V d cU cV cW hU hV, hst,
      AddEquiv.apply_symm_apply]
  · intro hs w
    obtain ⟨pq, hpq⟩ := hs (cW w)
    refine ⟨(cU.symm pq.1, cV.symm pq.2), ?_⟩
    apply cW.injective
    rw [difference_coordinates E U V d cU cV cW hU hV]
    simpa only [AddEquiv.apply_symm_apply] using hpq

/-- Missing Laurent coefficients are precisely the obstruction to solving
an actual two-open difference equation under the specified coordinates.
No identification with an Ext group is asserted here. -/
theorem primitive_exists_iff_gap_zero (w : SectionsOn E (U ⊓ V)) :
    Nonempty (Primitive E U V w) ↔ P1Overlap.gapProjection d (cW w) = 0 := by
  constructor
  · rintro ⟨p⟩
    have hc : cW w ∈ LinearMap.range (P1Overlap.cechDifference (K := K) d) := by
      refine ⟨(cU p.val.1, cV p.val.2), ?_⟩
      rw [← difference_coordinates E U V d cU cV cW hU hV, p.property]
    rw [← P1Overlap.gapProjection_kernel] at hc
    exact hc
  · intro h
    have hc : cW w ∈ LinearMap.range (P1Overlap.cechDifference (K := K) d) := by
      rw [← P1Overlap.gapProjection_kernel]
      exact h
    obtain ⟨pq, hpq⟩ := hc
    refine ⟨⟨(cU.symm pq.1, cV.symm pq.2), ?_⟩⟩
    apply cW.injective
    rw [difference_coordinates E U V d cU cV cW hU hV]
    simpa only [AddEquiv.apply_symm_apply] using hpq

/-- A local change of primitive leaves the gap obstruction unchanged. -/
theorem gap_obstruction_add_difference (w : SectionsOn E (U ⊓ V))
    (st : SectionsOn E U × SectionsOn E V) :
    P1Overlap.gapProjection d (cW (w + pairDifference E U V st)) =
      P1Overlap.gapProjection d (cW w) := by
  have hz : P1Overlap.gapProjection d (cW (pairDifference E U V st)) = 0 :=
    (primitive_exists_iff_gap_zero E U V d cU cV cW hU hV _).mp ⟨⟨st, rfl⟩⟩
  rw [map_add, map_add, hz, add_zero]

end LaurentCoordinates

/-- A genuine sheaf isomorphism transports algebraic sections additively. -/
def algebraicSectionIso {X : Scheme} {E F : OModule X} (e : E ≅ F) :
    AlgebraicSection E ≃+ AlgebraicSection F where
  toFun s := s ≫ e.hom
  invFun t := t ≫ e.inv
  left_inv s := by simp
  right_inv t := by simp
  map_add' s t := by simp only [Preadditive.add_comp]

/-- The analogous additive equivalence on whole-open section values. -/
def globalSectionIso {X : Scheme} {E F : OModule X} (e : E ≅ F) :
    GlobalSections E ≃+ GlobalSections F where
  toFun s := e.hom.app ⊤ s
  invFun t := e.inv.app ⊤ t
  left_inv s := by
    change (e.hom ≫ e.inv).app ⊤ s = s
    simp
  right_inv t := by
    change (e.inv ≫ e.hom).app ⊤ t = t
    simp
  map_add' s t := map_add (e.hom.app ⊤).hom s t

/-- The already constructed whole-space local-Hom equivalence is additive. -/
def topLocalHomAddEquiv {X : Scheme} (E F : OModule X) :
    HomConstruction.Section E F ⊤ ≃+ (E ⟶ F) where
  toEquiv := P1Ideal.topSectionHomEquiv E F
  map_add' φ ψ := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl

/-- Global sections of the original chosen internal Hom are actual sheaf
morphisms. The comparison uses its proved isomorphism with local Hom. -/
def internalHomSectionAddEquiv {X : Scheme} (E F : OModule X) :
    AlgebraicSection (internalHomSheaf E F) ≃+ (E ⟶ F) :=
  (sectionAddEquiv (internalHomSheaf E F)).trans
    ((globalSectionIso (internalHomConstructionIso E F)).trans
      (topLocalHomAddEquiv E F))

/-- The section of internal Hom corresponding to a specified genuine morphism. -/
def homSection {X : Scheme} {E F : OModule X} (f : E ⟶ F) :
    AlgebraicSection (internalHomSheaf E F) :=
  (internalHomSectionAddEquiv E F).symm f

@[simp]
theorem internalHomSectionAddEquiv_homSection {X : Scheme} {E F : OModule X}
    (f : E ⟶ F) : internalHomSectionAddEquiv E F (homSection f) = f :=
  (internalHomSectionAddEquiv E F).apply_symm_apply f

@[simp]
theorem homSection_internalHomSectionAddEquiv {X : Scheme} {E F : OModule X}
    (s : AlgebraicSection (internalHomSheaf E F)) :
    homSection (internalHomSectionAddEquiv E F s) = s :=
  (internalHomSectionAddEquiv E F).symm_apply_apply s

/-- After the proved comparison with genuine local Hom, the global value
of `homSection f` is exactly restriction of `f` to every subopen. -/
theorem homSection_localHomValue {X : Scheme} {E F : OModule X} (f : E ⟶ F) :
    (internalHomConstructionIso E F).hom.app ⊤ (sectionValue (homSection f)) =
      P1Ideal.localSectionOfHom f ⊤ := by
  apply (P1Ideal.topSectionHomEquiv E F).injective
  have h := internalHomSectionAddEquiv_homSection f
  change P1Ideal.homOfTopSection
    ((internalHomConstructionIso E F).hom.app ⊤ (sectionValue (homSection f))) = f at h
  exact h.trans (P1Ideal.homOfTopSection_localSection f).symm

@[simp]
theorem homSection_zero {X : Scheme} (E F : OModule X) :
    homSection (0 : E ⟶ F) = 0 :=
  (internalHomSectionAddEquiv E F).symm.map_zero

@[simp]
theorem homSection_add {X : Scheme} {E F : OModule X} (f g : E ⟶ F) :
    homSection (f + g) = homSection f + homSection g :=
  (internalHomSectionAddEquiv E F).symm.map_add f g

theorem homSection_eq_zero_iff {X : Scheme} {E F : OModule X} (f : E ⟶ F) :
    homSection f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have hh := congrArg (internalHomSectionAddEquiv E F) h
    simpa only [internalHomSectionAddEquiv_homSection, map_zero] using hh
  · rintro rfl
    exact homSection_zero E F

/-- Vanishing of sections of a genuine internal Hom forces vanishing of every
sheaf morphism. An arbitrary isomorphic model may be used for the section calculation. -/
theorem hom_eq_zero_of_section_vanishing {X : Scheme} {E F L : OModule X}
    (e : internalHomSheaf E F ≅ L)
    (h : ∀ s : AlgebraicSection L, s = 0) (f : E ⟶ F) : f = 0 := by
  apply (homSection_eq_zero_iff f).mp
  apply (algebraicSectionIso e).injective
  rw [map_zero]
  exact h _

end LeBrunSalamon.TwoChartSections

end
/- END UNCOMPILED continuation cech_sections.lean.txt -/


namespace LeBrunSalamon.PhaseThirtyTwo

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseEighteen
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight

/-- The ideal of the rational point is the kernel O_P1 -> p_*O_C. -/
abbrev projectivePointIdealSheaf (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) : OModule ProjectiveLine :=
  kernel (structurePushforwardMap p.map)

set_option backward.isDefEq.respectTransparency false in
theorem projectivePointIdeal_rankOne (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) :
    IsLocallyFreeOfRank (projectivePointIdealSheaf P p) 1 := by
  let q := ProjectiveLinePoint.rebase Skeleton.canonicalProjectiveLine p
  have hq : IsLocallyFreeOfRank (kernel (structurePushforwardMap q.map)) 1 :=
    P1Ideal.canonicalPointIdeal_rankOne q.map q.overC
  exact locallyFreeOfRank_iso
    (P1Restriction.structureKernel_precomposeIso
      (Skeleton.canonicalProjectiveLine.zeroDegreeIso.symm ≪≫ P.zeroDegreeIso) p.map) hq

def projectiveMinusOneLine (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) : LineBundle ProjectiveLine :=
  ⟨projectivePointIdealSheaf P p, projectivePointIdeal_rankOne P p⟩

def projectiveOneLine (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) : LineBundle ProjectiveLine :=
  dualLine (projectiveMinusOneLine P p)

def projectiveTwist (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) : LineBundle ProjectiveLine :=
  linePowerInt (projectiveOneLine P p) d

set_option backward.isDefEq.respectTransparency false in
theorem projectiveLine_hasPoint (P : ProjectiveLineOverC) :
    Nonempty (ProjectiveLinePoint P) := ⟨ProjectiveLinePoint.rebase P (P1Charts.markedPoint 0 0)⟩

set_option backward.isDefEq.respectTransparency false in
theorem projectiveLine_hasDistinctPoints (P : ProjectiveLineOverC) :
    ∃ p q : ProjectiveLinePoint P, p.map ≠ q.map := by
  refine ⟨ProjectiveLinePoint.rebase P (P1Charts.markedPoint 0 0),
    ProjectiveLinePoint.rebase P (P1Charts.markedPoint 1 0), ?_⟩
  intro h
  exact P1Charts.coordinatePoints_distinct
    ((ProjectiveLinePoint.rebase_map_eq_iff P _ _).mp h)

set_option backward.isDefEq.respectTransparency false in
theorem projectivePointIdeal_independent (P : ProjectiveLineOverC)
    (p q : ProjectiveLinePoint P) :
    Nonempty (projectivePointIdealSheaf P p ≅ projectivePointIdealSheaf P q) := by
  obtain ⟨d⟩ := P1Ideal.projectiveLinePoint_normalizedFrames P p
  obtain ⟨e⟩ := P1Ideal.projectiveLinePoint_normalizedFrames P q
  exact ⟨P1Ideal.normalizedPointIdealIso d e⟩

set_option backward.isDefEq.respectTransparency false in
theorem projectiveOneLine_independent (P : ProjectiveLineOverC)
    (p q : ProjectiveLinePoint P) :
    Nonempty ((projectiveOneLine P p).sheaf ≅ (projectiveOneLine P q).sheaf) := by
  obtain ⟨e⟩ := projectivePointIdeal_independent P p q
  exact ⟨LineBundleClasses.dualCongrIso
    (L := projectiveMinusOneLine P p) (M := projectiveMinusOneLine P q) e⟩

set_option backward.isDefEq.respectTransparency false in
theorem projectiveTwist_independent (P : ProjectiveLineOverC)
    (p q : ProjectiveLinePoint P) (a : ℤ) :
    Nonempty ((projectiveTwist P p a).sheaf ≅ (projectiveTwist P q a).sheaf) := by
  obtain ⟨e⟩ := projectiveOneLine_independent P p q
  exact LineBundleClasses.linePowerInt_congr
    (L := projectiveOneLine P p) (M := projectiveOneLine P q) e a

set_option backward.isDefEq.respectTransparency false in
theorem projectiveTwist_add (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (a b : ℤ) :
    Nonempty ((tensorLine (projectiveTwist P p a) (projectiveTwist P p b)).sheaf ≅
      (projectiveTwist P p (a + b)).sheaf) :=
  LineBundleClasses.linePowerInt_add (projectiveOneLine P p) a b

set_option backward.isDefEq.respectTransparency false in
theorem projectiveTwist_dual (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (a : ℤ) :
    Nonempty ((dualLine (projectiveTwist P p a)).sheaf ≅
      (projectiveTwist P p (-a)).sheaf) :=
  LineBundleClasses.linePowerInt_dual (projectiveOneLine P p) a

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix

open LeBrunSalamon.PhaseTwo

theorem projectiveTwist_internalHom (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (a b : ℤ) :
    Nonempty (internalHomSheaf (projectiveTwist P p a).sheaf
      (projectiveTwist P p b).sheaf ≅ (projectiveTwist P p (b - a)).sheaf) :=
  LineBundleClasses.internalHom_linePowerInt (projectiveOneLine P p) a b

end

end LeBrunSalamon.PhaseThirtyTwo

/- BEGIN UNCOMPILED continuation twist_frames.lean.txt -/
/-!
Actual local frames for the original integer twists.

This continuation is a source draft: it has deliberately not been compiled.
All constructions use existing sheaves and actual isomorphisms.  In particular,
the input to `twistOverFrame` is the existing marked point, not an assumed
trivialization or an assumed splitting theorem.

Insert after the existing PhaseThirtyTwo namespace has closed.  The generic
frame calculus is independent of P1.  The last section constructs polynomial
coordinates on both standard charts for every original O(d).  Identifying the
transition of these *chosen* coordinates with t^d remains a separate task.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix

namespace LeBrunSalamon.LocalFrames

namespace Generic

open HomConstruction.Generic

variable {C : Type} [Category.{0} C] {J : GrothendieckTopology C}
variable {R : Sheaf J CommRingCat}

/-- A specified basis of a rank-one module sheaf on a ringed site. -/
abbrev Frame (E : Modules R) := SheafOfModules.unit (ringSheaf R) ≅ E

/-- A frame identifies the module over each object with its ring of scalars. -/
def coordinates {E : Modules R} (e : Frame E) (U : C) :
    SectionsOn E U ≃ₗ[RingSections R U] RingSections R U where
  toFun x := e.inv.val.app (op U) x
  invFun r := e.hom.val.app (op U) r
  left_inv x := congrArg (fun f : E ⟶ E => f.val.app (op U) x) e.inv_hom_id
  right_inv r := congrArg
    (fun f : SheafOfModules.unit (ringSheaf R) ⟶
      SheafOfModules.unit (ringSheaf R) => f.val.app (op U) r) e.hom_inv_id
  map_add' x y := (e.inv.val.app (op U)).hom.map_add x y
  map_smul' r x := (e.inv.val.app (op U)).hom.map_smul r x

@[simp]
theorem coordinates_apply {E : Modules R} (e : Frame E) (U : C)
    (x : SectionsOn E U) :
    coordinates e U x = e.inv.val.app (op U) x := rfl

@[simp]
theorem coordinates_symm_apply {E : Modules R} (e : Frame E) (U : C)
    (r : RingSections R U) :
    (coordinates e U).symm r = e.hom.val.app (op U) r := rfl

/-- The distinguished local generator is the image of 1. -/
def generator {E : Modules R} (e : Frame E) (U : C) : SectionsOn E U :=
  (coordinates e U).symm 1

@[simp]
theorem coordinates_generator {E : Modules R} (e : Frame E) (U : C) :
    coordinates e U (generator e U) = 1 :=
  (coordinates e U).apply_symm_apply 1

/-- Recover a section by multiplying its coordinate by the specified generator. -/
theorem reconstruct {E : Modules R} (e : Frame E) (U : C)
    (x : SectionsOn E U) :
    coordinates e U x • generator e U = x := by
  apply (coordinates e U).injective
  rw [map_smul, coordinates_generator]
  simp only [smul_eq_mul, mul_one]

theorem coordinates_eq_zero_iff {E : Modules R} (e : Frame E) (U : C)
    (x : SectionsOn E U) : coordinates e U x = 0 ↔ x = 0 :=
  (coordinates e U).map_eq_zero_iff

/-- Frame coordinates commute with restriction in the underlying ringed site. -/
theorem coordinates_naturality {E : Modules R} (e : Frame E) {U V : C}
    (i : V ⟶ U) (x : SectionsOn E U) :
    coordinates e V (E.val.map i.op x) = R.obj.map i.op (coordinates e U x) := by
  exact PresheafOfModules.naturality_apply e.inv.val i.op x

theorem generator_naturality {E : Modules R} (e : Frame E) {U V : C}
    (i : V ⟶ U) : E.val.map i.op (generator e U) = generator e V := by
  apply (coordinates e V).injective
  rw [coordinates_naturality, coordinates_generator, map_one, coordinates_generator]

/-- The scalar coordinate of an actual sheaf map in two specified local frames. -/
def mapCoefficient {E F : Modules R} (e : Frame E) (f : Frame F)
    (a : E ⟶ F) (U : C) : RingSections R U :=
  coordinates f U (a.val.app (op U) (generator e U))

/-- A local module map is multiplication by its coefficient. -/
theorem map_coordinates {E F : Modules R} (e : Frame E) (f : Frame F)
    (a : E ⟶ F) (U : C) (x : SectionsOn E U) :
    coordinates f U (a.val.app (op U) x) =
      coordinates e U x * mapCoefficient e f a U := by
  conv_lhs => rw [← reconstruct e U x]
  rw [(a.val.app (op U)).hom.map_smul, (coordinates f U).map_smul]
  rfl

theorem mapCoefficient_naturality {E F : Modules R}
    (e : Frame E) (f : Frame F) (a : E ⟶ F) {U V : C} (i : V ⟶ U) :
    R.obj.map i.op (mapCoefficient e f a U) = mapCoefficient e f a V := by
  unfold mapCoefficient
  rw [← coordinates_naturality, ← PresheafOfModules.naturality_apply,
    generator_naturality]

@[simp]
theorem mapCoefficient_id {E : Modules R} (e : Frame E) (U : C) :
    mapCoefficient e e (𝟙 E) U = 1 := coordinates_generator e U

@[simp]
theorem mapCoefficient_zero {E F : Modules R} (e : Frame E) (f : Frame F) (U : C) :
    mapCoefficient e f (0 : E ⟶ F) U = 0 := by
  exact (coordinates f U).map_zero

theorem mapCoefficient_add {E F : Modules R} (e : Frame E) (f : Frame F)
    (a b : E ⟶ F) (U : C) :
    mapCoefficient e f (a + b) U =
      mapCoefficient e f a U + mapCoefficient e f b U :=
  (coordinates f U).map_add _ _

/-- Composition corresponds to multiplication of the actual coefficient functions. -/
theorem mapCoefficient_comp {E F G : Modules R}
    (e : Frame E) (f : Frame F) (g : Frame G)
    (a : E ⟶ F) (b : F ⟶ G) (U : C) :
    mapCoefficient e g (a ≫ b) U =
      mapCoefficient e f a U * mapCoefficient f g b U := by
  exact map_coordinates f g b U (a.val.app (op U) (generator e U))

theorem hom_ext_of_coefficients {E F : Modules R} (e : Frame E) (f : Frame F)
    {a b : E ⟶ F} (h : ∀ U, mapCoefficient e f a U = mapCoefficient e f b U) :
    a = b := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  apply (coordinates f U.unop).injective
  rw [map_coordinates, map_coordinates, h]

/-- A change of frame is measured by the new generator in the old coordinates. -/
def transition {E : Modules R} (e f : Frame E) (U : C) : RingSections R U :=
  coordinates e U (generator f U)

@[simp]
theorem transition_self {E : Modules R} (e : Frame E) (U : C) :
    transition e e U = 1 := coordinates_generator e U

theorem coordinates_change {E : Modules R} (e f : Frame E) (U : C)
    (x : SectionsOn E U) :
    coordinates e U x = coordinates f U x * transition e f U := by
  exact map_coordinates f e (𝟙 E) U x

theorem transition_cocycle {E : Modules R} (e f g : Frame E) (U : C) :
    transition e g U = transition f g U * transition e f U := by
  exact coordinates_change e f U (generator g U)

theorem transition_mul_reverse {E : Modules R} (e f : Frame E) (U : C) :
    transition e f U * transition f e U = 1 := by
  exact (transition_cocycle f e f U).symm.trans (transition_self f U)

/-- Transition functions are proved to be units; invertibility is not supplied. -/
def transitionUnit {E : Modules R} (e f : Frame E) (U : C) : (RingSections R U)ˣ where
  val := transition e f U
  inv := transition f e U
  val_inv := transition_mul_reverse e f U
  inv_val := transition_mul_reverse f e U

theorem transition_naturality {E : Modules R} (e f : Frame E)
    {U V : C} (i : V ⟶ U) :
    R.obj.map i.op (transition e f U) = transition e f V := by
  unfold transition
  rw [← coordinates_naturality, generator_naturality]

/-- Transporting both frames through the same actual isomorphism preserves
their transition function. -/
theorem transition_transport {E F : Modules R} (e f : Frame E)
    (a : E ≅ F) (U : C) :
    transition (e ≪≫ a) (f ≪≫ a) U = transition e f U := by
  change e.inv.val.app (op U)
      (a.inv.val.app (op U) (a.hom.val.app (op U) (generator f U))) =
    e.inv.val.app (op U) (generator f U)
  exact congrArg (fun x => e.inv.val.app (op U) x)
    (congrArg (fun g : E ⟶ E => g.val.app (op U) (generator f U))
      a.hom_inv_id)

/-- A frame of the actual local-Hom sheaf, with contravariance in its source. -/
def homFrame {E F : Modules R} (e : Frame E) (f : Frame F) :
    Frame (object E F) :=
  (unitSourceIso (SheafOfModules.unit (ringSheaf R))).symm ≪≫ mapIso e f

/-- The Hom-frame coordinate formula holds on every smaller object, not only
on the object where the Hom section was initially given. -/
theorem homFrame_apply {E F : Modules R} (e : Frame E) (f : Frame F)
    (U : C) (r : RingSections R U) (V : (Over U)ᵒᵖ)
    (x : E.val.obj (op V.unop.left)) :
    ((homFrame e f).hom.val.app (op U) r).app V x =
      f.hom.val.app (op V.unop.left)
        (R.obj.map V.unop.hom.op r * coordinates e V.unop.left x) := by
  change f.hom.val.app (op V.unop.left)
      (((unitSourceIso (SheafOfModules.unit (ringSheaf R))).inv.val.app
        (op U) r).app V (e.inv.val.app (op V.unop.left) x)) = _
  rw [unitSourceIso_inv_app]
  exact congrArg (fun a => f.hom.val.app (op V.unop.left) a)
    (mul_comm (coordinates e V.unop.left x) (R.obj.map V.unop.hom.op r))

/-- Evaluation of a Hom-frame section becomes multiplication of coordinates. -/
theorem homFrame_evaluate_coordinates {E F : Modules R}
    (e : Frame E) (f : Frame F) (U : C) (r : RingSections R U)
    (V : (Over U)ᵒᵖ) (x : E.val.obj (op V.unop.left)) :
    coordinates f V.unop.left (((homFrame e f).hom.val.app (op U) r).app V x) =
      R.obj.map V.unop.hom.op r * coordinates e V.unop.left x := by
  rw [homFrame_apply]
  exact (coordinates f V.unop.left).apply_symm_apply _

set_option backward.isDefEq.respectTransparency.types false in
/-- The coefficient of any actual local-Hom section gives its action on
every local section.  The statement is not restricted to a selected generator. -/
theorem hom_coordinates {E F : Modules R} (e : Frame E) (f : Frame F)
    (U : C) (φ : Section E F U) (x : SectionsOn E U) :
    coordinates f U (evaluationAt E F U φ x) =
      coordinates (homFrame e f) U φ * coordinates e U x := by
  let r := coordinates (homFrame e f) U φ
  have hφ : (homFrame e f).hom.val.app (op U) r = φ :=
    (coordinates (homFrame e f) U).symm_apply_apply φ
  have h := homFrame_evaluate_coordinates e f U r (op (Over.mk (𝟙 U))) x
  rw [hφ] at h
  have hr : R.obj.map (𝟙 (op U)) r = r :=
    congrArg (fun a : R.obj.obj (op U) ⟶ R.obj.obj (op U) => a r)
      (R.obj.map_id (op U))
  change coordinates f U ((φ.app (op (Over.mk (𝟙 U)))).hom x) =
    R.obj.map (𝟙 (op U)) r * coordinates e U x at h
  rw [hr] at h
  change coordinates f U ((φ.app (op (Over.mk (𝟙 U)))).hom x) =
    r * coordinates e U x
  exact h

/-- The Hom transition is target transition times the inverse source
transition.  This proves the sign reversal needed for dual powers. -/
theorem homFrame_transition {E F : Modules R}
    (e e' : Frame E) (f f' : Frame F) (U : C) :
    transition (homFrame e f) (homFrame e' f') U =
      transition e' e U * transition f f' U := by
  let φ := generator (homFrame e' f') U
  have h : coordinates f U (evaluationAt E F U φ (generator e U)) =
      transition (homFrame e f) (homFrame e' f') U := by
    rw [hom_coordinates, coordinates_generator, mul_one]
    rfl
  calc
    transition (homFrame e f) (homFrame e' f') U =
        coordinates f U (evaluationAt E F U φ (generator e U)) := h.symm
    _ = coordinates f' U (evaluationAt E F U φ (generator e U)) *
        transition f f' U := coordinates_change f f' U _
    _ = transition e' e U * transition f f' U := by
      rw [hom_coordinates]
      change coordinates (homFrame e' f') U (generator (homFrame e' f') U) *
          coordinates e' U (generator e U) * transition f f' U = _
      rw [coordinates_generator, one_mul]
      rfl

theorem dualFrame_transition {E : Modules R} (e e' : Frame E) (U : C) :
    transition
      (homFrame e (Iso.refl (SheafOfModules.unit (ringSheaf R))))
      (homFrame e' (Iso.refl (SheafOfModules.unit (ringSheaf R)))) U =
      transition e' e U := by
  rw [homFrame_transition, transition_self, mul_one]

/-- A normalized dual frame takes value 1 on the original generator. -/
theorem dualFrame_evaluate_generator {E : Modules R} (e : Frame E) (U : C) :
    ((homFrame e (Iso.refl (SheafOfModules.unit (ringSheaf R)))).hom.val.app
      (op U) (1 : RingSections R U)).app (op (Over.mk (𝟙 U))) (generator e U) =
        (1 : RingSections R U) := by
  rw [homFrame_apply]
  change R.obj.map (𝟙 U).op (1 : RingSections R U) *
    coordinates e U (generator e U) = (1 : RingSections R U)
  rw [map_one, coordinates_generator, one_mul]

section Tensor

open CategoryTheory.MonoidalCategory
variable [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]

/-- The tensor of two unit sheaves is the unit, through actual sheafification. -/
def tensorUnitIso :
    SheafTensor.tensor R (SheafOfModules.unit (ringSheaf R))
      (SheafOfModules.unit (ringSheaf R)) ≅ SheafOfModules.unit (ringSheaf R) := by
  let O : Modules R := SheafOfModules.unit (ringSheaf R)
  let A : PresheafOfModules (ringSheaf R).obj := SheafTensor.tensorPresheaf R O O
  let u : A ≅ O.val := CategoryTheory.MonoidalCategory.leftUnitor
    (C := PresheafOfModulesOfCommRing R.obj) O.val
  let h : SheafTensor.tensor R O O ⟶ O :=
    (PresheafOfModules.sheafificationHomEquiv (R := ringSheaf R)
      (𝟙 (ringSheaf R).obj) (P := A) (F := O)).symm u.hom
  letI : IsIso h := SheafTensor.LocalEvaluation.sheafificationLift_isIso
    (R := R) (P := A) (F := O) u.hom
  exact asIso h

/-- The genuine tensor-pairing section, obtained from the sheafification unit. -/
def tensorPair (E F : Modules R) (U : C)
    (x : SectionsOn E U) (y : SectionsOn F U) :
    SectionsOn (SheafTensor.tensor R E F) U :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
    (SheafTensor.tensorPresheaf R E F)).app (op U)
      (x ⊗ₜ[RingSections R U] y)

/-- The sheafification unit is natural on actual local sections. -/
theorem sheafification_map_unit_apply
    {A B : PresheafOfModules (ringSheaf R).obj} (a : A ⟶ B)
    (U : C) (x : A.obj (op U)) :
    ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map a).val.app (op U)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app A).app
        (op U) x) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app B).app
        (op U) (a.app (op U) x) := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (ringSheaf R).obj)).unit.naturality a
  exact (congrArg (fun g : A ⟶ _ => g.app (op U) x) h).symm

theorem tensorUnitIso_hom_pair (U : C) (r s : RingSections R U) :
    (tensorUnitIso (R := R)).hom.val.app (op U)
      (tensorPair (SheafOfModules.unit (ringSheaf R))
        (SheafOfModules.unit (ringSheaf R)) U r s) = r * s := by
  let O : Modules R := SheafOfModules.unit (ringSheaf R)
  let A : PresheafOfModules (ringSheaf R).obj := SheafTensor.tensorPresheaf R O O
  let u : A ≅ O.val := CategoryTheory.MonoidalCategory.leftUnitor
    (C := PresheafOfModulesOfCommRing R.obj) O.val
  have h := SheafTensor.sheafificationUnit_lift (R := ringSheaf R)
    (P := A) (F := O) u.hom
  have h' := congrArg (fun g : A ⟶ O.val =>
    g.app (op U) (r ⊗ₜ[RingSections R U] s)) h
  change (tensorUnitIso (R := R)).hom.val.app (op U)
      (tensorPair (SheafOfModules.unit (ringSheaf R))
        (SheafOfModules.unit (ringSheaf R)) U r s) =
    (CategoryTheory.MonoidalCategory.leftUnitor
      (ModuleCat.of (RingSections R U) (RingSections R U))).hom (r ⊗ₜ s) at h'
  exact h'.trans (by simpa only [smul_eq_mul] using
    (ModuleCat.MonoidalCategory.leftUnitor_hom_apply
      (M := ModuleCat.of (RingSections R U) (RingSections R U)) r s))

theorem tensorIso_inv_pair {E E' F F' : Modules R} (e : E ≅ E') (f : F ≅ F')
    (U : C) (x : SectionsOn E' U) (y : SectionsOn F' U) :
    (SheafTensor.tensorIso R e f).inv.val.app (op U) (tensorPair E' F' U x y) =
      tensorPair E F U (e.inv.val.app (op U) x) (f.inv.val.app (op U) y) := by
  change ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom e.inv.val f.inv.val)).val.app (op U)
        (tensorPair E' F' U x y) = _
  unfold tensorPair
  rw [sheafification_map_unit_apply]
  rfl

/-- Tensor specified local bases before sheafifying. -/
def tensorFrame {E F : Modules R} (e : Frame E) (f : Frame F) :
    Frame (SheafTensor.tensor R E F) :=
  (tensorUnitIso (R := R)).symm ≪≫ SheafTensor.tensorIso R e f

/-- The specified tensor frame has the product coordinate on every pure tensor. -/
theorem tensorFrame_coordinates_pair {E F : Modules R} (e : Frame E) (f : Frame F)
    (U : C) (x : SectionsOn E U) (y : SectionsOn F U) :
    coordinates (tensorFrame e f) U (tensorPair E F U x y) =
      coordinates e U x * coordinates f U y := by
  change (tensorUnitIso (R := R)).hom.val.app (op U)
    ((SheafTensor.tensorIso R e f).inv.val.app (op U) (tensorPair E F U x y)) = _
  rw [tensorIso_inv_pair, tensorUnitIso_hom_pair]
  rfl

theorem tensorFrame_generator {E F : Modules R} (e : Frame E) (f : Frame F) (U : C) :
    generator (tensorFrame e f) U = tensorPair E F U (generator e U) (generator f U) := by
  apply (coordinates (tensorFrame e f) U).injective
  rw [coordinates_generator, tensorFrame_coordinates_pair,
    coordinates_generator, coordinates_generator, one_mul]

/-- Tensor-product transitions multiply, proved using the actual pairing. -/
theorem tensorFrame_transition {E F : Modules R}
    (e e' : Frame E) (f f' : Frame F) (U : C) :
    transition (tensorFrame e f) (tensorFrame e' f') U =
      transition e e' U * transition f f' U := by
  unfold transition
  rw [tensorFrame_generator, tensorFrame_coordinates_pair]

end Tensor

end Generic

/-- A frame on the actual slice site of all opens contained in U. -/
abbrev OverFrame {X : Scheme} (E : X.Modules) (U : X.Opens) :=
  SheafOfModules.unit (X.ringCatSheaf.over U) ≅ E.over U

/-- Local section coordinates for an actual module sheaf on a scheme. -/
def coordinates {X : Scheme} {E : X.Modules} {U : X.Opens} (e : OverFrame E U) :
    SectionsOn E U ≃ₗ[RingSections X U] RingSections X U :=
  Generic.coordinates (R := X.sheaf.over U) e (Over.mk (𝟙 U))

@[simp]
theorem coordinates_apply {X : Scheme} {E : X.Modules} {U : X.Opens}
    (e : OverFrame E U) (x : SectionsOn E U) :
    coordinates e x = e.inv.val.app (op (Over.mk (𝟙 U))) x := rfl

@[simp]
theorem coordinates_symm_apply {X : Scheme} {E : X.Modules} {U : X.Opens}
    (e : OverFrame E U) (r : RingSections X U) :
    (coordinates e).symm r = e.hom.val.app (op (Over.mk (𝟙 U))) r := rfl

def generator {X : Scheme} {E : X.Modules} {U : X.Opens}
    (e : OverFrame E U) : SectionsOn E U := (coordinates e).symm 1

@[simp]
theorem coordinates_generator {X : Scheme} {E : X.Modules} {U : X.Opens}
    (e : OverFrame E U) : coordinates e (generator e) = 1 :=
  (coordinates e).apply_symm_apply 1

theorem reconstruct {X : Scheme} {E : X.Modules} {U : X.Opens}
    (e : OverFrame E U) (x : SectionsOn E U) : coordinates e x • generator e = x :=
  Generic.reconstruct (R := X.sheaf.over U) e (Over.mk (𝟙 U)) x

/-- Restrict the same specified frame, retaining the canonical slice comparisons. -/
def restrict {X : Scheme} {E : X.Modules} {U V : X.Opens} (i : V ⟶ U)
    (e : OverFrame E U) : OverFrame E V :=
  P1Ideal.restrictOverIso (E := structureModule X) (F := E) i e

/-- Coordinates obtained by restricting a frame are its original components
at the smaller open. -/
theorem restrict_coordinates_apply {X : Scheme} {E : X.Modules} {U V : X.Opens}
    (i : V ⟶ U) (e : OverFrame E U) (x : SectionsOn E V) :
    coordinates (restrict i e) x = e.inv.val.app (op (Over.mk i)) x := rfl

theorem coordinates_restrict {X : Scheme} {E : X.Modules} {U V : X.Opens}
    (i : V ⟶ U) (e : OverFrame E U) (x : SectionsOn E U) :
    coordinates (restrict i e) (E.presheaf.map i.op x) =
      X.presheaf.map i.op (coordinates e x) := by
  rw [restrict_coordinates_apply]
  let j : Over.mk i ⟶ Over.mk (𝟙 U) := Over.homMk i
  exact PresheafOfModules.naturality_apply e.inv.val j.op x

theorem generator_restrict {X : Scheme} {E : X.Modules} {U V : X.Opens}
    (i : V ⟶ U) (e : OverFrame E U) :
    E.presheaf.map i.op (generator e) = generator (restrict i e) := by
  apply (coordinates (restrict i e)).injective
  rw [coordinates_restrict, coordinates_generator, map_one, coordinates_generator]

/-- Convert an actual open-subscheme frame to a frame on the over site. -/
def ofOpenFrame {X : Scheme} {E : X.Modules} (U : X.Opens)
    (e : structureModule U.toScheme ≅ E.restrict U.ι) : OverFrame E U :=
  ModuleGluing.overIsoOfOpenIso U (Scheme.Modules.restrictUnitIso U.ι ≪≫ e)

/-- Convert the constructed slice frame back to an actual open-subscheme frame. -/
def toOpenFrame {X : Scheme} {E : X.Modules} {U : X.Opens}
    (e : OverFrame E U) : structureModule U.toScheme ≅ E.restrict U.ι :=
  (Scheme.Modules.restrictUnitIso U.ι).symm ≪≫
    ((Scheme.Modules.overFunctorEquiv U).app (structureModule X)).symm ≪≫
      (Scheme.Modules.overEquiv U).functor.mapIso e ≪≫
        (Scheme.Modules.overFunctorEquiv U).app E

/-- The trivial line has its actual identity frame on every slice. -/
def unitFrame {X : Scheme} (U : X.Opens) : OverFrame (structureModule X) U :=
  Iso.refl _

/-- Tensor frames of the original global sheaves, through their proved
sheafification/restriction comparison. -/
def tensorFrame {X : Scheme} {E F : X.Modules} {U : X.Opens}
    (e : OverFrame E U) (f : OverFrame F U) : OverFrame (tensorSheaf E F) U :=
  Generic.tensorFrame (R := X.sheaf.over U) e f ≪≫ (SheafTensor.tensorOverIso U E F).symm

/-- A frame of the originally chosen global internal Hom, not a replacement object. -/
def homFrame {X : Scheme} {E F : X.Modules} {U : X.Opens}
    (e : OverFrame E U) (f : OverFrame F U) : OverFrame (internalHomSheaf E F) U :=
  Generic.homFrame (R := X.sheaf.over U) e f ≪≫ (internalHomOverIso E F U).symm

/-- Dualization of an actual local frame uses the proved restriction comparison. -/
def dualFrame {X : Scheme} {E : X.Modules} {U : X.Opens}
    (e : OverFrame E U) : OverFrame (dualSheaf E) U :=
  homFrame e (unitFrame U)

/-- The actual change-of-basis function on the scheme open. -/
def transition {X : Scheme} {E : X.Modules} {U : X.Opens}
    (e f : OverFrame E U) : RingSections X U := coordinates e (generator f)

def transitionUnit {X : Scheme} {E : X.Modules} {U : X.Opens}
    (e f : OverFrame E U) : (RingSections X U)ˣ :=
  Generic.transitionUnit (R := X.sheaf.over U) e f (Over.mk (𝟙 U))

theorem coordinates_change {X : Scheme} {E : X.Modules} {U : X.Opens}
    (e f : OverFrame E U) (x : SectionsOn E U) :
    coordinates e x = coordinates f x * transition e f :=
  Generic.coordinates_change (R := X.sheaf.over U) e f (Over.mk (𝟙 U)) x

/-- The original chosen internal Hom has the expected change-of-frame law
on each fixed open; the chosen representing-object comparison cancels. -/
theorem homFrame_transition {X : Scheme} {E F : X.Modules} {U : X.Opens}
    (e e' : OverFrame E U) (f f' : OverFrame F U) :
    transition (homFrame e f) (homFrame e' f') =
      transition e' e * transition f f' := by
  change Generic.transition (R := X.sheaf.over U)
      (Generic.homFrame (R := X.sheaf.over U) e f ≪≫ (internalHomOverIso E F U).symm)
      (Generic.homFrame (R := X.sheaf.over U) e' f' ≪≫ (internalHomOverIso E F U).symm)
      (Over.mk (𝟙 U)) = _
  rw [Generic.transition_transport, Generic.homFrame_transition]
  rfl

theorem dualFrame_transition {X : Scheme} {E : X.Modules} {U : X.Opens}
    (e e' : OverFrame E U) :
    transition (dualFrame e) (dualFrame e') = transition e' e := by
  change transition (homFrame e (unitFrame U)) (homFrame e' (unitFrame U)) = _
  rw [homFrame_transition]
  rw [show transition (unitFrame U) (unitFrame U) = (1 : RingSections X U) from rfl,
    mul_one]

theorem tensorFrame_transition {X : Scheme} {E F : X.Modules} {U : X.Opens}
    (e e' : OverFrame E U) (f f' : OverFrame F U) :
    transition (tensorFrame e f) (tensorFrame e' f') =
      transition e e' * transition f f' := by
  change Generic.transition (R := X.sheaf.over U)
      (Generic.tensorFrame (R := X.sheaf.over U) e f ≪≫ (SheafTensor.tensorOverIso U E F).symm)
      (Generic.tensorFrame (R := X.sheaf.over U) e' f' ≪≫ (SheafTensor.tensorOverIso U E F).symm)
      (Over.mk (𝟙 U)) = _
  rw [Generic.transition_transport, Generic.tensorFrame_transition]
  rfl

/-- Frame recursion follows the original tensor-power recursion literally. -/
def linePowerFrame {X : Scheme} (L : LineBundle X) {U : X.Opens}
    (e : OverFrame L.sheaf U) : (n : ℕ) → OverFrame (linePower L n).sheaf U
  | 0 => unitFrame U
  | n + 1 => tensorFrame (linePowerFrame L e n) e

@[simp]
theorem linePowerFrame_zero {X : Scheme} (L : LineBundle X) {U : X.Opens}
    (e : OverFrame L.sheaf U) : linePowerFrame L e 0 = unitFrame U := rfl

@[simp]
theorem linePowerFrame_succ {X : Scheme} (L : LineBundle X) {U : X.Opens}
    (e : OverFrame L.sheaf U) (n : ℕ) :
    linePowerFrame L e (n + 1) = tensorFrame (linePowerFrame L e n) e := rfl

/-- On a fixed open, tensor powers raise the actual transition function to
the corresponding natural power. -/
theorem linePowerFrame_transition {X : Scheme} (L : LineBundle X) {U : X.Opens}
    (e f : OverFrame L.sheaf U) (n : ℕ) :
    transition (linePowerFrame L e n) (linePowerFrame L f n) = transition e f ^ n := by
  induction n with
  | zero =>
      change Generic.transition (R := X.sheaf.over U) (unitFrame U) (unitFrame U)
        (Over.mk (𝟙 U)) = transition e f ^ 0
      rw [Generic.transition_self, pow_zero]
  | succ n ih =>
      rw [linePowerFrame_succ, linePowerFrame_succ, tensorFrame_transition, ih, pow_succ]

/-- Both signs of the original integer-power type are given actual frames.
Negative powers use the frame of the actual chosen dual sheaf. -/
def linePowerIntFrame {X : Scheme} (L : LineBundle X) {U : X.Opens}
    (e : OverFrame L.sheaf U) : (d : ℤ) → OverFrame (linePowerInt L d).sheaf U
  | Int.ofNat n => linePowerFrame L e n
  | Int.negSucc n => linePowerFrame (dualLine L) (dualFrame e) (n + 1)

@[simp]
theorem linePowerIntFrame_natCast {X : Scheme} (L : LineBundle X) {U : X.Opens}
    (e : OverFrame L.sheaf U) (n : ℕ) :
    linePowerIntFrame L e (n : ℤ) = linePowerFrame L e n := rfl

@[simp]
theorem linePowerIntFrame_negSucc {X : Scheme} (L : LineBundle X) {U : X.Opens}
    (e : OverFrame L.sheaf U) (n : ℕ) :
    linePowerIntFrame L e (Int.negSucc n) =
      linePowerFrame (dualLine L) (dualFrame e) (n + 1) := rfl

/-- Negative-power transitions use the actual reciprocal unit, without
requiring an inverse operation on the entire ring of regular functions. -/
theorem linePowerIntFrame_transition_negSucc {X : Scheme} (L : LineBundle X)
    {U : X.Opens} (e f : OverFrame L.sheaf U) (n : ℕ) :
    transition (linePowerIntFrame L e (Int.negSucc n))
      (linePowerIntFrame L f (Int.negSucc n)) = transition f e ^ (n + 1) := by
  rw [linePowerIntFrame_negSucc, linePowerIntFrame_negSucc,
    linePowerFrame_transition, dualFrame_transition]

/-- Integer powers remain trivial on the *same specified* open, with a
constructed frame.  No classification of line bundles is used. -/
theorem linePowerInt_restrict_trivial {X : Scheme} (L : LineBundle X)
    {U : X.Opens} (e : structureModule U.toScheme ≅ L.sheaf.restrict U.ι) (d : ℤ) :
    Nonempty (structureModule U.toScheme ≅ (linePowerInt L d).sheaf.restrict U.ι) :=
  ⟨toOpenFrame (linePowerIntFrame L (ofOpenFrame U e) d)⟩

end LeBrunSalamon.LocalFrames

namespace LeBrunSalamon.P1TwistFrames

open LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.P1Charts LeBrunSalamon.P1Ideal LeBrunSalamon.LocalFrames
open scoped LaurentPolynomial

/-- Select the normalized ideal frames from their actual proved constructor. -/
def normalizedFrames (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) :
    NormalizedPointIdealFrames p.map :=
  Classical.choice (projectiveLinePoint_normalizedFrames P p)

/-- Both polynomial-chart ideal frames, selected from the same normalized pair. -/
def idealPolynomialFrame (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) (i : Fin 2) :
    structureModule (Spec (CommRingCat.of (Polynomial ℂ))) ≅
      (projectiveMinusOneLine P p).sheaf.restrict (polynomialChartInclusion i) := by
  rcases i with ⟨i, hi⟩
  cases i with
  | zero => exact (normalizedFrames P p).frameZero
  | succ i =>
    cases i with
    | zero => exact (normalizedFrames P p).frameOne
    | succ i => omega

@[simp]
theorem idealPolynomialFrame_zero (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) :
    idealPolynomialFrame P p 0 = (normalizedFrames P p).frameZero := rfl

@[simp]
theorem idealPolynomialFrame_one (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) :
    idealPolynomialFrame P p 1 = (normalizedFrames P p).frameOne := rfl

/-- Transport the normalized polynomial-chart frame to the actual open subscheme. -/
def idealOpenFrame (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) (i : Fin 2) :
    structureModule (chartOpen i).toScheme ≅
      (projectiveMinusOneLine P p).sheaf.restrict (chartOpen i).ι :=
  (restrictTrivial_of_iso (projectiveMinusOneLine P p).sheaf
    (chartOpen i).ι (polynomialChartInclusion i) (polynomialChartIso i)
    (polynomialChartIso_hom_inclusion i) (idealPolynomialFrame P p i).symm).symm

/-- The actual normalized ideal frame on all opens inside the selected chart. -/
def idealOverFrame (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) (i : Fin 2) :
    OverFrame (projectiveMinusOneLine P p).sheaf (chartOpen i) :=
  ofOpenFrame (chartOpen i) (idealOpenFrame P p i)

/-- The original O(1), defined as the actual dual of the point ideal, has a
constructed dual frame on each standard chart. -/
def oneOverFrame (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) (i : Fin 2) :
    OverFrame (projectiveOneLine P p).sheaf (chartOpen i) :=
  dualFrame (idealOverFrame P p i)

/-- Actual standard-chart frames for every original O(d), including d<0. -/
def twistOverFrame (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (d : ℤ) (i : Fin 2) : OverFrame (projectiveTwist P p d).sheaf (chartOpen i) :=
  linePowerIntFrame (projectiveOneLine P p) (oneOverFrame P p i) d

def twistOpenFrame (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (d : ℤ) (i : Fin 2) :
    structureModule (chartOpen i).toScheme ≅
      (projectiveTwist P p d).sheaf.restrict (chartOpen i).ι :=
  toOpenFrame (twistOverFrame P p d i)

/-- Return to the polynomial affine chart without changing the global twist. -/
def twistPolynomialFrame (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (d : ℤ) (i : Fin 2) :
    structureModule (Spec (CommRingCat.of (Polynomial ℂ))) ≅
      (projectiveTwist P p d).sheaf.restrict (polynomialChartInclusion i) :=
  (restrictTrivial_of_iso (projectiveTwist P p d).sheaf
    (polynomialChartInclusion i) (chartOpen i).ι (polynomialChartIso i).symm
    rfl (twistOpenFrame P p d i).symm).symm

theorem projectiveTwist_standardCharts_trivial
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) (d : ℤ) (i : Fin 2) :
    Nonempty (structureModule (Spec (CommRingCat.of (Polynomial ℂ))) ≅
      (projectiveTwist P p d).sheaf.restrict (polynomialChartInclusion i)) :=
  ⟨twistPolynomialFrame P p d i⟩

/-- The polynomial ring of a standard open, using the proved Proj chart calculation. -/
def polynomialChartRingEquiv (i : Fin 2) :
    RingSections lineScheme (chartOpen i) ≃+* Polynomial ℂ where
  toFun a := chartRingEquiv i ((chartSectionsIso i).inv a)
  invFun f := (chartSectionsIso i).hom ((chartRingEquiv i).symm f)
  left_inv a := by simp
  right_inv f := by simp
  map_mul' a b := by simp
  map_add' a b := by simp

/-- Polynomial coordinates of actual twist sections on a standard open.
The result is additive.  For arbitrary P, a C-linear claim would require
transport through its chosen base automorphism. -/
def polynomialCoordinates (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (d : ℤ) (i : Fin 2) :
    SectionsOn (projectiveTwist P p d).sheaf (chartOpen i) ≃+ Polynomial ℂ :=
  (coordinates (twistOverFrame P p d i)).toAddEquiv.trans
    (polynomialChartRingEquiv i).toAddEquiv

@[simp]
theorem polynomialCoordinates_zero (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (i : Fin 2) :
    polynomialCoordinates P p d i 0 = 0 := (polynomialCoordinates P p d i).map_zero

theorem polynomialCoordinates_eq_zero_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (i : Fin 2)
    (s : SectionsOn (projectiveTwist P p d).sheaf (chartOpen i)) :
    polynomialCoordinates P p d i s = 0 ↔ s = 0 :=
  (polynomialCoordinates P p d i).map_eq_zero_iff

/-- Multiplication by an actual regular function is multiplication by its
polynomial image.  This O-linear formula makes no base-field identification. -/
theorem polynomialCoordinates_smul (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (i : Fin 2)
    (a : RingSections lineScheme (chartOpen i))
    (s : SectionsOn (projectiveTwist P p d).sheaf (chartOpen i)) :
    polynomialCoordinates P p d i (a • s) =
      polynomialChartRingEquiv i a * polynomialCoordinates P p d i s := by
  change polynomialChartRingEquiv i
      (coordinates (twistOverFrame P p d i) (a • s)) = _
  rw [(coordinates (twistOverFrame P p d i)).map_smul]
  exact (polynomialChartRingEquiv i).map_mul _ _

/-- The chart generator has polynomial coordinate 1. -/
theorem polynomialCoordinates_generator (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (i : Fin 2) :
    polynomialCoordinates P p d i (generator (twistOverFrame P p d i)) = 1 := by
  change polynomialChartRingEquiv i
    (coordinates (twistOverFrame P p d i) (generator (twistOverFrame P p d i))) = 1
  rw [coordinates_generator, map_one]

/-- Actual sections on the complete chart intersection, measured in the
restriction of the first chart's chosen twist frame. -/
def overlapCoordinates (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) (d : ℤ) :
    SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0 ⊓ chartOpen 1) ≃ₗ[
      RingSections lineScheme (chartOpen 0 ⊓ chartOpen 1)]
      RingSections lineScheme (chartOpen 0 ⊓ chartOpen 1) :=
  coordinates (LocalFrames.restrict (homOfLE inf_le_left) (twistOverFrame P p d 0))

/-- The actual transition of the recursively constructed frames on the whole
chart intersection.  Its value is derived from these isomorphisms. -/
def overlapTransitionUnit (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) (d : ℤ) :
    (RingSections lineScheme (chartOpen 0 ⊓ chartOpen 1))ˣ :=
  LocalFrames.transitionUnit
    (LocalFrames.restrict (homOfLE inf_le_left) (twistOverFrame P p d 0))
    (LocalFrames.restrict (homOfLE inf_le_right) (twistOverFrame P p d 1))

theorem overlapCoordinates_restrict_zero (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0)) :
    overlapCoordinates P p d
        ((projectiveTwist P p d).sheaf.presheaf.map (homOfLE inf_le_left).op s) =
      lineScheme.presheaf.map (homOfLE inf_le_left).op
        (coordinates (twistOverFrame P p d 0) s) :=
  coordinates_restrict (homOfLE inf_le_left) (twistOverFrame P p d 0) s

/-- Restriction from the second chart is measured by the constructed unit.
Its normalization to t^d is supplied in the later uncompiled continuation. -/
theorem overlapCoordinates_restrict_one (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 1)) :
    overlapCoordinates P p d
        ((projectiveTwist P p d).sheaf.presheaf.map (homOfLE inf_le_right).op s) =
      lineScheme.presheaf.map (homOfLE inf_le_right).op
        (coordinates (twistOverFrame P p d 1) s) *
      (overlapTransitionUnit P p d : RingSections lineScheme (chartOpen 0 ⊓ chartOpen 1)) := by
  change coordinates
      (LocalFrames.restrict (homOfLE inf_le_left) (twistOverFrame P p d 0)) _ = _
  rw [LocalFrames.coordinates_change _
    (LocalFrames.restrict (homOfLE inf_le_right) (twistOverFrame P p d 1)),
    coordinates_restrict]
  rfl

/-- The equalizer equation for actual local twist sections, written entirely
in regular functions on the actual chart intersection. -/
theorem restrictions_agree_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s₀ : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0))
    (s₁ : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 1)) :
    (projectiveTwist P p d).sheaf.presheaf.map (homOfLE inf_le_left).op s₀ =
        (projectiveTwist P p d).sheaf.presheaf.map (homOfLE inf_le_right).op s₁ ↔
      lineScheme.presheaf.map (homOfLE inf_le_left).op
          (coordinates (twistOverFrame P p d 0) s₀) =
        lineScheme.presheaf.map (homOfLE inf_le_right).op
          (coordinates (twistOverFrame P p d 1) s₁) *
        (overlapTransitionUnit P p d :
          RingSections lineScheme (chartOpen 0 ⊓ chartOpen 1)) := by
  rw [← (overlapCoordinates P p d).injective.eq_iff,
    overlapCoordinates_restrict_zero, overlapCoordinates_restrict_one]

/-- Global functions on the Laurent affine scheme are functions on the
entire chart intersection, by its proved range equation. -/
def overlapSectionsIso :
    lineScheme.presheaf.obj (op (chartOpen 0 ⊓ chartOpen 1)) ≅
      CommRingCat.of ℂ[T;T⁻¹] :=
  lineScheme.presheaf.mapIso (eqToIso polynomialOverlap_range).op ≪≫
    (IsOpenImmersion.ΓIsoTop
      (polynomialOverlapToZero ≫ polynomialChartInclusion 0)).symm ≪≫
      Scheme.ΓSpecIso (CommRingCat.of ℂ[T;T⁻¹])

def overlapRingCoordinates :
    RingSections lineScheme (chartOpen 0 ⊓ chartOpen 1) ≃+* ℂ[T;T⁻¹] :=
  overlapSectionsIso.commRingCatIsoToRingEquiv

/-- Laurent-polynomial coordinates on actual overlap sections. -/
def laurentCoordinates (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) (d : ℤ) :
    SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0 ⊓ chartOpen 1) ≃+ ℂ[T;T⁻¹] :=
  (overlapCoordinates P p d).toAddEquiv.trans overlapRingCoordinates.toAddEquiv

/-- The actual overlap unit, now expressed as a Laurent polynomial unit. -/
def laurentTransitionUnit (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) (d : ℤ) :
    ℂ[T;T⁻¹]ˣ :=
  Units.map overlapRingCoordinates.toRingHom.toMonoidHom (overlapTransitionUnit P p d)

/-- The first actual restriction homomorphism, using the constructed chart
and overlap ring equivalences. Its equality with `Polynomial.toLaurent`
is supplied below in the uncompiled normalization continuation. -/
def zeroRestrictionRingHom : Polynomial ℂ →+* ℂ[T;T⁻¹] :=
  overlapRingCoordinates.toRingHom.comp
    ((lineScheme.presheaf.map (homOfLE inf_le_left).op).hom.comp
      (polynomialChartRingEquiv 0).symm.toRingHom)

/-- The second actual restriction homomorphism. The uncompiled normalization
continuation identifies it with inversion after the Laurent inclusion. -/
def oneRestrictionRingHom : Polynomial ℂ →+* ℂ[T;T⁻¹] :=
  overlapRingCoordinates.toRingHom.comp
    ((lineScheme.presheaf.map (homOfLE inf_le_right).op).hom.comp
      (polynomialChartRingEquiv 1).symm.toRingHom)

theorem laurentCoordinates_restrict_zero (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0)) :
    laurentCoordinates P p d
        ((projectiveTwist P p d).sheaf.presheaf.map (homOfLE inf_le_left).op s) =
      zeroRestrictionRingHom (polynomialCoordinates P p d 0 s) := by
  change overlapRingCoordinates (overlapCoordinates P p d _) = _
  rw [overlapCoordinates_restrict_zero]
  change overlapRingCoordinates (lineScheme.presheaf.map (homOfLE inf_le_left).op
      (coordinates (twistOverFrame P p d 0) s)) =
    overlapRingCoordinates (lineScheme.presheaf.map (homOfLE inf_le_left).op
      ((polynomialChartRingEquiv 0).symm
        (polynomialChartRingEquiv 0 (coordinates (twistOverFrame P p d 0) s))))
  rw [RingEquiv.symm_apply_apply]

theorem laurentCoordinates_restrict_one (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 1)) :
    laurentCoordinates P p d
        ((projectiveTwist P p d).sheaf.presheaf.map (homOfLE inf_le_right).op s) =
      oneRestrictionRingHom (polynomialCoordinates P p d 1 s) *
        (laurentTransitionUnit P p d : ℂ[T;T⁻¹]) := by
  change overlapRingCoordinates (overlapCoordinates P p d _) = _
  rw [overlapCoordinates_restrict_one, map_mul]
  change overlapRingCoordinates (lineScheme.presheaf.map (homOfLE inf_le_right).op
      (coordinates (twistOverFrame P p d 1) s)) *
        overlapRingCoordinates (overlapTransitionUnit P p d) =
    overlapRingCoordinates (lineScheme.presheaf.map (homOfLE inf_le_right).op
      ((polynomialChartRingEquiv 1).symm
        (polynomialChartRingEquiv 1 (coordinates (twistOverFrame P p d 1) s)))) *
      overlapRingCoordinates (overlapTransitionUnit P p d)
  rw [RingEquiv.symm_apply_apply]

/-- The actual transition is a nonzero monomial by the Laurent-unit theorem.
The later uncompiled normalization computes its coefficient as 1 and exponent as d. -/
theorem laurentTransitionUnit_is_monomial (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    ∃ (c : ℂ) (k : ℤ), c ≠ 0 ∧
      (laurentTransitionUnit P p d : ℂ[T;T⁻¹]) =
        LaurentPolynomial.C c * LaurentPolynomial.T k :=
  P1Overlap.unit_is_monomial _ (laurentTransitionUnit P p d).isUnit

/-- The scalar and exponent of this actual transition are uniquely determined.
This is uniqueness of a Laurent-unit expression, not Picard classification. -/
theorem laurentTransition_monomial_unique (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    ∃! z : ℂ × ℤ, z.1 ≠ 0 ∧
      (laurentTransitionUnit P p d : ℂ[T;T⁻¹]) =
        LaurentPolynomial.C z.1 * LaurentPolynomial.T z.2 := by
  obtain ⟨c, k, hc, he⟩ := laurentTransitionUnit_is_monomial P p d
  refine ⟨(c, k), ⟨hc, he⟩, ?_⟩
  intro z hz
  obtain ⟨h₀, h₁⟩ := P1Overlap.monomial_unique hz.1 hc (hz.2.symm.trans he)
  exact Prod.ext h₀ h₁

/- These definitions are normalized in the following uncompiled components:
actual restriction maps, restriction coherence of the chosen frames, and
the exact transition T d. Actual section and Cech calculations follow. -/

end LeBrunSalamon.P1TwistFrames

end
/- END UNCOMPILED continuation twist_frames.lean.txt -/

/- BEGIN UNCOMPILED continuation frame_coherence.lean.txt -/
/-!
Restriction coherence for the actual chosen local frames.

UNCOMPILED SOURCE DRAFT.  The user has deferred all Lean/Lake invocations until
the integrated source reaches 30,000 lines.  This component uses the tensor
sheafification unit and the concrete iterated-slice internal Hom comparison;
it assumes no separate coherence or normalization certificate.

Insertion point: after the LocalFrames definitions and fixed-open transition
laws in twist_frames.lean.txt.  No P1 classification or section-vanishing
theorem is used.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix

namespace LeBrunSalamon.LocalFrames.Generic

open HomConstruction.Generic

variable {C : Type} [Category.{0} C] {J : GrothendieckTopology C}
variable {R : Sheaf J CommRingCat}

/-- A frame morphism is determined by the images of 1 on the site objects. -/
theorem frame_ext_of_generators {E : Modules R} {e f : Frame E}
    (h : ∀ U, generator e U = generator f U) : e = f := by
  apply Iso.ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  change ∀ r : RingSections R U.unop, e.hom.val.app U r = f.hom.val.app U r
  intro r
  change e.hom.val.app U r = f.hom.val.app U r
  have he : e.hom.val.app U r = r • generator e U.unop := by
    simpa only [generator, coordinates_symm_apply, smul_eq_mul, mul_one] using
      (e.hom.val.app U).hom.map_smul r (1 : RingSections R U.unop)
  have hf : f.hom.val.app U r = r • generator f U.unop := by
    simpa only [generator, coordinates_symm_apply, smul_eq_mul, mul_one] using
      (f.hom.val.app U).hom.map_smul r (1 : RingSections R U.unop)
  exact he.trans ((congrArg (fun x => r • x) (h U.unop)).trans hf.symm)

section Tensor

variable [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]

/-- The genuine sheafified tensor pairing commutes with restriction.
This is the naturality of the sheafification unit on a pure tensor. -/
theorem tensorPair_naturality (E F : Modules R) {U V : C} (i : V ⟶ U)
    (x : SectionsOn E U) (y : SectionsOn F U) :
    (SheafTensor.tensor R E F).val.map i.op (tensorPair E F U x y) =
      tensorPair E F V (E.val.map i.op x) (F.val.map i.op y) := by
  exact (PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
      (SheafTensor.tensorPresheaf R E F)) i.op
    (x ⊗ₜ[RingSections R U] y)).symm

end Tensor

end LeBrunSalamon.LocalFrames.Generic

namespace LeBrunSalamon.SheafTensor

/-- The chosen sheafification/restriction comparison sends the restricted
sheafification-unit section to the original sheafification-unit section. -/
theorem sheafificationOverHom_apply_unit {X : Scheme} (U : X.Opens)
    (P : PresheafOfModules X.ringCatSheaf.obj) (V : Over U)
    (x : P.obj (op V.left)) :
    (sheafificationOverHom X U P).val.app (op V)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 (X.ringCatSheaf.over U).obj)).unit.app
          ((overPresheaf X U).obj P)).app (op V) x) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app P).app (op V.left) x := by
  let A : PresheafOfModules (X.ringCatSheaf.over U).obj := (overPresheaf X U).obj P
  let F : SheafOfModules (X.ringCatSheaf.over U) :=
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).over U
  let a : A ⟶ F.val := (overPresheaf X U).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)
  have h := sheafificationUnit_lift (R := X.ringCatSheaf.over U)
    (P := A) (F := F) a
  exact congrArg (fun k : A ⟶ F.val => k.app (op V) x) h

/-- Pointwise coherence for the actual tensor restriction isomorphism.
It holds on every object of the slice, rather than only its terminal object. -/
theorem tensorOverIso_inv_pair {X : Scheme} (U : X.Opens) (E F : X.Modules)
    (V : Over U) (x : SectionsOn E V.left) (y : SectionsOn F V.left) :
    (tensorOverIso U E F).inv.val.app (op V)
      (LocalFrames.Generic.tensorPair (R := X.sheaf.over U)
        (E.over U) (F.over U) V x y) =
      LocalFrames.Generic.tensorPair (R := X.sheaf) E F V.left x y := by
  change (sheafificationOverHom X U (tensorPresheaf X.sheaf E F)).val.app (op V)
      (((PresheafOfModules.sheafification
        (𝟙 (X.ringCatSheaf.over U).obj)).map
          (overTensorPresheafIso U E F).inv).val.app (op V)
            (LocalFrames.Generic.tensorPair (R := X.sheaf.over U)
              (E.over U) (F.over U) V x y)) = _
  unfold LocalFrames.Generic.tensorPair
  have hu := LocalFrames.Generic.sheafification_map_unit_apply
    (R := X.sheaf.over U) (overTensorPresheafIso U E F).inv V
    (x ⊗ₜ[RingSections X V.left] y)
  exact (congrArg (fun z =>
      (sheafificationOverHom X U (tensorPresheaf X.sheaf E F)).val.app (op V) z)
    hu).trans (sheafificationOverHom_apply_unit U (tensorPresheaf X.sheaf E F) V
      (x ⊗ₜ[RingSections X V.left] y))

end LeBrunSalamon.SheafTensor

namespace LeBrunSalamon.LocalFrames

/-- On a scheme open, the single generator determines the entire slice frame.
The underlying fact is the existing unit-Hom/sections equivalence. -/
theorem ext_of_generator_eq {X : Scheme} {E : X.Modules} {U : X.Opens}
    {e f : OverFrame E U} (h : generator e = generator f) : e = f := by
  apply Iso.ext
  exact (SheafModuleLocal.unitOverHomEquiv E U).injective h

/-- The canonical slice comparisons in `restrict` act identically on the
underlying module components. -/
theorem restrict_hom_app {X : Scheme} {E : X.Modules} {U V : X.Opens}
    (i : V ⟶ U) (e : OverFrame E U) (W : Over V)
    (r : RingSections X W.left) :
    (restrict i e).hom.val.app (op W) r =
      e.hom.val.app (op ((Over.map i).obj W)) r := rfl

theorem restrict_inv_app {X : Scheme} {E : X.Modules} {U V : X.Opens}
    (i : V ⟶ U) (e : OverFrame E U) (W : Over V)
    (x : SectionsOn E W.left) :
    (restrict i e).inv.val.app (op W) x =
      e.inv.val.app (op ((Over.map i).obj W)) x := rfl

@[simp]
theorem restrict_unitFrame {X : Scheme} {U V : X.Opens} (i : V ⟶ U) :
    restrict i (unitFrame U) = unitFrame V := by
  apply Iso.ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- The generator of the actual global tensor sheaf is the actual global
tensor pairing of the two chosen local generators. -/
theorem tensorFrame_generator {X : Scheme} {E F : X.Modules} {U : X.Opens}
    (e : OverFrame E U) (f : OverFrame F U) :
    generator (tensorFrame e f) =
      Generic.tensorPair (R := X.sheaf) E F U (generator e) (generator f) := by
  change (SheafTensor.tensorOverIso U E F).inv.val.app (op (Over.mk (𝟙 U)))
      (Generic.generator (Generic.tensorFrame (R := X.sheaf.over U) e f)
        (Over.mk (𝟙 U))) = _
  rw [Generic.tensorFrame_generator, SheafTensor.tensorOverIso_inv_pair]
  rfl

/-- Restricting a tensor frame gives exactly the tensor frame of the
restricted factors, including the chosen sheafification comparisons. -/
theorem restrict_tensorFrame {X : Scheme} {E F : X.Modules} {U V : X.Opens}
    (i : V ⟶ U) (e : OverFrame E U) (f : OverFrame F U) :
    restrict i (tensorFrame e f) = tensorFrame (restrict i e) (restrict i f) := by
  apply ext_of_generator_eq
  calc
    generator (restrict i (tensorFrame e f)) =
        (tensorSheaf E F).val.map i.op (generator (tensorFrame e f)) :=
      (generator_restrict i (tensorFrame e f)).symm
    _ = Generic.tensorPair (R := X.sheaf) E F V
          (E.val.map i.op (generator e)) (F.val.map i.op (generator f)) := by
      rw [tensorFrame_generator]
      exact Generic.tensorPair_naturality E F i (generator e) (generator f)
    _ = generator (tensorFrame (restrict i e) (restrict i f)) := by
      rw [tensorFrame_generator]
      exact congrArg₂ (Generic.tensorPair (R := X.sheaf) E F V)
        (generator_restrict i e) (generator_restrict i f)

/-- The concrete local-Hom section sending the source generator to the
target generator.  Its definition uses the given frame maps themselves. -/
def homGeneratorSection {X : Scheme} {E F : X.Modules} {U : X.Opens}
    (e : OverFrame E U) (f : OverFrame F U) :
    HomConstruction.Generic.Section (R := X.sheaf) E F U :=
  (HomConstruction.Generic.sectionOverEquiv E F U).symm (e.inv ≫ f.hom)

@[simp]
theorem homGeneratorSection_app {X : Scheme} {E F : X.Modules} {U : X.Opens}
    (e : OverFrame E U) (f : OverFrame F U) (W : (Over U)ᵒᵖ)
    (x : SectionsOn E W.unop.left) :
    (homGeneratorSection e f).app W x =
      f.hom.val.app W (e.inv.val.app W x) := rfl

/-- This concrete Hom section restricts by composition of the actual frame
maps.  The slice comparison components are identities on the module values. -/
theorem homGeneratorSection_restrict {X : Scheme} {E F : X.Modules}
    {U V : X.Opens} (i : V ⟶ U) (e : OverFrame E U) (f : OverFrame F U) :
    (HomConstruction.Generic.object (R := X.sheaf) E F).val.map i.op
        (homGeneratorSection e f) =
      homGeneratorSection (restrict i e) (restrict i f) := by
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  rfl

/-- The chosen global Hom-frame generator is the image of the concrete
frame-composition section under the original representing-object isomorphism.
This explicitly checks the iterated-slice comparison in `internalHomOverIso`. -/
theorem homFrame_generator {X : Scheme} {E F : X.Modules} {U : X.Opens}
    (e : OverFrame E U) (f : OverFrame F U) :
    generator (homFrame e f) =
      (internalHomGenericIso E F).inv.val.app (op U) (homGeneratorSection e f) := by
  change (internalHomGenericIso E F).inv.val.app (op U)
      ((HomConstruction.Generic.overIso (R := X.sheaf) E F U).inv.val.app
        (op (Over.mk (𝟙 U)))
          (Generic.generator (Generic.homFrame (R := X.sheaf.over U) e f)
            (Over.mk (𝟙 U)))) = _
  apply congrArg ((internalHomGenericIso E F).inv.val.app (op U))
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  change ((Generic.homFrame (R := X.sheaf.over U) e f).hom.val.app
      (op (Over.mk (𝟙 U))) (1 : RingSections X U)).app
        (op ((Over.iteratedSliceBackward (Over.mk (𝟙 U))).obj W.unop)) x =
      f.hom.val.app W (e.inv.val.app W x)
  rw [Generic.homFrame_apply]
  simp only [map_one, one_mul, Category.comp_id, Generic.coordinates_apply]
  change f.hom.val.app (op (Over.mk (W.unop.hom ≫ 𝟙 U)))
      (e.inv.val.app (op (Over.mk (W.unop.hom ≫ 𝟙 U))) x) =
    f.hom.val.app W (e.inv.val.app W x)
  simp only [Category.comp_id] <;> rfl

/-- Hom restriction is coherent for the originally chosen internal-Hom
object.  Naturality of the global representing-object isomorphism is retained. -/
theorem restrict_homFrame {X : Scheme} {E F : X.Modules} {U V : X.Opens}
    (i : V ⟶ U) (e : OverFrame E U) (f : OverFrame F U) :
    restrict i (homFrame e f) = homFrame (restrict i e) (restrict i f) := by
  apply ext_of_generator_eq
  calc
    generator (restrict i (homFrame e f)) =
        (internalHomSheaf E F).val.map i.op (generator (homFrame e f)) :=
      (generator_restrict i (homFrame e f)).symm
    _ = (internalHomGenericIso E F).inv.val.app (op V)
          ((HomConstruction.Generic.object (R := X.sheaf) E F).val.map i.op
            (homGeneratorSection e f)) := by
      rw [homFrame_generator]
      exact (PresheafOfModules.naturality_apply
        (internalHomGenericIso E F).inv.val i.op (homGeneratorSection e f)).symm
    _ = generator (homFrame (restrict i e) (restrict i f)) := by
      rw [homGeneratorSection_restrict, homFrame_generator]

/-- Dual-frame coherence follows from Hom coherence and the actual unit frame. -/
theorem restrict_dualFrame {X : Scheme} {E : X.Modules} {U V : X.Opens}
    (i : V ⟶ U) (e : OverFrame E U) :
    restrict i (dualFrame e) = dualFrame (restrict i e) := by
  unfold dualFrame
  rw [restrict_homFrame, restrict_unitFrame]

/-- Nonnegative-power frame recursion commutes with shrinking the open. -/
theorem restrict_linePowerFrame {X : Scheme} (L : LineBundle X)
    {U V : X.Opens} (i : V ⟶ U) (e : OverFrame L.sheaf U) (n : ℕ) :
    restrict i (linePowerFrame L e n) = linePowerFrame L (restrict i e) n := by
  induction n with
  | zero => exact restrict_unitFrame i
  | succ n ih =>
      rw [linePowerFrame_succ, restrict_tensorFrame, ih, linePowerFrame_succ]

/-- Both signs of the original integer-power frame construction commute
with restriction.  Negative powers use the actual dual frame on both sides. -/
theorem restrict_linePowerIntFrame {X : Scheme} (L : LineBundle X)
    {U V : X.Opens} (i : V ⟶ U) (e : OverFrame L.sheaf U) (d : ℤ) :
    restrict i (linePowerIntFrame L e d) =
      linePowerIntFrame L (restrict i e) d := by
  cases d with
  | ofNat n => exact restrict_linePowerFrame L i e n
  | negSucc n =>
      change restrict i (linePowerFrame (dualLine L) (dualFrame e) (n + 1)) =
        linePowerFrame (dualLine L) (dualFrame (restrict i e)) (n + 1)
      rw [restrict_linePowerFrame, restrict_dualFrame]

/-- The transition of two restricted frames is the restriction of their
transition function, with no affineness or rank-classification assumption. -/
theorem transition_restrict {X : Scheme} {E : X.Modules} {U V : X.Opens}
    (i : V ⟶ U) (e f : OverFrame E U) :
    transition (restrict i e) (restrict i f) =
      X.presheaf.map i.op (transition e f) := by
  change coordinates (restrict i e) (generator (restrict i f)) =
    X.presheaf.map i.op (coordinates e (generator f))
  rw [← generator_restrict i f]
  exact coordinates_restrict i e (generator f)

end LeBrunSalamon.LocalFrames

end
/- END UNCOMPILED continuation frame_coherence.lean.txt -/

/- BEGIN UNCOMPILED continuation restriction_normalization.lean.txt -/
/-!
Actual affine restriction maps for the standard projective-line charts.

Uncompiled continuation. Insert immediately after twist_frames.lean.txt.
The two normalization equations are proved from the existing affine chart
isomorphisms and overlap inclusions. No normalization certificate is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite
open scoped LaurentPolynomial
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.P1Charts
open LeBrunSalamon.Skeleton

namespace LeBrunSalamon.P1TwistFrames

/-! The following elementary scheme identities keep equality transports out
of the explicit Proj calculation. They concern actual sheaf pullbacks. -/

private theorem gammaIsoTop_inv_eq_appLE {X Y : Scheme} (f : X ⟶ Y)
    [IsOpenImmersion f] :
    (IsOpenImmersion.ΓIsoTop f).inv =
      f.appLE f.opensRange ⊤ (by rw [Scheme.Hom.preimage_opensRange]) := by
  simp only [IsOpenImmersion.ΓIsoTop, Iso.trans_inv, Functor.mapIso_inv,
    Iso.op_inv, eqToIso.inv, eqToHom_op, Iso.symm_inv,
    Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

private theorem appLE_top_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : Z.Opens) (hg : ⊤ ≤ g ⁻¹ᵁ U) (hfg : ⊤ ≤ (f ≫ g) ⁻¹ᵁ U) :
    (f ≫ g).appLE U ⊤ hfg = g.appLE U ⊤ hg ≫ f.appTop := by
  calc
    _ = g.appLE U ⊤ hg ≫ f.appLE ⊤ ⊤ le_rfl :=
      (Scheme.Hom.appLE_comp_appLE f g U ⊤ ⊤ hg le_rfl).symm
    _ = _ := by simp [Scheme.Hom.appLE]

private theorem appLE_congr_morphism {X Y : Scheme} {f g : X ⟶ Y}
    (e : f = g) (U : Y.Opens) (V : X.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

private theorem open_topIso_inv_eq_appLE {X : Scheme} (U : X.Opens) :
    U.topIso.inv = U.ι.appLE U ⊤ U.ι_preimage_self.ge := by
  simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE] <;> congr 1

/-- Pullback through a chosen chart isomorphism separates into restriction
to the open subscheme and the isomorphism's map on global sections. -/
theorem isoChart_appLE {X Y : Scheme} (U : X.Opens)
    (e : U.toScheme ≅ Y) (h : ⊤ ≤ (e.inv ≫ U.ι) ⁻¹ᵁ U) :
    (e.inv ≫ U.ι).appLE U ⊤ h = U.topIso.inv ≫ e.inv.appTop := by
  rw [appLE_top_comp e.inv U.ι U
    U.ι_preimage_self.ge,
    ← open_topIso_inv_eq_appLE]

set_option backward.isDefEq.respectTransparency.types false in
/-- The established Proj section isomorphism is inverse to pullback along
the established homogeneous-localization chart inclusion. -/
theorem chartSectionsIso_hom_appLE (i : Fin 2) :
    (chartSectionsIso i).hom ≫
        (chartInclusion i).appLE (chartOpen i) ⊤
          (by rw [← chartInclusion_range i, Scheme.Hom.preimage_opensRange]) =
      (Scheme.ΓSpecIso (CommRingCat.of (ChartRing i))).inv := by
  have hchart : (chartIso i).hom.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (ChartRing i))).hom ≫
        (chartSectionsIso i).hom ≫ (chartOpen i).topIso.inv := by
    change (Proj.basicOpenToSpec grading (MvPolynomial.X i : Binary)).app ⊤ =
      (Scheme.ΓSpecIso (CommRingCat.of (ChartRing i))).hom ≫
        Proj.awayToSection grading (MvPolynomial.X i : Binary) ≫ (chartOpen i).topIso.inv
    exact Proj.basicOpenToSpec_app_top grading (MvPolynomial.X i : Binary)
  change (chartSectionsIso i).hom ≫
      ((chartIso i).inv ≫ (chartOpen i).ι).appLE (chartOpen i) ⊤ _ = _
  rw [isoChart_appLE]
  apply (cancel_epi (Scheme.ΓSpecIso (CommRingCat.of (ChartRing i))).hom).mp
  calc
    (Scheme.ΓSpecIso (CommRingCat.of (ChartRing i))).hom ≫
        ((chartSectionsIso i).hom ≫
          ((chartOpen i).topIso.inv ≫ (chartIso i).inv.appTop)) =
        (chartIso i).hom.appTop ≫ (chartIso i).inv.appTop := by
      rw [hchart] <;> simp only [Category.assoc]
    _ = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id] <;> rfl
    _ = (Scheme.ΓSpecIso (CommRingCat.of (ChartRing i))).hom ≫
        (Scheme.ΓSpecIso (CommRingCat.of (ChartRing i))).inv := by
      rw [Iso.hom_inv_id]

theorem chartSectionsIso_inv_eq_appLE (i : Fin 2) :
    (chartSectionsIso i).inv =
      (chartInclusion i).appLE (chartOpen i) ⊤
          (by rw [← chartInclusion_range i, Scheme.Hom.preimage_opensRange]) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (ChartRing i))).hom := by
  apply (cancel_epi (chartSectionsIso i).hom).mp
  rw [← Category.assoc, chartSectionsIso_hom_appLE]
  simp only [Iso.hom_inv_id, Iso.inv_hom_id]

/-- Polynomial coordinates are the pullback along the actual polynomial
chart inclusion, followed by the canonical global-sections isomorphism. -/
theorem polynomialChartRingEquiv_eq_appLE (i : Fin 2) :
    CommRingCat.ofHom (polynomialChartRingEquiv i).toRingHom =
      (polynomialChartInclusion i).appLE (chartOpen i) ⊤
          (by rw [← polynomialChartInclusion_range i,
            Scheme.Hom.preimage_opensRange]) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).hom := by
  have hcomp :
      (polynomialChartInclusion i).appLE (chartOpen i) ⊤
          (by rw [← polynomialChartInclusion_range i,
            Scheme.Hom.preimage_opensRange]) =
        (chartInclusion i).appLE (chartOpen i) ⊤
            (by rw [← chartInclusion_range i, Scheme.Hom.preimage_opensRange]) ≫
          (Spec.map (CommRingCat.ofHom (chartToPolynomial i))).appTop := by
    change (Spec.map (CommRingCat.ofHom (chartToPolynomial i)) ≫
      chartInclusion i).appLE (chartOpen i) ⊤ _ = _
    exact appLE_top_comp _ _ _ _ _
  change (chartSectionsIso i).inv ≫ CommRingCat.ofHom (chartToPolynomial i) = _
  rw [hcomp, Category.assoc, Scheme.ΓSpecIso_naturality,
    ← Category.assoc, ← chartSectionsIso_inv_eq_appLE]

/-- The inverse coordinate map followed by actual chart pullback is the
canonical inclusion of a polynomial into global functions on its spectrum. -/
theorem polynomialChartRingEquiv_symm_appLE (i : Fin 2) :
    CommRingCat.ofHom (polynomialChartRingEquiv i).symm.toRingHom ≫
        (polynomialChartInclusion i).appLE (chartOpen i) ⊤
          (by rw [← polynomialChartInclusion_range i,
            Scheme.Hom.preimage_opensRange]) =
      (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).inv := by
  apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).hom).mp
  rw [Category.assoc, ← polynomialChartRingEquiv_eq_appLE]
  change (polynomialChartRingEquiv i).toCommRingCatIso.inv ≫
      (polynomialChartRingEquiv i).toCommRingCatIso.hom = _
  simp only [Iso.inv_hom_id]

/-- Laurent coordinates are pullback along the actual overlap immersion,
including the transport from its proved range to the chart intersection. -/
theorem overlapSectionsIso_hom_eq_appLE :
    overlapSectionsIso.hom =
      (polynomialOverlapToZero ≫ polynomialChartInclusion 0).appLE
          (chartOpen 0 ⊓ chartOpen 1) ⊤
          (by rw [← polynomialOverlap_range, Scheme.Hom.preimage_opensRange]) ≫
        (Scheme.ΓSpecIso (CommRingCat.of ℂ[T;T⁻¹])).hom := by
  simp only [overlapSectionsIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.op_hom, eqToIso.hom, eqToHom_op, Iso.symm_hom,
    gammaIsoTop_inv_eq_appLE, Scheme.Hom.map_appLE_assoc]

theorem overlapRingCoordinates_eq_appLE
    (a : RingSections lineScheme (chartOpen 0 ⊓ chartOpen 1)) :
    overlapRingCoordinates a =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ[T;T⁻¹])).hom
        ((polynomialOverlapToZero ≫ polynomialChartInclusion 0).appLE
          (chartOpen 0 ⊓ chartOpen 1) ⊤
          (by rw [← polynomialOverlap_range, Scheme.Hom.preimage_opensRange]) a) := by
  change overlapSectionsIso.hom a = _
  rw [overlapSectionsIso_hom_eq_appLE] <;> rfl

/-- The first actual structure-sheaf restriction is the ordinary polynomial
inclusion into Laurent polynomials. This discharges the first normalization
obligation for the original, already constructed projective-line charts. -/
theorem zeroRestrictionRingHom_eq_toLaurent :
    zeroRestrictionRingHom =
      (Polynomial.toLaurent : Polynomial ℂ →+* ℂ[T;T⁻¹]) := by
  have hcat : CommRingCat.ofHom zeroRestrictionRingHom =
      CommRingCat.ofHom (Polynomial.toLaurent : Polynomial ℂ →+* ℂ[T;T⁻¹]) := by
    change CommRingCat.ofHom (polynomialChartRingEquiv 0).symm.toRingHom ≫
      lineScheme.presheaf.map (homOfLE inf_le_left).op ≫
        overlapSectionsIso.hom = _
    rw [overlapSectionsIso_hom_eq_appLE, Scheme.Hom.map_appLE_assoc,
      appLE_top_comp polynomialOverlapToZero (polynomialChartInclusion 0)
        (chartOpen 0)
        (by rw [← polynomialChartInclusion_range 0,
          Scheme.Hom.preimage_opensRange])]
    rw [← Category.assoc, ← Category.assoc,
      polynomialChartRingEquiv_symm_appLE, Category.assoc]
    change (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).inv ≫
      (Spec.map (CommRingCat.ofHom
        (Polynomial.toLaurent : Polynomial ℂ →+* ℂ[T;T⁻¹]))).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of ℂ[T;T⁻¹])).hom = _
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact congrArg (fun f => f.hom) hcat

/-- The second actual structure-sheaf restriction substitutes the inverse
Laurent coordinate. The sign comes from the existing overlap morphism. -/
theorem oneRestrictionRingHom_eq_invert_toLaurent :
    oneRestrictionRingHom = LaurentPolynomial.invert.toRingHom.comp
      (Polynomial.toLaurent : Polynomial ℂ →+* ℂ[T;T⁻¹]) := by
  have hcomp (h : ⊤ ≤
      (polynomialOverlapToZero ≫ polynomialChartInclusion 0) ⁻¹ᵁ chartOpen 1) :
      (polynomialOverlapToZero ≫ polynomialChartInclusion 0).appLE
          (chartOpen 1) ⊤ h =
        (polynomialChartInclusion 1).appLE (chartOpen 1) ⊤
            (by rw [← polynomialChartInclusion_range 1,
              Scheme.Hom.preimage_opensRange]) ≫ polynomialOverlapToOne.appTop := by
    calc
      _ = (polynomialOverlapToOne ≫ polynomialChartInclusion 1).appLE
          (chartOpen 1) ⊤
          (by rw [Scheme.Hom.comp_preimage, ← polynomialChartInclusion_range 1,
            Scheme.Hom.preimage_opensRange, Scheme.Hom.preimage_top]) :=
        appLE_congr_morphism polynomialOverlap_condition _ _ _ _
      _ = _ := appLE_top_comp _ _ _ _ _
  have hcat : CommRingCat.ofHom oneRestrictionRingHom =
      CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp
        (Polynomial.toLaurent : Polynomial ℂ →+* ℂ[T;T⁻¹])) := by
    change CommRingCat.ofHom (polynomialChartRingEquiv 1).symm.toRingHom ≫
      lineScheme.presheaf.map (homOfLE inf_le_right).op ≫
        overlapSectionsIso.hom = _
    rw [overlapSectionsIso_hom_eq_appLE, Scheme.Hom.map_appLE_assoc, hcomp]
    rw [← Category.assoc, ← Category.assoc,
      polynomialChartRingEquiv_symm_appLE, Category.assoc]
    change (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).inv ≫
      (Spec.map (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp
        (Polynomial.toLaurent : Polynomial ℂ →+* ℂ[T;T⁻¹])))).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of ℂ[T;T⁻¹])).hom = _
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact congrArg (fun f => f.hom) hcat

/-- Pulling canonical complex constants into a polynomial chart gives
constant polynomials. This concerns the specified coefficient structure. -/
theorem polynomialChartRingEquiv_canonical_constant (i : Fin 2) (c : ℂ) :
    polynomialChartRingEquiv i
        (lineScheme.presheaf.map (homOfLE le_top).op
          (canonicalProjectiveLine.structureMap.appTop
            ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))) =
      Polynomial.C c := by
  have hconstant :
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
          canonicalBaseMap.appTop ≫
          lineScheme.presheaf.map (homOfLE (show chartOpen i ≤ ⊤ from le_top)).op ≫
          CommRingCat.ofHom (polynomialChartRingEquiv i).toRingHom =
        CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ) := by
    have htop : (polynomialChartInclusion i).appLE ⊤ ⊤ (by simp) =
        (polynomialChartInclusion i).appTop := by
      simp [Scheme.Hom.appLE]
    rw [polynomialChartRingEquiv_eq_appLE, Scheme.Hom.map_appLE_assoc, htop]
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
      canonicalBaseMap.appTop ≫ (polynomialChartInclusion i).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).hom = _
    rw [← Scheme.Hom.comp_appTop_assoc, polynomialChartInclusion_baseMap,
      Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact congrArg (fun f : CommRingCat.of ℂ ⟶ CommRingCat.of (Polynomial ℂ) => f c)
    hconstant

/-- Actual section restriction from chart zero, with the structure-ring
normalization now substituted into the existing frame-coordinate theorem. -/
theorem laurentCoordinates_restrict_zero_normalized
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) (d : ℤ)
    (s : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0)) :
    laurentCoordinates P p d
        ((projectiveTwist P p d).sheaf.presheaf.map (homOfLE inf_le_left).op s) =
      Polynomial.toLaurent (polynomialCoordinates P p d 0 s) := by
  rw [laurentCoordinates_restrict_zero, zeroRestrictionRingHom_eq_toLaurent]

/-- The remaining factor in chart-one restriction is precisely the
constructed twist transition; the structure-ring substitution is settled. -/
theorem laurentCoordinates_restrict_one_normalized
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) (d : ℤ)
    (s : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 1)) :
    laurentCoordinates P p d
        ((projectiveTwist P p d).sheaf.presheaf.map (homOfLE inf_le_right).op s) =
      LaurentPolynomial.invert (Polynomial.toLaurent (polynomialCoordinates P p d 1 s)) *
        (laurentTransitionUnit P p d : ℂ[T;T⁻¹]) := by
  rw [laurentCoordinates_restrict_one, oneRestrictionRingHom_eq_invert_toLaurent] <;> rfl

end LeBrunSalamon.P1TwistFrames

end
/- END UNCOMPILED continuation restriction_normalization.lean.txt -/

/- BEGIN UNCOMPILED continuation ideal_transition_normalization.lean.txt -/
/-!
Actual frame transport from the open-cover coordinates to the Laurent overlap.

UNCOMPILED source continuation.  The identities below retain the originally
chosen point-ideal frames, the actual restriction functors, and the actual
isomorphism from the Laurent affine scheme to the chart intersection.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.P1Ideal

open LeBrunSalamon.ModuleGluing

/-- Normalizing the source of a transported local frame by the unit comparison
agrees with restricting the corresponding isomorphism of global restrictions.
This is the unit coherence needed to use `restrictIsoAlong_comp` for frames. -/
theorem unitIso_trans_transportedRestrictedFrame {X U V : Scheme}
    (E : X.Modules) (f : V ⟶ U) (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion j] [IsOpenImmersion k]
    (h : f ≫ j = k) (e : structureModule U ≅ E.restrict j) :
    Scheme.Modules.restrictUnitIso k ≪≫
        transportedRestrictedFrame E f j k h e =
      restrictIsoAlong f j k h (Scheme.Modules.restrictUnitIso j ≪≫ e) := by
  subst k
  simp only [restrictIsoAlong, transportRestrictIso_rfl,
    transportedRestrictedFrame, ModuleGluing.restrictFunctorCongr_rfl]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.refl_hom, NatTrans.id_app, Category.comp_id,
    restrictedFrame, restrictLocalIso, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← restrictUnitIso_comp f j]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- Successive transported restrictions of a frame are the single transported
restriction through the composite map.  The proof uses the checked coherence
for the actual restriction functors, not a replacement frame object. -/
theorem transportedRestrictedFrame_comp {X A B C : Scheme}
    (E : X.Modules) (f : B ⟶ A) (j : A ⟶ X) (i : B ⟶ X)
    (g : C ⟶ B) (k : C ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion j] [IsOpenImmersion i]
    [IsOpenImmersion g] [IsOpenImmersion k]
    (h : f ≫ j = i) (h' : g ≫ i = k)
    (e : structureModule A ≅ E.restrict j) :
    transportedRestrictedFrame E g i k h'
        (transportedRestrictedFrame E f j i h e) =
      transportedRestrictedFrame E (g ≫ f) j k
        (by rw [Category.assoc, h, h']) e := by
  have hw := restrictIsoAlong_comp f j i g k h h'
    (Scheme.Modules.restrictUnitIso j ≪≫ e)
  rw [← unitIso_trans_transportedRestrictedFrame,
    ← unitIso_trans_transportedRestrictedFrame,
    ← unitIso_trans_transportedRestrictedFrame] at hw
  apply Iso.ext
  apply (cancel_epi (Scheme.Modules.restrictUnitIso k).hom).1
  exact congrArg Iso.hom hw

/-- Equal factor maps give exactly the same transported frame. -/
theorem transportedRestrictedFrame_congr {X U V : Scheme}
    (E : X.Modules) {f g : V ⟶ U} (hfg : f = g)
    (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion g]
    [IsOpenImmersion j] [IsOpenImmersion k]
    (hf : f ≫ j = k) (hg : g ≫ j = k)
    (e : structureModule U ≅ E.restrict j) :
    transportedRestrictedFrame E f j k hf e =
      transportedRestrictedFrame E g j k hg e := by
  subst g
  rfl

/-- The old chart-triviality transport is the inverse of the actual transported
frame.  This fixes its orientation before applying it to the point ideal. -/
theorem restrictTrivial_of_iso_symm_eq_transportedFrame {X U V : Scheme}
    (E : X.Modules) (i : U ⟶ X) (j : V ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j]
    (c : U ≅ V) (hc : c.hom ≫ j = i)
    (e : structureModule V ≅ E.restrict j) :
    (restrictTrivial_of_iso E i j c hc e.symm).symm =
      transportedRestrictedFrame E c.hom j i hc e := by
  apply Iso.ext
  simp [restrictTrivial_of_iso, transportedRestrictedFrame, restrictedFrame,
    Category.assoc]

end LeBrunSalamon.P1Ideal

namespace LeBrunSalamon.LocalFrames

open LeBrunSalamon.P1Ideal LeBrunSalamon.ModuleGluing

/-- The conversion to the over site and back preserves the chosen frame. -/
@[simp]
theorem toOpenFrame_ofOpenFrame {X : Scheme} {E : X.Modules} (U : X.Opens)
    (e : structureModule U.toScheme ≅ E.restrict U.ι) :
    toOpenFrame (ofOpenFrame U e) = e := by
  unfold toOpenFrame ofOpenFrame
  rw [map_overIsoOfOpenIso]
  apply Iso.ext
  simp [Category.assoc]

/-- The reverse conversion also preserves every specified over-site frame. -/
@[simp]
theorem ofOpenFrame_toOpenFrame {X : Scheme} {E : X.Modules} {U : X.Opens}
    (e : OverFrame E U) : ofOpenFrame U (toOpenFrame e) = e := by
  apply (Scheme.Modules.overEquiv U).functor.mapIso_injective
  unfold ofOpenFrame
  rw [map_overIsoOfOpenIso]
  apply Iso.ext
  simp [toOpenFrame, Category.assoc]

/-- Restricting an over-site frame agrees with restricting its actual
open-subscheme frame, including all structure-sheaf unit comparisons. -/
theorem toOpenFrame_restrict {X : Scheme} {E : X.Modules} {U V : X.Opens}
    (i : V ⟶ U) (e : OverFrame E U) :
    toOpenFrame (restrict i e) =
      transportedRestrictedFrame E (X.homOfLE (leOfHom i)) U.ι V.ι
        (X.homOfLE_ι (leOfHom i)) (toOpenFrame e) := by
  have h := overIsoOfOpenIso_restrict (E := structureModule X) (F := E) i
    (Scheme.Modules.restrictUnitIso U.ι ≪≫ toOpenFrame e)
  change restrict i (ofOpenFrame U (toOpenFrame e)) =
    overIsoOfOpenIso V (restrictOpenIso i
      (Scheme.Modules.restrictUnitIso U.ι ≪≫ toOpenFrame e)) at h
  rw [ofOpenFrame_toOpenFrame, restrictOpenIso_eq_along,
    ← unitIso_trans_transportedRestrictedFrame] at h
  change restrict i e = ofOpenFrame V
    (transportedRestrictedFrame E (X.homOfLE (leOfHom i)) U.ι V.ι
      (X.homOfLE_ι (leOfHom i)) (toOpenFrame e)) at h
  rw [h, toOpenFrame_ofOpenFrame]

/-- On an open subscheme, the transition of the converted frames is the
restriction of the original transition function.  This computation uses the
actual over-equivalence components and the structure-sheaf comparison. -/
theorem toOpenFrame_transition {X : Scheme} {E : X.Modules} {U : X.Opens}
    (e f : OverFrame E U) (W : U.toScheme.Opens) :
    Generic.transition (R := U.toScheme.sheaf) (toOpenFrame e) (toOpenFrame f) W =
      X.presheaf.map (homOfLE (U.ι_image_le W)).op (transition e f) := by
  change (toOpenFrame e).inv.app W
    ((toOpenFrame f).hom.app W (1 : RingSections U.toScheme W)) = _
  simp only [toOpenFrame, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
    Iso.symm_hom, Iso.app_inv, Iso.app_hom, Functor.mapIso_inv,
    Functor.mapIso_hom, Scheme.Modules.Hom.comp_app,
    ModuleGluing.overFunctorEquiv_hom_app, ModuleGluing.overFunctorEquiv_inv_app,
    AddCommGrpCat.comp_apply, AddCommGrpCat.id_apply]
  change (U.ι.appIso W).hom
      (e.inv.val.app (op (Over.mk (homOfLE (U.ι_image_le W))))
        (f.hom.val.app (op (Over.mk (homOfLE (U.ι_image_le W))))
          ((U.ι.appIso W).inv 1))) = _
  rw [Scheme.Opens.ι_appIso]
  let i : U.ι ''ᵁ W ⟶ U := homOfLE (U.ι_image_le W)
  let j : Over.mk i ⟶ Over.mk (𝟙 U) := Over.homMk i
  exact (Generic.transition_naturality (R := X.sheaf.over U) e f j).symm

/-- Restriction of actual open-subscheme frames transports their transition
through the actual structure-sheaf isomorphism of the open immersion. -/
theorem restrictedFrame_transition {X U V : Scheme} (E : X.Modules)
    (g : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion g] [IsOpenImmersion j]
    (e f : structureModule U ≅ E.restrict j) (W : V.Opens) :
    Generic.transition (R := V.sheaf) (restrictedFrame E g j e)
        (restrictedFrame E g j f) W =
      (g.appIso W).hom (Generic.transition (R := U.sheaf) e f (g ''ᵁ W)) := by
  simp only [restrictedFrame, ← Iso.trans_assoc, Generic.transition_transport]
  change (g.appIso W).hom
      (e.inv.app (g ''ᵁ W)
        (f.hom.app (g ''ᵁ W) ((g.appIso W).inv (1 : RingSections V W)))) =
    (g.appIso W).hom (e.inv.app (g ''ᵁ W)
      (f.hom.app (g ''ᵁ W) (1 : RingSections U (g ''ᵁ W))))
  rw [map_one]

/-- Equality transport of the target restriction does not change the scalar
transition, so the same formula holds for the transported restriction. -/
theorem transportedRestrictedFrame_transition {X U V : Scheme} (E : X.Modules)
    (g : V ⟶ U) (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion j] [IsOpenImmersion k]
    (h : g ≫ j = k) (e f : structureModule U ≅ E.restrict j) (W : V.Opens) :
    Generic.transition (R := V.sheaf)
        (transportedRestrictedFrame E g j k h e)
        (transportedRestrictedFrame E g j k h f) W =
      (g.appIso W).hom (Generic.transition (R := U.sheaf) e f (g ''ᵁ W)) := by
  simp only [transportedRestrictedFrame, Generic.transition_transport]
  exact restrictedFrame_transition E g j e f W

/-- Reading a transition on any open-immersion presentation is actual
pullback of its regular function.  In particular this compares over-site
transitions with affine Laurent coordinates without a normalization hypothesis. -/
theorem transportedOverFrame_transition {X Y : Scheme} (E : X.Modules)
    (U : X.Opens) (g : Y ⟶ U.toScheme) (k : Y ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion k] (h : g ≫ U.ι = k)
    (e f : OverFrame E U) (W : Y.Opens) (hk : W ≤ k ⁻¹ᵁ U) :
    Generic.transition (R := Y.sheaf)
        (transportedRestrictedFrame E g U.ι k h (toOpenFrame e))
        (transportedRestrictedFrame E g U.ι k h (toOpenFrame f)) W =
      k.appLE U W hk (transition e f) := by
  rw [transportedRestrictedFrame_transition, toOpenFrame_transition]
  subst k
  have hmap : X.presheaf.map (homOfLE (U.ι_image_le (g ''ᵁ W))).op ≫
        (g.appIso W).hom = (g ≫ U.ι).appLE U W hk := by
    calc
      _ = U.ι.appLE U (g ''ᵁ W) (by simp) ≫ (g.appIso W).hom := by
        rw [Scheme.Opens.ι_appLE]
      _ = _ := by
        rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
  exact congrArg (fun a => a (transition e f)) hmap

end LeBrunSalamon.LocalFrames

open scoped LaurentPolynomial
open LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.P1Charts LeBrunSalamon.P1Ideal LeBrunSalamon.LocalFrames

namespace LeBrunSalamon.P1TwistFrames

/-- The selected ideal frame on the standard open is exactly the transported
normalized polynomial frame; the triviality construction introduces no rescaling. -/
theorem idealOpenFrame_eq_transportedFrame (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (i : Fin 2) :
    idealOpenFrame P p i =
      transportedRestrictedFrame (projectiveMinusOneLine P p).sheaf
        (polynomialChartIso i).hom (polynomialChartInclusion i) (chartOpen i).ι
        (polynomialChartIso_hom_inclusion i) (idealPolynomialFrame P p i) :=
  restrictTrivial_of_iso_symm_eq_transportedFrame
    (projectiveMinusOneLine P p).sheaf (chartOpen i).ι
    (polynomialChartInclusion i) (polynomialChartIso i)
    (polynomialChartIso_hom_inclusion i) (idealPolynomialFrame P p i)

/-- The first actual restricted over-site ideal frame, viewed on the Laurent
affine presentation of the whole chart intersection. -/
def idealOverlapZeroFrameViaOver (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) :
    affineStructureModule (CommRingCat.of ℂ[T;T⁻¹]) ≅ pointIdealOnOverlap p.map :=
  transportedRestrictedFrame (projectiveMinusOneLine P p).sheaf
    polynomialOverlapIsoInf.hom (chartOpen 0 ⊓ chartOpen 1).ι
    (polynomialOverlapToZero ≫ polynomialChartInclusion 0)
    polynomialOverlapIsoInf_hom_ι
    (toOpenFrame (LocalFrames.restrict (homOfLE inf_le_left)
      (idealOverFrame P p 0)))

/-- The second actual restricted over-site ideal frame on the same Laurent
affine presentation and the same restricted point-ideal object. -/
def idealOverlapOneFrameViaOver (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) :
    affineStructureModule (CommRingCat.of ℂ[T;T⁻¹]) ≅ pointIdealOnOverlap p.map :=
  transportedRestrictedFrame (projectiveMinusOneLine P p).sheaf
    polynomialOverlapIsoInf.hom (chartOpen 0 ⊓ chartOpen 1).ι
    (polynomialOverlapToZero ≫ polynomialChartInclusion 0)
    polynomialOverlapIsoInf_hom_ι
    (toOpenFrame (LocalFrames.restrict (homOfLE inf_le_right)
      (idealOverFrame P p 1)))

set_option backward.isDefEq.respectTransparency.types false in
/-- The first over-site frame really is the previously normalized Laurent
frame of the actual kernel inclusion. -/
theorem idealOverlapZeroFrameViaOver_eq (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) :
    idealOverlapZeroFrameViaOver P p =
      pointIdealOverlapZeroFrame (normalizedFrames P p) := by
  unfold idealOverlapZeroFrameViaOver
  rw [toOpenFrame_restrict]
  simp only [idealOverFrame, toOpenFrame_ofOpenFrame]
  rw [idealOpenFrame_eq_transportedFrame, transportedRestrictedFrame_comp,
    transportedRestrictedFrame_comp]
  have hp := (Category.assoc polynomialOverlapIsoInf.hom
    (lineScheme.homOfLE (inf_le_left :
      chartOpen 0 ⊓ chartOpen 1 ≤ chartOpen 0))
    (polynomialChartIso 0).hom).trans polynomialOverlapIsoInf_toZero
  have ht := transportedRestrictedFrame_congr
    (projectiveMinusOneLine P p).sheaf hp (polynomialChartInclusion 0)
    (polynomialOverlapToZero ≫ polynomialChartInclusion 0)
    (congrArg (fun a => a ≫ polynomialChartInclusion 0) hp) rfl
    (idealPolynomialFrame P p 0)
  have hrefl (E : lineScheme.Modules) :
      (Iso.refl (Scheme.Modules.restrictFunctor
        (polynomialOverlapToZero ≫ polynomialChartInclusion 0))).app E =
          Iso.refl _ := rfl
  simpa only [transportedRestrictedFrame, idealPolynomialFrame_zero,
    pointIdealOverlapZeroFrame, projectiveMinusOneLine,
    ModuleGluing.restrictFunctorCongr_rfl,
    hrefl, Iso.trans_refl] using ht

set_option backward.isDefEq.respectTransparency.types false in
/-- The second over-site frame has the prescribed equal-composite transport;
it is not silently replaced by another trivialization. -/
theorem idealOverlapOneFrameViaOver_eq (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) :
    idealOverlapOneFrameViaOver P p =
      pointIdealOverlapOneFrame (normalizedFrames P p) := by
  unfold idealOverlapOneFrameViaOver
  rw [toOpenFrame_restrict]
  simp only [idealOverFrame, toOpenFrame_ofOpenFrame]
  rw [idealOpenFrame_eq_transportedFrame, transportedRestrictedFrame_comp,
    transportedRestrictedFrame_comp]
  have hp := (Category.assoc polynomialOverlapIsoInf.hom
    (lineScheme.homOfLE (inf_le_right :
      chartOpen 0 ⊓ chartOpen 1 ≤ chartOpen 1))
    (polynomialChartIso 1).hom).trans polynomialOverlapIsoInf_toOne
  have ht := transportedRestrictedFrame_congr
    (projectiveMinusOneLine P p).sheaf hp (polynomialChartInclusion 1)
    (polynomialOverlapToZero ≫ polynomialChartInclusion 0)
    ((congrArg (fun a => a ≫ polynomialChartInclusion 1) hp).trans
      polynomialOverlap_condition.symm) polynomialOverlap_condition.symm
    (idealPolynomialFrame P p 1)
  simpa only [transportedRestrictedFrame, idealPolynomialFrame_one,
    pointIdealOverlapOneFrame, projectiveMinusOneLine] using ht

/-- Exact normalized transition for the constructed over-site frames after
their actual restriction to the Laurent affine scheme. -/
theorem idealOverlapFrameViaOver_transition (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) :
    (idealOverlapOneFrameViaOver P p).hom =
      affineScalarEnd (LaurentPolynomial.T (-1) : ℂ[T;T⁻¹]) ≫
        (idealOverlapZeroFrameViaOver P p).hom := by
  rw [idealOverlapOneFrameViaOver_eq, idealOverlapZeroFrameViaOver_eq]
  exact pointIdealOverlapFrame_transition (normalizedFrames P p)

/-- The corresponding isomorphism equation records the same normalization. -/
theorem idealOverlapFrameViaOver_iso_transition (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) :
    idealOverlapOneFrameViaOver P p =
      affineScalarIso idealLaurentTransitionUnit ≪≫ idealOverlapZeroFrameViaOver P p := by
  apply Iso.ext
  exact idealOverlapFrameViaOver_transition P p

/-- Evaluation of the exact affine frame equation gives the normalized
Laurent function, with no nonzero scalar ambiguity. -/
theorem idealOverlapFrameViaOver_transition_top (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) :
    LocalFrames.Generic.transition
        (R := (Spec (CommRingCat.of ℂ[T;T⁻¹])).sheaf)
        (idealOverlapZeroFrameViaOver P p) (idealOverlapOneFrameViaOver P p) ⊤ =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ[T;T⁻¹])).inv
        (LaurentPolynomial.T (-1)) := by
  rw [idealOverlapFrameViaOver_iso_transition]
  change (LocalFrames.Generic.coordinates (idealOverlapZeroFrameViaOver P p) ⊤)
      ((LocalFrames.Generic.coordinates (idealOverlapZeroFrameViaOver P p) ⊤).symm
        ((affineScalarEnd (LaurentPolynomial.T (-1) : ℂ[T;T⁻¹])).app ⊤
          (1 : RingSections (Spec (CommRingCat.of ℂ[T;T⁻¹])) ⊤))) = _
  rw [LinearEquiv.apply_symm_apply, affineScalarEnd_app_one]
  change ((Spec (CommRingCat.of ℂ[T;T⁻¹])).presheaf.map (𝟙 _))
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ[T;T⁻¹])).inv
      (LaurentPolynomial.T (-1))) = _
  rw [CategoryTheory.Functor.map_id] <;> rfl

/-- The actual restricted ideal frames have Laurent transition t⁻¹.  The
coefficient is computed through the same overlap ring equivalence used by
`laurentTransitionUnit`, so this closes the actual frame normalization bridge. -/
theorem idealOverFrame_laurent_transition (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) :
    overlapRingCoordinates
        (LocalFrames.transition
          (LocalFrames.restrict (homOfLE inf_le_left) (idealOverFrame P p 0))
          (LocalFrames.restrict (homOfLE inf_le_right) (idealOverFrame P p 1))) =
      LaurentPolynomial.T (-1) := by
  rw [overlapRingCoordinates_eq_appLE]
  have h := transportedOverFrame_transition (projectiveMinusOneLine P p).sheaf
    (chartOpen 0 ⊓ chartOpen 1) polynomialOverlapIsoInf.hom
    (polynomialOverlapToZero ≫ polynomialChartInclusion 0)
    polynomialOverlapIsoInf_hom_ι
    (LocalFrames.restrict (homOfLE inf_le_left) (idealOverFrame P p 0))
    (LocalFrames.restrict (homOfLE inf_le_right) (idealOverFrame P p 1)) ⊤
    (by rw [← polynomialOverlap_range, Scheme.Hom.preimage_opensRange])
  change LocalFrames.Generic.transition
      (R := (Spec (CommRingCat.of ℂ[T;T⁻¹])).sheaf)
      (idealOverlapZeroFrameViaOver P p) (idealOverlapOneFrameViaOver P p) ⊤ = _ at h
  rw [← h, idealOverlapFrameViaOver_transition_top]
  exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of ℂ[T;T⁻¹])) _

/-- Reversing the two ideal frames gives t, by the proved inverse-transition
identity in the actual ring of regular functions on the intersection. -/
theorem idealOverFrame_laurent_reverse_transition (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) :
    overlapRingCoordinates
        (LocalFrames.transition
          (LocalFrames.restrict (homOfLE inf_le_right) (idealOverFrame P p 1))
          (LocalFrames.restrict (homOfLE inf_le_left) (idealOverFrame P p 0))) =
      LaurentPolynomial.T 1 := by
  let e := LocalFrames.restrict
    (homOfLE (inf_le_left : chartOpen 0 ⊓ chartOpen 1 ≤ chartOpen 0))
    (idealOverFrame P p 0)
  let f := LocalFrames.restrict
    (homOfLE (inf_le_right : chartOpen 0 ⊓ chartOpen 1 ≤ chartOpen 1))
    (idealOverFrame P p 1)
  have hmul := congrArg overlapRingCoordinates
    (LocalFrames.Generic.transition_mul_reverse (R := lineScheme.sheaf.over
      (chartOpen 0 ⊓ chartOpen 1)) e f (Over.mk (𝟙 _)))
  change overlapRingCoordinates (LocalFrames.transition e f *
    LocalFrames.transition f e) = overlapRingCoordinates 1 at hmul
  rw [map_mul, map_one] at hmul
  have he : overlapRingCoordinates (LocalFrames.transition e f) =
      LaurentPolynomial.T (-1) := idealOverFrame_laurent_transition P p
  rw [he] at hmul
  change overlapRingCoordinates (LocalFrames.transition f e) = _
  calc
    _ = (LaurentPolynomial.T 1 * LaurentPolynomial.T (-1)) *
        overlapRingCoordinates (LocalFrames.transition f e) := by
      rw [← LaurentPolynomial.T_add]
      norm_num
    _ = LaurentPolynomial.T 1 := by rw [mul_assoc, hmul, mul_one]

/-- Dualizing the normalized ideal frame produces transition t for the
originally defined O(1), including restriction of the chosen dual frame. -/
theorem oneOverFrame_laurent_transition (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) :
    overlapRingCoordinates
        (LocalFrames.transition
          (LocalFrames.restrict (homOfLE inf_le_left) (oneOverFrame P p 0))
          (LocalFrames.restrict (homOfLE inf_le_right) (oneOverFrame P p 1))) =
      LaurentPolynomial.T 1 := by
  simp only [oneOverFrame, LocalFrames.restrict_dualFrame,
    LocalFrames.dualFrame_transition]
  exact idealOverFrame_laurent_reverse_transition P p

/-- The reverse O(1) transition is t⁻¹, using the actual dual-frame identity. -/
theorem oneOverFrame_laurent_reverse_transition (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) :
    overlapRingCoordinates
        (LocalFrames.transition
          (LocalFrames.restrict (homOfLE inf_le_right) (oneOverFrame P p 1))
          (LocalFrames.restrict (homOfLE inf_le_left) (oneOverFrame P p 0))) =
      LaurentPolynomial.T (-1) := by
  simp only [oneOverFrame, LocalFrames.restrict_dualFrame,
    LocalFrames.dualFrame_transition]
  exact idealOverFrame_laurent_transition P p

/-- The transition unit of the actual recursively constructed O(d) frames
is exactly tᵈ for every integer d.  Both sign branches use restriction
coherence for the original tensor and dual sheaves. -/
theorem laurentTransitionUnit_eq_T (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    (laurentTransitionUnit P p d : ℂ[T;T⁻¹]) = LaurentPolynomial.T d := by
  change overlapRingCoordinates
    (LocalFrames.transition
      (LocalFrames.restrict (homOfLE inf_le_left)
        (linePowerIntFrame (projectiveOneLine P p) (oneOverFrame P p 0) d))
      (LocalFrames.restrict (homOfLE inf_le_right)
        (linePowerIntFrame (projectiveOneLine P p) (oneOverFrame P p 1) d))) = _
  rw [LocalFrames.restrict_linePowerIntFrame, LocalFrames.restrict_linePowerIntFrame]
  cases d with
  | ofNat n =>
      change overlapRingCoordinates (LocalFrames.transition
        (linePowerIntFrame (projectiveOneLine P p) _ (n : ℤ))
        (linePowerIntFrame (projectiveOneLine P p) _ (n : ℤ))) =
          LaurentPolynomial.T (n : ℤ)
      rw [linePowerIntFrame_natCast, linePowerIntFrame_natCast,
        linePowerFrame_transition, map_pow, oneOverFrame_laurent_transition,
        LaurentPolynomial.T_pow]
      simp only [mul_one]
  | negSucc n =>
      rw [linePowerIntFrame_transition_negSucc, map_pow,
        oneOverFrame_laurent_reverse_transition, LaurentPolynomial.T_pow]
      congr 1
      omega

end LeBrunSalamon.P1TwistFrames

end
/- END UNCOMPILED continuation ideal_transition_normalization.lean.txt -/

/- BEGIN UNCOMPILED continuation twist_section_bridge.lean.txt -/
/-!
Genuine sections of every original O(d) as an actual polynomial equalizer.

Uncompiled continuation. Integrate after both TwoChartSections and
P1TwistFrames. This component constructs its maps and transition from the
actual twist frames. It does not assume that the transition is T d and does
not identify its additive equalizer with the standard Laurent matching space.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.P1Charts
open LeBrunSalamon.P1TwistFrames LeBrunSalamon.TwoChartSections

namespace LeBrunSalamon.TwistSectionBridge

/-- The ring of actual regular functions on the complete chart intersection. -/
abbrev OverlapRing := RingSections lineScheme (chartOpen 0 ⊓ chartOpen 1)

/-- A polynomial in the first chart, restricted by the actual structure sheaf. -/
def polynomialRestrictionZero : Polynomial ℂ →+ OverlapRing where
  toFun f := lineScheme.presheaf.map (homOfLE inf_le_left).op
    ((polynomialChartRingEquiv 0).symm f)
  map_zero' := by simp
  map_add' f g := by simp

/-- A polynomial in the second chart, restricted by the actual structure sheaf.
No Laurent coordinate or inversion convention is imposed by this definition. -/
def polynomialRestrictionOne : Polynomial ℂ →+ OverlapRing where
  toFun g := lineScheme.presheaf.map (homOfLE inf_le_right).op
    ((polynomialChartRingEquiv 1).symm g)
  map_zero' := by simp
  map_add' f g := by simp

theorem polynomialRestrictionZero_coordinates (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0)) :
    polynomialRestrictionZero (polynomialCoordinates P p d 0 s) =
      lineScheme.presheaf.map (homOfLE inf_le_left).op
        (LocalFrames.coordinates (twistOverFrame P p d 0) s) := by
  change lineScheme.presheaf.map (homOfLE inf_le_left).op
      ((polynomialChartRingEquiv 0).symm
        (polynomialChartRingEquiv 0 (LocalFrames.coordinates (twistOverFrame P p d 0) s))) = _
  rw [RingEquiv.symm_apply_apply]

theorem polynomialRestrictionOne_coordinates (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 1)) :
    polynomialRestrictionOne (polynomialCoordinates P p d 1 s) =
      lineScheme.presheaf.map (homOfLE inf_le_right).op
        (LocalFrames.coordinates (twistOverFrame P p d 1) s) := by
  change lineScheme.presheaf.map (homOfLE inf_le_right).op
      ((polynomialChartRingEquiv 1).symm
        (polynomialChartRingEquiv 1 (LocalFrames.coordinates (twistOverFrame P p d 1) s))) = _
  rw [RingEquiv.symm_apply_apply]

/-- The actual twist Cech differential in the two constructed polynomial
coordinates, with values in regular functions on the genuine overlap. -/
def polynomialDifference (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) (d : ℤ) :
    (Polynomial ℂ × Polynomial ℂ) →+ OverlapRing where
  toFun fg := polynomialRestrictionZero fg.1 -
    polynomialRestrictionOne fg.2 * (overlapTransitionUnit P p d : OverlapRing)
  map_zero' := by simp
  map_add' fg hk := by
    change polynomialRestrictionZero (fg.1 + hk.1) -
      polynomialRestrictionOne (fg.2 + hk.2) *
        (overlapTransitionUnit P p d : OverlapRing) = _
    rw [map_add, map_add, add_mul]
    exact (sub_add_sub_comm _ _ _ _).symm

/-- The coordinate matching space of the original twist, using its constructed
transition rather than an assumed normalized power of a Laurent variable. -/
def polynomialMatchingSpace (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) (d : ℤ) :
    AddSubgroup (Polynomial ℂ × Polynomial ℂ) :=
  (polynomialDifference P p d).ker

theorem mem_polynomialMatchingSpace (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (f g : Polynomial ℂ) :
    (f, g) ∈ polynomialMatchingSpace P p d ↔
      polynomialRestrictionZero f =
        polynomialRestrictionOne g * (overlapTransitionUnit P p d : OverlapRing) :=
  sub_eq_zero

/-- The actual sheaf matching condition is equivalent to the constructed
polynomial equalizer condition, with no geometric compatibility assumption. -/
theorem pairCompatible_iff_polynomials (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0))
    (t : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 1)) :
    PairCompatible (projectiveTwist P p d).sheaf (chartOpen 0) (chartOpen 1) s t ↔
      (polynomialCoordinates P p d 0 s, polynomialCoordinates P p d 1 t) ∈
        polynomialMatchingSpace P p d := by
  rw [mem_polynomialMatchingSpace, polynomialRestrictionZero_coordinates,
    polynomialRestrictionOne_coordinates]
  exact restrictions_agree_iff P p d s t

/-- The actual overlap-coordinate map conjugates the actual sheaf differential
to the constructed polynomial differential. -/
theorem polynomialDifference_coordinates (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (st : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0) ×
      SectionsOn (projectiveTwist P p d).sheaf (chartOpen 1)) :
    polynomialDifference P p d
        (polynomialCoordinates P p d 0 st.1, polynomialCoordinates P p d 1 st.2) =
      overlapCoordinates P p d
        (pairDifference (projectiveTwist P p d).sheaf (chartOpen 0) (chartOpen 1) st) := by
  change polynomialRestrictionZero (polynomialCoordinates P p d 0 st.1) -
      polynomialRestrictionOne (polynomialCoordinates P p d 1 st.2) *
        (overlapTransitionUnit P p d : OverlapRing) =
    overlapCoordinates P p d
      ((projectiveTwist P p d).sheaf.presheaf.map (homOfLE inf_le_left).op st.1 -
        (projectiveTwist P p d).sheaf.presheaf.map (homOfLE inf_le_right).op st.2)
  rw [map_sub, overlapCoordinates_restrict_zero, overlapCoordinates_restrict_one,
    polynomialRestrictionZero_coordinates, polynomialRestrictionOne_coordinates]

/-- Coordinate conversion on the actual compatible local sections. -/
def localPolynomialPairEquiv (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) (d : ℤ) :
    matchingPairs (projectiveTwist P p d).sheaf (chartOpen 0) (chartOpen 1) ≃+
      polynomialMatchingSpace P p d where
  toFun st := ⟨(polynomialCoordinates P p d 0 st.val.1,
    polynomialCoordinates P p d 1 st.val.2),
    (pairCompatible_iff_polynomials P p d _ _).mp st.property⟩
  invFun fg := ⟨((polynomialCoordinates P p d 0).symm fg.val.1,
    (polynomialCoordinates P p d 1).symm fg.val.2), by
    apply (pairCompatible_iff_polynomials P p d _ _).mpr
    simpa only [AddEquiv.apply_symm_apply] using fg.property⟩
  left_inv st := by
    apply Subtype.ext
    exact Prod.ext ((polynomialCoordinates P p d 0).symm_apply_apply st.val.1)
      ((polynomialCoordinates P p d 1).symm_apply_apply st.val.2)
  right_inv fg := by
    apply Subtype.ext
    exact Prod.ext ((polynomialCoordinates P p d 0).apply_symm_apply fg.val.1)
      ((polynomialCoordinates P p d 1).apply_symm_apply fg.val.2)
  map_add' st ab := by
    apply Subtype.ext
    exact Prod.ext ((polynomialCoordinates P p d 0).map_add st.val.1 ab.val.1)
      ((polynomialCoordinates P p d 1).map_add st.val.2 ab.val.2)

/-- Genuine global sections of every original O(d), including negative d,
are identified with an explicitly constructed polynomial equalizer. This
does not yet evaluate the equalizer's dimension or its transition exponent. -/
def algebraicSectionsPolynomialEquiv (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    AlgebraicSection (projectiveTwist P p d).sheaf ≃+ polynomialMatchingSpace P p d :=
  (algebraicSectionsEquiv (projectiveTwist P p d).sheaf
    (chartOpen 0) (chartOpen 1) chartOpen_zero_sup_one).trans
      (localPolynomialPairEquiv P p d)

@[simp]
theorem algebraicSectionsPolynomialEquiv_fst (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s : AlgebraicSection (projectiveTwist P p d).sheaf) :
    (algebraicSectionsPolynomialEquiv P p d s).val.1 =
      polynomialCoordinates P p d 0
        (restrictValue (projectiveTwist P p d).sheaf le_top (sectionValue s)) := rfl

@[simp]
theorem algebraicSectionsPolynomialEquiv_snd (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s : AlgebraicSection (projectiveTwist P p d).sheaf) :
    (algebraicSectionsPolynomialEquiv P p d s).val.2 =
      polynomialCoordinates P p d 1
        (restrictValue (projectiveTwist P p d).sheaf le_top (sectionValue s)) := rfl

/-- Glue an actually compatible polynomial pair into the original algebraic section. -/
def sectionOfPolynomialPair (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    polynomialMatchingSpace P p d →+ AlgebraicSection (projectiveTwist P p d).sheaf :=
  (algebraicSectionsPolynomialEquiv P p d).symm.toAddMonoidHom

@[simp]
theorem sectionOfPolynomialPair_coordinates (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (fg : polynomialMatchingSpace P p d) :
    algebraicSectionsPolynomialEquiv P p d (sectionOfPolynomialPair P p d fg) = fg :=
  (algebraicSectionsPolynomialEquiv P p d).apply_symm_apply fg

@[simp]
theorem sectionOfPolynomialPair_restriction (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s : AlgebraicSection (projectiveTwist P p d).sheaf) :
    sectionOfPolynomialPair P p d (algebraicSectionsPolynomialEquiv P p d s) = s :=
  (algebraicSectionsPolynomialEquiv P p d).symm_apply_apply s

/-- The original section is zero exactly when both actual polynomial coordinates vanish. -/
theorem section_eq_zero_iff_polynomials (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s : AlgebraicSection (projectiveTwist P p d).sheaf) :
    s = 0 ↔ (algebraicSectionsPolynomialEquiv P p d s).val.1 = 0 ∧
      (algebraicSectionsPolynomialEquiv P p d s).val.2 = 0 := by
  constructor
  · rintro rfl
    have h := (algebraicSectionsPolynomialEquiv P p d).map_zero
    exact ⟨congrArg (fun st : polynomialMatchingSpace P p d => st.val.1) h,
      congrArg (fun st : polynomialMatchingSpace P p d => st.val.2) h⟩
  · intro hs
    apply (algebraicSectionsPolynomialEquiv P p d).injective
    rw [(algebraicSectionsPolynomialEquiv P p d).map_zero]
    apply Subtype.ext
    exact Prod.ext hs.1 hs.2

/-- The actual twist differential is solvable precisely when its polynomial
coordinate differential is solvable. Neither side is identified with Ext. -/
theorem polynomialDifference_surjective_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    Function.Surjective (polynomialDifference P p d) ↔
      Function.Surjective
        (pairDifference (projectiveTwist P p d).sheaf (chartOpen 0) (chartOpen 1)) := by
  constructor
  · intro hs w
    obtain ⟨fg, hfg⟩ := hs (overlapCoordinates P p d w)
    refine ⟨((polynomialCoordinates P p d 0).symm fg.1,
      (polynomialCoordinates P p d 1).symm fg.2), ?_⟩
    apply (overlapCoordinates P p d).injective
    rw [← polynomialDifference_coordinates]
    simpa only [AddEquiv.apply_symm_apply] using hfg
  · intro hs w
    obtain ⟨st, hst⟩ := hs ((overlapCoordinates P p d).symm w)
    refine ⟨(polynomialCoordinates P p d 0 st.1, polynomialCoordinates P p d 1 st.2), ?_⟩
    rw [polynomialDifference_coordinates, hst, LinearEquiv.apply_symm_apply]

end LeBrunSalamon.TwistSectionBridge

end
/- END UNCOMPILED continuation twist_section_bridge.lean.txt -/

/- BEGIN UNCOMPILED continuation actual_twist_sections.lean.txt -/
/-!
Actual sections and actual two-chart differences of the original integer twists.

This continuation is uncompiled. The coordinate equations below are obtained
from the constructed chart morphisms and chosen frames. They are not fields of
an assumed comparison certificate. Insert after the frame-normalization
components and before the original PhaseThirtyTwo classification targets.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.P1Charts
open LeBrunSalamon.P1TwistFrames LeBrunSalamon.TwoChartSections
open scoped LaurentPolynomial

namespace LeBrunSalamon.P1TwistSections

/-- Restriction from the first actual chart is the ordinary Laurent inclusion. -/
theorem restrict_zero_coordinates (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0)) :
    laurentCoordinates P p d
        (restrictValue (projectiveTwist P p d).sheaf inf_le_left s) =
      (polynomialCoordinates P p d 0 s).toLaurent := by
  change laurentCoordinates P p d
    ((projectiveTwist P p d).sheaf.presheaf.map (homOfLE inf_le_left).op s) = _
  rw [laurentCoordinates_restrict_zero, zeroRestrictionRingHom_eq_toLaurent]

/-- Restriction from the second chart has the actual transition t^d. -/
theorem restrict_one_coordinates (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 1)) :
    laurentCoordinates P p d
        (restrictValue (projectiveTwist P p d).sheaf inf_le_right s) =
      LaurentPolynomial.invert (polynomialCoordinates P p d 1 s).toLaurent *
        LaurentPolynomial.T d := by
  change laurentCoordinates P p d
    ((projectiveTwist P p d).sheaf.presheaf.map (homOfLE inf_le_right).op s) = _
  rw [laurentCoordinates_restrict_one, oneRestrictionRingHom_eq_invert_toLaurent,
    laurentTransitionUnit_eq_T] <;> rfl

/-- The computed Laurent matching space now parametrizes genuine sections
of the original point-ideal construction of O(d), for every chosen point. -/
def algebraicMatchingEquiv (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    AlgebraicSection (projectiveTwist P p d).sheaf ≃+
      P1Overlap.matchingSpace (K := ℂ) d :=
  algebraicSectionsLaurentEquiv (projectiveTwist P p d).sheaf
    (chartOpen 0) (chartOpen 1) d
    (polynomialCoordinates P p d 0) (polynomialCoordinates P p d 1)
    (laurentCoordinates P p d)
    (restrict_zero_coordinates P p d) (restrict_one_coordinates P p d)
    chartOpen_zero_sup_one

/-- The same comparison on ordinary global section values. -/
def globalMatchingEquiv (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    GlobalSections (projectiveTwist P p d).sheaf ≃+
      P1Overlap.matchingSpace (K := ℂ) d :=
  (sectionAddEquiv (projectiveTwist P p d).sheaf).symm.trans
    (algebraicMatchingEquiv P p d)

@[simp]
theorem algebraicMatchingEquiv_fst (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s : AlgebraicSection (projectiveTwist P p d).sheaf) :
    (algebraicMatchingEquiv P p d s).val.1 =
      polynomialCoordinates P p d 0
        (restrictValue (projectiveTwist P p d).sheaf le_top (sectionValue s)) := rfl

@[simp]
theorem algebraicMatchingEquiv_snd (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s : AlgebraicSection (projectiveTwist P p d).sheaf) :
    (algebraicMatchingEquiv P p d s).val.2 =
      polynomialCoordinates P p d 1
        (restrictValue (projectiveTwist P p d).sheaf le_top (sectionValue s)) := rfl

@[simp]
theorem globalMatchingEquiv_fst (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s : GlobalSections (projectiveTwist P p d).sheaf) :
    (globalMatchingEquiv P p d s).val.1 =
      polynomialCoordinates P p d 0
        (restrictValue (projectiveTwist P p d).sheaf le_top s) := by
  change polynomialCoordinates P p d 0
    (restrictValue (projectiveTwist P p d).sheaf le_top
      (sectionValue (sectionFromValue s))) = _
  rw [sectionFromValue_spec]

@[simp]
theorem globalMatchingEquiv_snd (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s : GlobalSections (projectiveTwist P p d).sheaf) :
    (globalMatchingEquiv P p d s).val.2 =
      polynomialCoordinates P p d 1
        (restrictValue (projectiveTwist P p d).sheaf le_top s) := by
  change polynomialCoordinates P p d 1
    (restrictValue (projectiveTwist P p d).sheaf le_top
      (sectionValue (sectionFromValue s))) = _
  rw [sectionFromValue_spec]

/-- Every standard matching pair glues to exactly one original section. -/
theorem existsUnique_algebraicSection (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (pq : P1Overlap.matchingSpace (K := ℂ) d) :
    ∃! s : AlgebraicSection (projectiveTwist P p d).sheaf,
      polynomialCoordinates P p d 0
          (restrictValue (projectiveTwist P p d).sheaf le_top (sectionValue s)) = pq.val.1 ∧
        polynomialCoordinates P p d 1
          (restrictValue (projectiveTwist P p d).sheaf le_top (sectionValue s)) = pq.val.2 :=
  existsUnique_section_of_laurent (projectiveTwist P p d).sheaf
    (chartOpen 0) (chartOpen 1) d
    (polynomialCoordinates P p d 0) (polynomialCoordinates P p d 1)
    (laurentCoordinates P p d)
    (restrict_zero_coordinates P p d) (restrict_one_coordinates P p d)
    chartOpen_zero_sup_one pq

/-- One polynomial chart detects equality of global twist sections. The
other chart is determined by the Laurent matching equation. -/
theorem globalSection_ext_zero_chart (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (s t : GlobalSections (projectiveTwist P p d).sheaf)
    (h : restrictValue (projectiveTwist P p d).sheaf
        (show chartOpen 0 ≤ ⊤ from le_top) s =
      restrictValue (projectiveTwist P p d).sheaf le_top t) : s = t := by
  apply (globalMatchingEquiv P p d).injective
  apply P1Overlap.matchingSpace_ext
  simp only [globalMatchingEquiv_fst, h]

/-- Negative twists have no genuine algebraic sections. This proof uses
neither Picard classification nor the degree chosen from that classification. -/
theorem algebraicSection_eq_zero_of_negative (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (hd : d < 0)
    (s : AlgebraicSection (projectiveTwist P p d).sheaf) : s = 0 := by
  letI := P1Overlap.matchingSpace_subsingleton_of_negative (K := ℂ) hd
  apply (algebraicMatchingEquiv P p d).injective
  exact Subsingleton.elim _ _

theorem globalSection_eq_zero_of_negative (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (hd : d < 0)
    (s : GlobalSections (projectiveTwist P p d).sheaf) : s = 0 := by
  letI := P1Overlap.matchingSpace_subsingleton_of_negative (K := ℂ) hd
  apply (globalMatchingEquiv P p d).injective
  exact Subsingleton.elim _ _

/-- The constructed internal-Hom comparison turns an actual morphism into
a Laurent matching pair of degree b-a. The isomorphism is chosen from the
proved tensor/dual law, not from line-bundle classification. -/
def homMatchingEquiv (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (a b : ℤ) :
    ((projectiveTwist P p a).sheaf ⟶ (projectiveTwist P p b).sheaf) ≃+
      P1Overlap.matchingSpace (K := ℂ) (b - a) :=
  (internalHomSectionAddEquiv (projectiveTwist P p a).sheaf
      (projectiveTwist P p b).sheaf).symm.trans
    ((algebraicSectionIso (Classical.choice (projectiveTwist_internalHom P p a b))).trans
      (algebraicMatchingEquiv P p (b - a)))

/-- Descending-degree Hom vanishing, proved before any classification target. -/
theorem hom_eq_zero_of_lt (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (a b : ℤ) (h : b < a)
    (f : (projectiveTwist P p a).sheaf ⟶ (projectiveTwist P p b).sheaf) : f = 0 := by
  letI := P1Overlap.matchingSpace_subsingleton_of_negative
    (K := ℂ) (d := b - a) (by omega)
  apply (homMatchingEquiv P p a b).injective
  exact Subsingleton.elim _ _

/-- The identity of a twist cannot vanish: its first-chart frame generator
has the nonzero polynomial coordinate 1. -/
theorem identity_ne_zero (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    (𝟙 (projectiveTwist P p d).sheaf) ≠ 0 := by
  intro h
  have he := congrArg
    (fun f : (projectiveTwist P p d).sheaf ⟶ (projectiveTwist P p d).sheaf =>
      polynomialCoordinates P p d 0
        (f.app (chartOpen 0) (LocalFrames.generator (twistOverFrame P p d 0)))) h
  change polynomialCoordinates P p d 0
      (LocalFrames.generator (twistOverFrame P p d 0)) =
    polynomialCoordinates P p d 0 0 at he
  rw [polynomialCoordinates_generator, map_zero] at he
  exact one_ne_zero he

/-- Uniqueness of the twist exponent is independent of existence of a
classification of all line bundles. -/
theorem exponent_eq_of_iso (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (a b : ℤ)
    (e : (projectiveTwist P p a).sheaf ≅ (projectiveTwist P p b).sheaf) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hz := hom_eq_zero_of_lt P p b a hab e.inv
    exact False.elim (identity_ne_zero P p b (by
      rw [← e.inv_hom_id, hz, zero_comp]))
  · exact hab
  · have hz := hom_eq_zero_of_lt P p a b hab e.hom
    exact False.elim (identity_ne_zero P p a (by
      rw [← e.hom_inv_id, hz, zero_comp]))

/-- Coordinate change for pairs of actual local sections. -/
def localPairCoordinates (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    (SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0) ×
      SectionsOn (projectiveTwist P p d).sheaf (chartOpen 1)) ≃+
        (Polynomial ℂ × Polynomial ℂ) :=
  (polynomialCoordinates P p d 0).prodCongr (polynomialCoordinates P p d 1)

/-- The actual sheaf difference is the standard Laurent differential in the
constructed coordinates. This is a statement about actual sections. -/
theorem difference_coordinates (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (st : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0) ×
      SectionsOn (projectiveTwist P p d).sheaf (chartOpen 1)) :
    laurentCoordinates P p d
        (pairDifference (projectiveTwist P p d).sheaf (chartOpen 0) (chartOpen 1) st) =
      P1Overlap.cechDifference d (localPairCoordinates P p d st) :=
  TwoChartSections.difference_coordinates (projectiveTwist P p d).sheaf
    (chartOpen 0) (chartOpen 1) d
    (polynomialCoordinates P p d 0) (polynomialCoordinates P p d 1)
    (laurentCoordinates P p d)
    (restrict_zero_coordinates P p d) (restrict_one_coordinates P p d) st

/-- A canonical representative on the genuine overlap, obtained by keeping
exactly the Laurent powers d<n<0 in its constructed frame. -/
def overlapNormalForm (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0 ⊓ chartOpen 1) →+
      SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0 ⊓ chartOpen 1) :=
  (laurentCoordinates P p d).symm.toAddMonoidHom.comp
    ((P1Overlap.cechNormalForm d).toAddMonoidHom.comp
      (laurentCoordinates P p d).toAddMonoidHom)

/-- Explicit actual local primitives for the part outside the gap interval. -/
def overlapHomotopy (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0 ⊓ chartOpen 1) →+
      (SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0) ×
        SectionsOn (projectiveTwist P p d).sheaf (chartOpen 1)) :=
  (localPairCoordinates P p d).symm.toAddMonoidHom.comp
    ((P1Overlap.cechHomotopy d).toAddMonoidHom.comp
      (laurentCoordinates P p d).toAddMonoidHom)

theorem normalForm_coordinates (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (w : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0 ⊓ chartOpen 1)) :
    laurentCoordinates P p d (overlapNormalForm P p d w) =
      P1Overlap.cechNormalForm d (laurentCoordinates P p d w) :=
  (laurentCoordinates P p d).apply_symm_apply _

theorem homotopy_coordinates (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (w : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0 ⊓ chartOpen 1)) :
    localPairCoordinates P p d (overlapHomotopy P p d w) =
      P1Overlap.cechHomotopy d (laurentCoordinates P p d w) :=
  (localPairCoordinates P p d).apply_symm_apply _

/-- An explicit decomposition in the original sheaf, not merely in a model
complex. The remaining term is the complete two-chart obstruction. -/
theorem homotopy_decomposition (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (w : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0 ⊓ chartOpen 1)) :
    pairDifference (projectiveTwist P p d).sheaf (chartOpen 0) (chartOpen 1)
        (overlapHomotopy P p d w) + overlapNormalForm P p d w = w := by
  apply (laurentCoordinates P p d).injective
  rw [map_add, difference_coordinates, homotopy_coordinates, normalForm_coordinates]
  exact P1Overlap.cechHomotopy_decomposition d _

theorem normalForm_idempotent (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (w : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0 ⊓ chartOpen 1)) :
    overlapNormalForm P p d (overlapNormalForm P p d w) = overlapNormalForm P p d w := by
  apply (laurentCoordinates P p d).injective
  simp only [normalForm_coordinates, P1Overlap.cechNormalForm_idempotent]

theorem normalForm_difference (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (st : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0) ×
      SectionsOn (projectiveTwist P p d).sheaf (chartOpen 1)) :
    overlapNormalForm P p d
      (pairDifference (projectiveTwist P p d).sheaf (chartOpen 0) (chartOpen 1) st) = 0 := by
  apply (laurentCoordinates P p d).injective
  rw [normalForm_coordinates, difference_coordinates, map_zero]
  exact P1Overlap.cechNormalForm_difference d _

/-- Exact solvability of the actual overlap equation, with no Ext/Cech
comparison silently included in the statement. -/
theorem primitive_exists_iff_normalForm_zero (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ)
    (w : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0 ⊓ chartOpen 1)) :
    Nonempty (Primitive (projectiveTwist P p d).sheaf (chartOpen 0) (chartOpen 1) w) ↔
      overlapNormalForm P p d w = 0 := by
  constructor
  · rintro ⟨⟨st, rfl⟩⟩
    exact normalForm_difference P p d st
  · intro h
    refine ⟨⟨overlapHomotopy P p d w, ?_⟩⟩
    simpa only [h, add_zero] using homotopy_decomposition P p d w

theorem normalForm_zero_of_ge_neg_one (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (hd : -1 ≤ d)
    (w : SectionsOn (projectiveTwist P p d).sheaf (chartOpen 0 ⊓ chartOpen 1)) :
    overlapNormalForm P p d w = 0 := by
  apply (laurentCoordinates P p d).injective
  rw [normalForm_coordinates, map_zero]
  exact P1Overlap.cechNormalForm_zero_of_ge_neg_one d hd _

/-- The actual differential has an explicitly constructed right inverse
in degrees at least -1. -/
theorem homotopy_rightInverse (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (hd : -1 ≤ d) :
    Function.RightInverse (overlapHomotopy P p d)
      (pairDifference (projectiveTwist P p d).sheaf (chartOpen 0) (chartOpen 1)) := by
  intro w
  simpa only [normalForm_zero_of_ge_neg_one P p d hd w, add_zero] using
    homotopy_decomposition P p d w

theorem pairDifference_surjective_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    Function.Surjective
      (pairDifference (projectiveTwist P p d).sheaf (chartOpen 0) (chartOpen 1)) ↔ -1 ≤ d :=
  pairDifference_surjective_iff_laurent (projectiveTwist P p d).sheaf
    (chartOpen 0) (chartOpen 1) d
    (polynomialCoordinates P p d 0) (polynomialCoordinates P p d 1)
    (laurentCoordinates P p d)
    (restrict_zero_coordinates P p d) (restrict_one_coordinates P p d)

end LeBrunSalamon.P1TwistSections

namespace LeBrunSalamon.TwistSectionBridge

/-- The differential constructed in the preceding continuation has exactly
the standard Laurent formula after applying its actual overlap coordinates. -/
theorem polynomialDifference_laurent (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (fg : Polynomial ℂ × Polynomial ℂ) :
    overlapRingCoordinates (polynomialDifference P p d fg) =
      P1Overlap.cechDifference d fg := by
  change overlapRingCoordinates
      (polynomialRestrictionZero fg.1 - polynomialRestrictionOne fg.2 *
        (overlapTransitionUnit P p d : OverlapRing)) = _
  rw [map_sub, map_mul]
  change zeroRestrictionRingHom fg.1 - oneRestrictionRingHom fg.2 *
    (laurentTransitionUnit P p d : ℂ[T;T⁻¹]) = _
  rw [zeroRestrictionRingHom_eq_toLaurent, oneRestrictionRingHom_eq_invert_toLaurent,
    laurentTransitionUnit_eq_T] <;> rfl

/-- The previously constructed actual polynomial kernel is the standard
matching subgroup, rather than a second unrelated model for sections. -/
theorem polynomialMatchingSpace_eq_standard (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    polynomialMatchingSpace P p d =
      (P1Overlap.matchingSpace (K := ℂ) d).toAddSubgroup := by
  ext fg
  change polynomialDifference P p d fg = 0 ↔ P1Overlap.Matching d fg.1 fg.2
  constructor
  · intro h
    have hc := congrArg overlapRingCoordinates h
    rw [polynomialDifference_laurent, map_zero] at hc
    exact sub_eq_zero.mp hc
  · intro h
    apply overlapRingCoordinates.injective
    rw [polynomialDifference_laurent, map_zero]
    exact sub_eq_zero.mpr h

end LeBrunSalamon.TwistSectionBridge

end
/- END UNCOMPILED continuation actual_twist_sections.lean.txt -/

/- BEGIN UNCOMPILED continuation scalar_endomorphisms.lean.txt -/
/-!
Actual scalar endomorphisms of the original projective-line twists.

Uncompiled continuation. Insert after the normalized P1TwistSections block
and before the original PhaseThirtyTwo classification and invertibility
targets. The maps below act on the original sheaves. No dimension-one
identification, classification hypothesis, or scalar compatibility certificate
is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.GlobalScalars

/-- Multiplication by an actual global regular function on an actual module
sheaf, using the already constructed whole-space local-Hom equivalence. -/
def scalarEnd {X : Scheme} (E : OModule X) (r : RingSections X ⊤) : E ⟶ E :=
  P1Ideal.homOfTopSection (r • P1Ideal.localSectionOfHom (𝟙 E) ⊤)

@[simp]
theorem scalarEnd_app {X : Scheme} (E : OModule X) (r : RingSections X ⊤)
    (U : X.Opens) (x : SectionsOn E U) :
    (scalarEnd E r).app U x = X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r • x := rfl

@[simp]
theorem scalarEnd_zero {X : Scheme} (E : OModule X) : scalarEnd E 0 = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op 0 • x = 0
  simp only [map_zero, zero_smul]

@[simp]
theorem scalarEnd_one {X : Scheme} (E : OModule X) : scalarEnd E 1 = 𝟙 E := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op 1 • x = x
  simp only [map_one, one_smul]

theorem scalarEnd_add {X : Scheme} (E : OModule X) (r s : RingSections X ⊤) :
    scalarEnd E (r + s) = scalarEnd E r + scalarEnd E s := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (r + s) • x =
    X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r • x +
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s • x
  rw [map_add, add_smul]

/-- Composition is multiplication of the original regular functions. -/
theorem scalarEnd_mul {X : Scheme} (E : OModule X) (r s : RingSections X ⊤) :
    scalarEnd E (r * s) = scalarEnd E r ≫ scalarEnd E s := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (r * s) • x =
    X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s •
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r • x)
  rw [map_mul, mul_smul]
  exact smul_comm _ _ _

/-- A global unit acts by an actual sheaf isomorphism, with its reciprocal
as the specified inverse. -/
def scalarIso {X : Scheme} (E : OModule X) (u : (RingSections X ⊤)ˣ) : E ≅ E where
  hom := scalarEnd E u.val
  inv := scalarEnd E u.inv
  hom_inv_id := by rw [← scalarEnd_mul, u.val_inv, scalarEnd_one]
  inv_hom_id := by rw [← scalarEnd_mul, u.inv_val, scalarEnd_one]

end LeBrunSalamon.GlobalScalars

namespace LeBrunSalamon.LocalFrames

/-- The coefficient of a genuine global sheaf map in two local frames. -/
def mapCoefficient {X : Scheme} {E F : OModule X} {U : X.Opens}
    (e : OverFrame E U) (f : OverFrame F U) (a : E ⟶ F) : RingSections X U :=
  coordinates f (a.app U (generator e))

/-- The actual map acts by multiplication by its local coefficient. -/
theorem map_coordinates {X : Scheme} {E F : OModule X} {U : X.Opens}
    (e : OverFrame E U) (f : OverFrame F U) (a : E ⟶ F) (x : SectionsOn E U) :
    coordinates f (a.app U x) = coordinates e x * mapCoefficient e f a := by
  conv_lhs => rw [← reconstruct e x]
  rw [Scheme.Modules.Hom.app_smul, (coordinates f).map_smul] <;> rfl

@[simp]
theorem mapCoefficient_id {X : Scheme} {E : OModule X} {U : X.Opens}
    (e : OverFrame E U) : mapCoefficient e e (𝟙 E) = 1 := coordinates_generator e

@[simp]
theorem mapCoefficient_zero {X : Scheme} {E F : OModule X} {U : X.Opens}
    (e : OverFrame E U) (f : OverFrame F U) : mapCoefficient e f (0 : E ⟶ F) = 0 :=
  (coordinates f).map_zero

theorem mapCoefficient_add {X : Scheme} {E F : OModule X} {U : X.Opens}
    (e : OverFrame E U) (f : OverFrame F U) (a b : E ⟶ F) :
    mapCoefficient e f (a + b) = mapCoefficient e f a + mapCoefficient e f b :=
  (coordinates f).map_add _ _

theorem mapCoefficient_comp {X : Scheme} {E F G : OModule X} {U : X.Opens}
    (e : OverFrame E U) (f : OverFrame F U) (g : OverFrame G U)
    (a : E ⟶ F) (b : F ⟶ G) :
    mapCoefficient e g (a ≫ b) = mapCoefficient e f a * mapCoefficient f g b :=
  map_coordinates f g b (a.app U (generator e))

/-- The coefficient commutes with actual restriction of both chosen frames. -/
theorem mapCoefficient_restrict {X : Scheme} {E F : OModule X} {U V : X.Opens}
    (i : V ⟶ U) (e : OverFrame E U) (f : OverFrame F U) (a : E ⟶ F) :
    X.presheaf.map i.op (mapCoefficient e f a) =
      mapCoefficient (restrict i e) (restrict i f) a := by
  unfold mapCoefficient
  rw [← generator_restrict i e, ← sheafHom_naturality a i,
    coordinates_restrict]

/-- A rank-one endomorphism coefficient is independent of the local frame.
The two frame-transition factors cancel as actual units. -/
theorem endCoefficient_frame_independent {X : Scheme} {E : OModule X} {U : X.Opens}
    (e f : OverFrame E U) (a : E ⟶ E) : mapCoefficient e e a = mapCoefficient f f a := by
  apply (transitionUnit e f).isUnit.mul_right_cancel
  change mapCoefficient e e a * transition e f = mapCoefficient f f a * transition e f
  calc
    _ = transition e f * mapCoefficient e e a := mul_comm _ _
    _ = coordinates e (a.app U (generator f)) := (map_coordinates e e a (generator f)).symm
    _ = mapCoefficient f f a * transition e f := coordinates_change e f _

/-- Equality of the coefficient on the full open implies equality of the
actual local maps on every subopen. -/
theorem localHom_eq_of_mapCoefficient_eq {X : Scheme} {E F : OModule X} {U : X.Opens}
    (e : OverFrame E U) (f : OverFrame F U) (a b : E ⟶ F)
    (h : mapCoefficient e f a = mapCoefficient e f b) :
    P1Ideal.localSectionOfHom a U = P1Ideal.localSectionOfHom b U := by
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  change a.app V.unop.left x = b.app V.unop.left x
  apply (coordinates (restrict V.unop.hom f)).injective
  rw [map_coordinates (restrict V.unop.hom e),
    map_coordinates (restrict V.unop.hom e),
    ← mapCoefficient_restrict, ← mapCoefficient_restrict, h]

theorem mapCoefficient_scalarEnd {X : Scheme} {E : OModule X} {U : X.Opens}
    (e : OverFrame E U) (r : RingSections X ⊤) :
    mapCoefficient e e (GlobalScalars.scalarEnd E r) =
      X.presheaf.map (homOfLE le_top).op r := by
  unfold mapCoefficient
  rw [GlobalScalars.scalarEnd_app, (coordinates e).map_smul, coordinates_generator]
  exact mul_one _

end LeBrunSalamon.LocalFrames

open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.P1Charts
open LeBrunSalamon.P1TwistFrames LeBrunSalamon.LocalFrames
open scoped LaurentPolynomial

namespace LeBrunSalamon.P1Endomorphisms

/-- Actual global constants for the fixed canonical complex structure.
This scalar structure suffices for the intrinsic invertibility statement;
an arbitrary supplied base changes the scalar label by its field automorphism. -/
def canonicalConstantRingHom : ℂ →+* RingSections lineScheme ⊤ :=
  Skeleton.canonicalProjectiveLine.structureMap.appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom

/-- Multiplication by a complex constant on any actual projective-line module. -/
def complexScalarEnd (E : OModule ProjectiveLine) (c : ℂ) : E ⟶ E :=
  GlobalScalars.scalarEnd E (canonicalConstantRingHom c)

@[simp]
theorem complexScalarEnd_zero (E : OModule ProjectiveLine) : complexScalarEnd E 0 = 0 := by
  simp only [complexScalarEnd, map_zero, GlobalScalars.scalarEnd_zero]

@[simp]
theorem complexScalarEnd_one (E : OModule ProjectiveLine) : complexScalarEnd E 1 = 𝟙 E := by
  simp only [complexScalarEnd, map_one, GlobalScalars.scalarEnd_one]

theorem complexScalarEnd_add (E : OModule ProjectiveLine) (c d : ℂ) :
    complexScalarEnd E (c + d) = complexScalarEnd E c + complexScalarEnd E d := by
  rw [complexScalarEnd, map_add, GlobalScalars.scalarEnd_add] <;> rfl

theorem complexScalarEnd_mul (E : OModule ProjectiveLine) (c d : ℂ) :
    complexScalarEnd E (c * d) = complexScalarEnd E c ≫ complexScalarEnd E d := by
  rw [complexScalarEnd, map_mul, GlobalScalars.scalarEnd_mul] <;> rfl

/-- Nonzero canonical constants act by explicit reciprocal isomorphisms. -/
def complexScalarIso (E : OModule ProjectiveLine) (u : ℂˣ) : E ≅ E :=
  GlobalScalars.scalarIso E (Units.map canonicalConstantRingHom.toMonoidHom u)

@[simp]
theorem complexScalarIso_hom (E : OModule ProjectiveLine) (u : ℂˣ) :
    (complexScalarIso E u).hom = complexScalarEnd E u.val := rfl

/-- Polynomial coefficient of the original sheaf endomorphism in its chosen
actual twist frame; no internal-Hom identification enters this definition. -/
def polynomialCoefficient (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (a : ℤ) (f : (projectiveTwist P p a).sheaf ⟶ (projectiveTwist P p a).sheaf)
    (i : Fin 2) : Polynomial ℂ :=
  polynomialChartRingEquiv i
    (LocalFrames.mapCoefficient (twistOverFrame P p a i) (twistOverFrame P p a i) f)

/-- Endomorphism coefficients have degree-zero matching, because the source
and target have the same transition and the coefficient is frame independent. -/
theorem polynomialCoefficient_matching (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (a : ℤ) (f : (projectiveTwist P p a).sheaf ⟶ (projectiveTwist P p a).sheaf) :
    P1Overlap.Matching 0 (polynomialCoefficient P p a f 0) (polynomialCoefficient P p a f 1) := by
  have h : zeroRestrictionRingHom (polynomialCoefficient P p a f 0) =
      oneRestrictionRingHom (polynomialCoefficient P p a f 1) := by
    change overlapRingCoordinates (lineScheme.presheaf.map (homOfLE inf_le_left).op
        ((polynomialChartRingEquiv 0).symm (polynomialChartRingEquiv 0
          (LocalFrames.mapCoefficient (twistOverFrame P p a 0) (twistOverFrame P p a 0) f)))) =
      overlapRingCoordinates (lineScheme.presheaf.map (homOfLE inf_le_right).op
        ((polynomialChartRingEquiv 1).symm (polynomialChartRingEquiv 1
          (LocalFrames.mapCoefficient (twistOverFrame P p a 1) (twistOverFrame P p a 1) f))))
    rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
    apply congrArg overlapRingCoordinates
    rw [LocalFrames.mapCoefficient_restrict, LocalFrames.mapCoefficient_restrict]
    exact LocalFrames.endCoefficient_frame_independent _ _ f
  rw [zeroRestrictionRingHom_eq_toLaurent, oneRestrictionRingHom_eq_invert_toLaurent] at h
  change (polynomialCoefficient P p a f 0).toLaurent =
    LaurentPolynomial.invert (polynomialCoefficient P p a f 1).toLaurent at h
  simpa only [P1Overlap.Matching, LaurentPolynomial.T_zero, mul_one, RingHom.comp_apply] using h

/-- The canonical complex scalar of an actual twist endomorphism. -/
def endomorphismScalar (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (a : ℤ) (f : (projectiveTwist P p a).sheaf ⟶ (projectiveTwist P p a).sheaf) : ℂ :=
  (polynomialCoefficient P p a f 0).coeff 0

theorem polynomialCoefficient_eq_C (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (a : ℤ) (f : (projectiveTwist P p a).sheaf ⟶ (projectiveTwist P p a).sheaf)
    (i : Fin 2) :
    polynomialCoefficient P p a f i = Polynomial.C (endomorphismScalar P p a f) := by
  have hm := polynomialCoefficient_matching P p a f
  have h0 : polynomialCoefficient P p a f 0 =
      Polynomial.C (endomorphismScalar P p a f) :=
    Polynomial.eq_C_of_natDegree_le_zero (P1Overlap.matching_degree_le (d := 0) hm)
  have h1 : polynomialCoefficient P p a f 1 =
      Polynomial.C (endomorphismScalar P p a f) := by
    apply P1Overlap.matching_first_injective hm
    simp only [h0, P1Overlap.Matching, Polynomial.toLaurent_C,
      LaurentPolynomial.invert_C, LaurentPolynomial.T_zero, mul_one]
  fin_cases i
  · exact h0
  · exact h1

/-- The explicitly constructed scalar endomorphism has constant polynomial
coefficient in every chosen frame, by the actual canonical constant formula. -/
theorem polynomialCoefficient_complexScalarEnd (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (a : ℤ) (c : ℂ) (i : Fin 2) :
    polynomialCoefficient P p a (complexScalarEnd (projectiveTwist P p a).sheaf c) i =
      Polynomial.C c := by
  unfold polynomialCoefficient complexScalarEnd
  rw [LocalFrames.mapCoefficient_scalarEnd]
  exact polynomialChartRingEquiv_canonical_constant i c

/-- The original global morphism is the actual scalar endomorphism determined
by its coefficient. The proof uses equality on all subopens of both charts. -/
theorem endomorphism_eq_scalar (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (a : ℤ) (f : (projectiveTwist P p a).sheaf ⟶ (projectiveTwist P p a).sheaf) :
    f = complexScalarEnd (projectiveTwist P p a).sheaf (endomorphismScalar P p a f) := by
  apply P1Ideal.hom_ext_of_localSections chartOpen chartOpen_cover
  intro i
  apply LocalFrames.localHom_eq_of_mapCoefficient_eq
    (twistOverFrame P p a i) (twistOverFrame P p a i)
  apply (polynomialChartRingEquiv i).injective
  change polynomialCoefficient P p a f i = polynomialCoefficient P p a
    (complexScalarEnd (projectiveTwist P p a).sheaf (endomorphismScalar P p a f)) i
  rw [polynomialCoefficient_eq_C, polynomialCoefficient_complexScalarEnd]

@[simp]
theorem endomorphismScalar_complexScalarEnd (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (a : ℤ) (c : ℂ) :
    endomorphismScalar P p a (complexScalarEnd (projectiveTwist P p a).sheaf c) = c := by
  unfold endomorphismScalar
  rw [polynomialCoefficient_complexScalarEnd]
  simp only [Polynomial.coeff_C_zero]

/-- Every endomorphism has a unique canonical scalar, with actual map equality. -/
theorem existsUnique_scalar (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (a : ℤ) (f : (projectiveTwist P p a).sheaf ⟶ (projectiveTwist P p a).sheaf) :
    ∃! c : ℂ, f = complexScalarEnd (projectiveTwist P p a).sheaf c := by
  refine ⟨endomorphismScalar P p a f, endomorphism_eq_scalar P p a f, ?_⟩
  intro c hc
  have h := congrArg (endomorphismScalar P p a) hc
  rw [endomorphismScalar_complexScalarEnd] at h
  exact h.symm

@[simp]
theorem endomorphismScalar_zero (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (a : ℤ) : endomorphismScalar P p a 0 = 0 := by
  rw [← complexScalarEnd_zero (projectiveTwist P p a).sheaf,
    endomorphismScalar_complexScalarEnd]

@[simp]
theorem endomorphismScalar_id (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (a : ℤ) :
    endomorphismScalar P p a (𝟙 (projectiveTwist P p a).sheaf) = 1 := by
  rw [← complexScalarEnd_one (projectiveTwist P p a).sheaf,
    endomorphismScalar_complexScalarEnd]

theorem endomorphismScalar_add (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (a : ℤ) (f g : (projectiveTwist P p a).sheaf ⟶ (projectiveTwist P p a).sheaf) :
    endomorphismScalar P p a (f + g) =
      endomorphismScalar P p a f + endomorphismScalar P p a g := by
  conv_lhs => rw [endomorphism_eq_scalar P p a f, endomorphism_eq_scalar P p a g]
  rw [← complexScalarEnd_add, endomorphismScalar_complexScalarEnd]

/-- The coefficient identifies actual composition with multiplication, not
just the underlying additive or vector-space structures. -/
theorem endomorphismScalar_comp (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (a : ℤ) (f g : (projectiveTwist P p a).sheaf ⟶ (projectiveTwist P p a).sheaf) :
    endomorphismScalar P p a (f ≫ g) =
      endomorphismScalar P p a f * endomorphismScalar P p a g := by
  conv_lhs => rw [endomorphism_eq_scalar P p a f, endomorphism_eq_scalar P p a g]
  rw [← complexScalarEnd_mul, endomorphismScalar_complexScalarEnd]

theorem endomorphismScalar_eq_zero_iff (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (a : ℤ) (f : (projectiveTwist P p a).sheaf ⟶ (projectiveTwist P p a).sheaf) :
    endomorphismScalar P p a f = 0 ↔ f = 0 := by
  constructor
  · intro h
    rw [endomorphism_eq_scalar P p a f, h, complexScalarEnd_zero]
  · rintro rfl
    exact endomorphismScalar_zero P p a

/-- Every nonzero endomorphism of the original O(a) is invertible, with the
reciprocal scalar providing an actual two-sided inverse. -/
theorem nonzero_endomorphism_isIso (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (a : ℤ) (f : (projectiveTwist P p a).sheaf ⟶ (projectiveTwist P p a).sheaf)
    (hf : f ≠ 0) : IsIso f := by
  have hc : endomorphismScalar P p a f ≠ 0 :=
    fun h => hf ((endomorphismScalar_eq_zero_iff P p a f).mp h)
  let e := complexScalarIso (projectiveTwist P p a).sheaf
    (Units.mk0 (endomorphismScalar P p a f) hc)
  have he : f = e.hom := endomorphism_eq_scalar P p a f
  rw [he]
  infer_instance

end LeBrunSalamon.P1Endomorphisms

end
/- END UNCOMPILED continuation scalar_endomorphisms.lean.txt -/

/- BEGIN UNCOMPILED continuation twist_global_generation.lean.txt -/
/-!
Global generation of the original twists by two specified actual sections.

Uncompiled continuation. Insert after the actual P1TwistSections comparison
and before the original PhaseThirtyTwo global-generation target. The proof
constructs the required categorical epimorphism from a free sheaf. It does
not replace that condition by a dimension count or an assumed fiber test.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.SectionGeneration

open LeBrunSalamon.PhaseThree

/-- Restricting the value of an algebraic section on 1 is its value on 1
at the smaller open; this is actual sheaf-map naturality. -/
theorem section_app_one_restrict {X : Scheme} {E : OModule X}
    (s : AlgebraicSection E) {U V : X.Opens} (i : V ⟶ U) :
    E.presheaf.map i.op (Scheme.Modules.Hom.app s U (1 : RingSections X U)) = Scheme.Modules.Hom.app s V (1 : RingSections X V) := by
  have h := sheafHom_naturality s i (1 : RingSections X U)
  change E.presheaf.map i.op (Scheme.Modules.Hom.app s U (1 : RingSections X U)) = Scheme.Modules.Hom.app s V (X.presheaf.map i.op 1) at h
  simpa only [map_one] using h

/-- If specified global sections are local frame generators on a cover,
their actual coproduct map is epi. The proof tests cancellation on every
subopen of the cover, using the existing local-Hom sheaf separation theorem. -/
theorem epi_of_local_frame_generators {X : Scheme} {E : OModule X} {I : Type}
    (U : I → X.Opens) (hcover : iSup U = ⊤) (s : I → AlgebraicSection E)
    (e : ∀ i, LocalFrames.OverFrame E (U i))
    (hs : ∀ i, (Scheme.Modules.Hom.app (s i)) (U i) (1 : RingSections X (U i)) = LocalFrames.generator (e i)) :
    Epi (Sigma.desc s : (∐ (fun _ : I => structureModule X)) ⟶ E) := by
  refine ⟨?_⟩
  intro Z f g hfg
  apply P1Ideal.hom_ext_of_localSections U hcover
  intro i
  have hi : s i ≫ f = s i ≫ g := by
    have h := congrArg (fun k => Sigma.ι (fun _ : I => structureModule X) i ≫ k) hfg
    simpa only [← Category.assoc, Sigma.ι_comp_desc] using h
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  change f.app V.unop.left x = g.app V.unop.left x
  let ei := LocalFrames.restrict V.unop.hom (e i)
  have hgen : (Scheme.Modules.Hom.app (s i)) V.unop.left (1 : RingSections X V.unop.left) = LocalFrames.generator ei := by
    rw [← section_app_one_restrict (s i) V.unop.hom, hs i,
      LocalFrames.generator_restrict]
  have hx : x = LocalFrames.coordinates ei x • (Scheme.Modules.Hom.app (s i)) V.unop.left (1 : RingSections X V.unop.left) := by
    rw [hgen]
    exact (LocalFrames.reconstruct ei x).symm
  have hv := congrArg
    (fun k : structureModule X ⟶ Z => k.app V.unop.left (1 : RingSections X V.unop.left)) hi
  change f.app V.unop.left ((Scheme.Modules.Hom.app (s i)) V.unop.left (1 : RingSections X V.unop.left)) =
    g.app V.unop.left ((Scheme.Modules.Hom.app (s i)) V.unop.left (1 : RingSections X V.unop.left)) at hv
  calc
    f.app V.unop.left x =
        f.app V.unop.left (LocalFrames.coordinates ei x • (Scheme.Modules.Hom.app (s i)) V.unop.left (1 : RingSections X V.unop.left)) :=
      congrArg (f.app V.unop.left) hx
    _ = LocalFrames.coordinates ei x • f.app V.unop.left ((Scheme.Modules.Hom.app (s i)) V.unop.left (1 : RingSections X V.unop.left)) :=
      Scheme.Modules.Hom.app_smul _ _ _
    _ = LocalFrames.coordinates ei x • g.app V.unop.left ((Scheme.Modules.Hom.app (s i)) V.unop.left (1 : RingSections X V.unop.left)) :=
      congrArg (fun y => LocalFrames.coordinates ei x • y) hv
    _ = g.app V.unop.left (LocalFrames.coordinates ei x • (Scheme.Modules.Hom.app (s i)) V.unop.left (1 : RingSections X V.unop.left)) :=
      (Scheme.Modules.Hom.app_smul _ _ _).symm
    _ = g.app V.unop.left x := congrArg (g.app V.unop.left) hx.symm

/-- The categorical epi criterion packages genuine generating sections in
the original mathlib structure used by IsGloballyGenerated. -/
def generatorsOfLocalFrames {X : Scheme} {E : OModule X} {I : Type}
    (U : I → X.Opens) (hcover : iSup U = ⊤) (s : I → AlgebraicSection E)
    (e : ∀ i, LocalFrames.OverFrame E (U i))
    (hs : ∀ i, (Scheme.Modules.Hom.app (s i)) (U i) (1 : RingSections X (U i)) = LocalFrames.generator (e i)) :
    SheafOfModules.GeneratingSections E := by
  letI := epi_of_local_frame_generators U hcover s e hs
  exact (SheafOfModules.free.generatingSections I).ofEpi (Sigma.desc s)

/-- If all actual global algebraic sections vanish, global generation forces
the identity to vanish. This uses the generating free map's actual epi property. -/
theorem not_globallyGenerated_of_section_vanishing {X : Scheme} {E : OModule X}
    (hidentity : (𝟙 E) ≠ 0) (hsections : ∀ s : AlgebraicSection E, s = 0) :
    ¬ IsGloballyGenerated E := by
  rintro ⟨G⟩
  have hzero : G.π = 0 := by
    apply Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan G.I)
    intro i
    change SheafOfModules.ιFree i ≫ G.π = SheafOfModules.ιFree i ≫ (0 : _)
    rw [comp_zero, ← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
    exact hsections _
  apply hidentity
  apply (cancel_epi G.π).mp
  simp only [hzero, zero_comp]

end LeBrunSalamon.SectionGeneration

open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.P1Charts
open LeBrunSalamon.PhaseThree
open LeBrunSalamon.P1TwistFrames LeBrunSalamon.P1TwistSections
open LeBrunSalamon.SectionGeneration LeBrunSalamon.TwoChartSections
open scoped LaurentPolynomial

namespace LeBrunSalamon.P1TwistGeneration

/-- A matching pair with coordinate 1 on chart zero. -/
def zeroGeneratorPair (n : ℕ) : P1Overlap.matchingSpace (K := ℂ) (n : ℤ) :=
  ⟨(1, Polynomial.X ^ n), by
    change P1Overlap.Matching (n : ℤ) 1 (Polynomial.X ^ n)
    simp only [P1Overlap.Matching, map_one, Polynomial.toLaurent_X_pow,
      LaurentPolynomial.invert_T, ← LaurentPolynomial.T_add, neg_add_cancel,
      LaurentPolynomial.T_zero]⟩

/-- A matching pair with coordinate 1 on chart one. -/
def oneGeneratorPair (n : ℕ) : P1Overlap.matchingSpace (K := ℂ) (n : ℤ) :=
  ⟨(Polynomial.X ^ n, 1), by
    change P1Overlap.Matching (n : ℤ) (Polynomial.X ^ n) 1
    simp only [P1Overlap.Matching, Polynomial.toLaurent_X_pow, map_one, one_mul]⟩

/-- Actual sections are obtained through the existing inverse sheaf gluing. -/
def zeroGeneratorSection (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) (n : ℕ) :
    AlgebraicSection (projectiveTwist P p (n : ℤ)).sheaf :=
  (algebraicMatchingEquiv P p (n : ℤ)).symm (zeroGeneratorPair n)

def oneGeneratorSection (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) (n : ℕ) :
    AlgebraicSection (projectiveTwist P p (n : ℤ)).sheaf :=
  (algebraicMatchingEquiv P p (n : ℤ)).symm (oneGeneratorPair n)

theorem zeroGeneratorSection_app_one (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (n : ℕ) :
    (Scheme.Modules.Hom.app (zeroGeneratorSection P p n)) (chartOpen 0) (1 : RingSections lineScheme (chartOpen 0)) =
      LocalFrames.generator (twistOverFrame P p (n : ℤ) 0) := by
  have h : polynomialCoordinates P p (n : ℤ) 0
      (restrictValue (projectiveTwist P p (n : ℤ)).sheaf le_top
        (sectionValue (zeroGeneratorSection P p n))) = 1 := by
    rw [← algebraicMatchingEquiv_fst, zeroGeneratorSection,
      AddEquiv.apply_symm_apply]
    rfl
  have hr := section_app_one_restrict (zeroGeneratorSection P p n)
    (homOfLE (show chartOpen 0 ≤ ⊤ from le_top))
  change restrictValue (projectiveTwist P p (n : ℤ)).sheaf le_top
    (sectionValue (zeroGeneratorSection P p n)) =
      (Scheme.Modules.Hom.app (zeroGeneratorSection P p n)) (chartOpen 0) (1 : RingSections lineScheme (chartOpen 0)) at hr
  rw [hr] at h
  apply (polynomialCoordinates P p (n : ℤ) 0).injective
  rw [polynomialCoordinates_generator]
  exact h

theorem oneGeneratorSection_app_one (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (n : ℕ) :
    (Scheme.Modules.Hom.app (oneGeneratorSection P p n)) (chartOpen 1) (1 : RingSections lineScheme (chartOpen 1)) =
      LocalFrames.generator (twistOverFrame P p (n : ℤ) 1) := by
  have h : polynomialCoordinates P p (n : ℤ) 1
      (restrictValue (projectiveTwist P p (n : ℤ)).sheaf le_top
        (sectionValue (oneGeneratorSection P p n))) = 1 := by
    rw [← algebraicMatchingEquiv_snd, oneGeneratorSection,
      AddEquiv.apply_symm_apply]
    rfl
  have hr := section_app_one_restrict (oneGeneratorSection P p n)
    (homOfLE (show chartOpen 1 ≤ ⊤ from le_top))
  change restrictValue (projectiveTwist P p (n : ℤ)).sheaf le_top
    (sectionValue (oneGeneratorSection P p n)) =
      (Scheme.Modules.Hom.app (oneGeneratorSection P p n)) (chartOpen 1) (1 : RingSections lineScheme (chartOpen 1)) at hr
  rw [hr] at h
  apply (polynomialCoordinates P p (n : ℤ) 1).injective
  rw [polynomialCoordinates_generator]
  exact h

/-- Two actual sections generate every nonnegative twist in the precise
GeneratingSections sense, with the chosen frame generator on each chart. -/
def generatingSections (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) (n : ℕ) :
    SheafOfModules.GeneratingSections (projectiveTwist P p (n : ℤ)).sheaf :=
  generatorsOfLocalFrames chartOpen chartOpen_cover
    (Fin.cases (zeroGeneratorSection P p n) (fun _ => oneGeneratorSection P p n))
    (fun i => twistOverFrame P p (n : ℤ) i) (by
      intro i
      fin_cases i
      · exact zeroGeneratorSection_app_one P p n
      · exact oneGeneratorSection_app_one P p n)

/-- The original global-generation criterion, proved with the actual free
sheaf epimorphism and actual negative-section vanishing. -/
theorem globallyGenerated_iff (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (d : ℤ) : IsGloballyGenerated (projectiveTwist P p d).sheaf ↔ 0 ≤ d := by
  constructor
  · intro h
    by_contra hd
    exact not_globallyGenerated_of_section_vanishing
      (P1TwistSections.identity_ne_zero P p d)
      (P1TwistSections.algebraicSection_eq_zero_of_negative P p d (lt_of_not_ge hd)) h
  · intro hd
    rw [← Int.toNat_of_nonneg hd]
    exact ⟨generatingSections P p d.toNat⟩

end LeBrunSalamon.P1TwistGeneration

end
/- END UNCOMPILED continuation twist_global_generation.lean.txt -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.P1Charts LeBrunSalamon.P1TwistFrames
open LeBrunSalamon.LocalFrames
open scoped LaurentPolynomial

namespace LeBrunSalamon.P1PicardTranslation

/-- The supplied line sheaf is trivial on each actual polynomial chart.
Restriction is compared with pullback before the generic UFD theorem is used.
-/
def chartFrame (L : LineBundle ProjectiveLine) (i : Fin 2) :
    OverFrame L.sheaf (chartOpen i) := by
  let j := polynomialChartInclusion i
  let F := pullbackModule j L.sheaf
  let e : structureModule (Spec (CommRingCat.of (Polynomial ℂ))) ≅ F :=
    Classical.choice (PublishedInputs.Picard.affineUFD_trivial (Polynomial ℂ) F
      (pullback_locallyFree j L.locallyFree))
  let ep : structureModule (Spec (CommRingCat.of (Polynomial ℂ))) ≅
      L.sheaf.restrict j :=
    e ≪≫ ((Scheme.Modules.restrictFunctorIsoPullback j).app L.sheaf).symm
  let eo : structureModule (chartOpen i).toScheme ≅
      L.sheaf.restrict (chartOpen i).ι :=
    (P1Ideal.restrictTrivial_of_iso L.sheaf (chartOpen i).ι j
      (polynomialChartIso i) (polynomialChartIso_hom_inclusion i) ep.symm).symm
  exact ofOpenFrame (chartOpen i) eo

/-- Restriction preserves the comparison of two specified frames. -/
theorem restrict_comparison {X : Scheme} {E F : X.Modules} {U V : X.Opens}
    (i : V ⟶ U) (e : OverFrame E U) (f : OverFrame F U) :
    P1Ideal.restrictOverIso i (e.symm ≪≫ f) =
      (restrict i e).symm ≪≫ restrict i f := by
  apply Iso.ext
  simp [P1Ideal.restrictOverIso, restrict, Functor.map_comp, Category.assoc]

/-- Equality of the actual transition functions gives equality of the actual
frame-comparison maps on every smaller open, by their naturality. -/
theorem comparison_eq_of_transition {X : Scheme} {E F : X.Modules} {U : X.Opens}
    (e e' : OverFrame E U) (f f' : OverFrame F U)
    (h : transition e e' = transition f f') : e.symm ≪≫ f = e'.symm ≪≫ f' := by
  apply Iso.ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  let j : W.unop ⟶ Over.mk (𝟙 U) := Over.homMk W.unop.hom
  have ht := congrArg
    (fun a => (X.sheaf.over U).obj.map j.op a) h
  change (X.sheaf.over U).obj.map j.op
      (Generic.transition (R := X.sheaf.over U) e e' (Over.mk (𝟙 U))) =
    (X.sheaf.over U).obj.map j.op
      (Generic.transition (R := X.sheaf.over U) f f' (Over.mk (𝟙 U))) at ht
  rw [Generic.transition_naturality, Generic.transition_naturality] at ht
  apply (Generic.coordinates (R := X.sheaf.over U) f W.unop).injective
  change Generic.coordinates (R := X.sheaf.over U) f W.unop
      ((Generic.coordinates (R := X.sheaf.over U) f W.unop).symm
        (Generic.coordinates (R := X.sheaf.over U) e W.unop x)) =
    Generic.coordinates (R := X.sheaf.over U) f W.unop
      ((Generic.coordinates (R := X.sheaf.over U) f' W.unop).symm
        (Generic.coordinates (R := X.sheaf.over U) e' W.unop x))
  rw [LinearEquiv.apply_symm_apply,
    Generic.coordinates_change (R := X.sheaf.over U) e e',
    Generic.coordinates_change (R := X.sheaf.over U) f f',
    LinearEquiv.apply_symm_apply, ht]

/-- Two actual over-site isomorphisms glue from one overlap equation. -/
def glueOverPairIso {X : Scheme} {E F : X.Modules} (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (eU : E.over U ≅ F.over U) (eV : E.over V ≅ F.over V)
    (h : P1Ideal.restrictOverIso (homOfLE (inf_le_left : U ⊓ V ≤ U)) eU =
      P1Ideal.restrictOverIso (homOfLE (inf_le_right : U ⊓ V ≤ V)) eV) : E ≅ F := by
  let O : Fin 2 → X.Opens := Fin.cases U (fun _ => V)
  have hc : iSup O = ⊤ := by
    apply le_antisymm le_top
    rw [← hcover]
    exact sup_le (le_iSup O 0) (le_iSup O 1)
  let e : ∀ i, E.over (O i) ≅ F.over (O i) := Fin.cases eU (fun _ => eV)
  apply P1Ideal.glueOverIso O hc e
  intro i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact h
  · change P1Ideal.restrictOverIso (homOfLE (inf_le_left : V ⊓ U ≤ V)) eV =
      P1Ideal.restrictOverIso (homOfLE (inf_le_right : V ⊓ U ≤ U)) eU
    have hs : ∀ (Z : X.Opens) (hZV : Z ≤ V) (hZU : Z ≤ U), Z = U ⊓ V →
        P1Ideal.restrictOverIso (homOfLE hZV) eV =
          P1Ideal.restrictOverIso (homOfLE hZU) eU := by
      intro Z hZV hZU hZ
      subst Z
      exact h.symm
    exact hs (V ⊓ U) inf_le_left inf_le_right (inf_comm V U)
  · rfl

def isoOfTransition {X : Scheme} {E F : X.Modules} (U V : X.Opens)
    (hcover : U ⊔ V = ⊤)
    (e₀ : OverFrame E U) (e₁ : OverFrame E V)
    (f₀ : OverFrame F U) (f₁ : OverFrame F V)
    (h : transition (restrict (homOfLE inf_le_left) e₀)
        (restrict (homOfLE inf_le_right) e₁) =
      transition (restrict (homOfLE inf_le_left) f₀)
        (restrict (homOfLE inf_le_right) f₁)) : E ≅ F :=
  glueOverPairIso U V hcover (e₀.symm ≪≫ f₀) (e₁.symm ≪≫ f₁) (by
    rw [restrict_comparison, restrict_comparison]
    exact comparison_eq_of_transition _ _ _ _ h)

/-- Rescale a specified frame by a genuine global constant automorphism. -/
def scaleFrame {E : ProjectiveLine.Modules} {U : ProjectiveLine.Opens}
    (e : OverFrame E U) (c : ℂˣ) : OverFrame E U :=
  e ≪≫ (SheafOfModules.overFunctor ProjectiveLine.ringCatSheaf U).mapIso
    (P1Endomorphisms.complexScalarIso E c)

theorem restricted_scale_transition {E : ProjectiveLine.Modules}
    (e₀ : OverFrame E (chartOpen 0)) (e₁ : OverFrame E (chartOpen 1)) (c : ℂˣ) :
    transition (restrict (homOfLE inf_le_left) (scaleFrame e₀ c))
        (restrict (homOfLE inf_le_right) e₁) =
      ProjectiveLine.presheaf.map (homOfLE le_top).op
        (P1Endomorphisms.canonicalConstantRingHom (c.inv)) *
      transition (restrict (homOfLE inf_le_left) e₀)
        (restrict (homOfLE inf_le_right) e₁) := by
  change e₀.inv.val.app (op (Over.mk (homOfLE inf_le_left)))
      ((GlobalScalars.scalarEnd E
        (P1Endomorphisms.canonicalConstantRingHom c.inv)).app
          (chartOpen 0 ⊓ chartOpen 1)
          (generator (restrict (homOfLE inf_le_right) e₁))) = _
  rw [GlobalScalars.scalarEnd_app]
  exact (e₀.inv.val.app (op (Over.mk (homOfLE inf_le_left)))).hom.map_smul _ _

theorem overlap_constant (c : ℂ) :
    overlapRingCoordinates (ProjectiveLine.presheaf.map (homOfLE le_top).op
      (P1Endomorphisms.canonicalConstantRingHom c)) = LaurentPolynomial.C c := by
  have h := polynomialChartRingEquiv_canonical_constant 0 c
  let r := P1Endomorphisms.canonicalConstantRingHom c
  change polynomialChartRingEquiv 0
    (ProjectiveLine.presheaf.map (homOfLE le_top).op r) = Polynomial.C c at h
  change overlapRingCoordinates (ProjectiveLine.presheaf.map (homOfLE le_top).op r) = _
  calc
    _ = overlapRingCoordinates (ProjectiveLine.presheaf.map (homOfLE inf_le_left).op
        (ProjectiveLine.presheaf.map
          (homOfLE (show chartOpen 0 ≤ ⊤ from le_top)).op r)) := by
      congr 1
    _ = zeroRestrictionRingHom (polynomialChartRingEquiv 0
        (ProjectiveLine.presheaf.map (homOfLE le_top).op r)) := by
      change _ = overlapRingCoordinates (ProjectiveLine.presheaf.map
        (homOfLE inf_le_left).op ((polynomialChartRingEquiv 0).symm
          (polynomialChartRingEquiv 0
            (ProjectiveLine.presheaf.map (homOfLE le_top).op r))))
      rw [RingEquiv.symm_apply_apply]
    _ = zeroRestrictionRingHom (Polynomial.C c) := congrArg zeroRestrictionRingHom h
    _ = LaurentPolynomial.C c := by
      rw [zeroRestrictionRingHom_eq_toLaurent, Polynomial.toLaurent_C]

/-- The old Picard admission, now proved by two affine frames, the Laurent-unit
calculation, a specified scalar normalization, and actual sheaf gluing. -/
theorem lineBundleClassification (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (L : LineBundle ProjectiveLine) :
    ∃! d : ℤ, Nonempty (L.sheaf ≅ (projectiveTwist P p d).sheaf) := by
  let e₀ := chartFrame L 0
  let e₁ := chartFrame L 1
  let t := transitionUnit (restrict (homOfLE inf_le_left) e₀)
    (restrict (homOfLE inf_le_right) e₁)
  have ht : IsUnit (overlapRingCoordinates (t : RingSections ProjectiveLine
      (chartOpen 0 ⊓ chartOpen 1))) := t.isUnit.map overlapRingCoordinates.toRingHom
  obtain ⟨c, d, hc, hcd⟩ := P1Overlap.unit_is_monomial _ ht
  let u : ℂˣ := Units.mk0 c hc
  have htransition :
      transition (restrict (homOfLE inf_le_left) (scaleFrame e₀ u))
          (restrict (homOfLE inf_le_right) e₁) =
        transition (restrict (homOfLE inf_le_left) (twistOverFrame P p d 0))
          (restrict (homOfLE inf_le_right) (twistOverFrame P p d 1)) := by
    apply overlapRingCoordinates.injective
    rw [restricted_scale_transition, map_mul, overlap_constant]
    change LaurentPolynomial.C (u.inv) * overlapRingCoordinates (t.val) = _
    rw [hcd]
    change LaurentPolynomial.C c⁻¹ *
      (LaurentPolynomial.C c * LaurentPolynomial.T d) = (laurentTransitionUnit P p d).val
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul,
      laurentTransitionUnit_eq_T]
  let e := isoOfTransition (chartOpen 0) (chartOpen 1) chartOpen_zero_sup_one
    (scaleFrame e₀ u) e₁ (twistOverFrame P p d 0) (twistOverFrame P p d 1) htransition
  refine ⟨d, ⟨e⟩, ?_⟩
  intro k hk
  obtain ⟨ek⟩ := hk
  exact P1TwistSections.exponent_eq_of_iso P p k d (ek.symm ≪≫ e)

end LeBrunSalamon.P1PicardTranslation

end

namespace LeBrunSalamon.PhaseThirtyTwo

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseEighteen
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight

/-- Picard classification in the project's actual marked-point twist convention,
proved by the two affine frames and their Laurent transition normalization. -/
theorem _root_.LeBrunSalamon.PublishedInputs.ProjectiveLineGeometry.lineBundleClassification
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (L : LineBundle ProjectiveLine) :
    ∃! d : ℤ, Nonempty (L.sheaf ≅ (projectiveTwist P p d).sheaf) := by
  exact LeBrunSalamon.P1PicardTranslation.lineBundleClassification P p L

/-- Project wrapper for the Picard classification of `P¹`. -/
theorem projectiveLineBundle_classification (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (L : LineBundle ProjectiveLine) :
    ∃! d : ℤ, Nonempty (L.sheaf ≅ (projectiveTwist P p d).sheaf) :=
  LeBrunSalamon.PublishedInputs.ProjectiveLineGeometry.lineBundleClassification
    P p L

theorem projectiveTwist_iso_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (a b : ℤ) :
    Nonempty ((projectiveTwist P p a).sheaf ≅
      (projectiveTwist P p b).sheaf) ↔ a = b := by
  constructor
  · rintro ⟨e⟩
    exact P1TwistSections.exponent_eq_of_iso P p a b e
  · rintro rfl
    exact ⟨Iso.refl _⟩

/-- Degree is the unique exponent of O(1), not an extra label. -/
def projectiveLineDegree (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (L : LineBundle ProjectiveLine) : ℤ :=
  Classical.choose (projectiveLineBundle_classification P p L)

theorem projectiveLineDegree_spec (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (L : LineBundle ProjectiveLine) :
    Nonempty (L.sheaf ≅ (projectiveTwist P p (projectiveLineDegree P p L)).sheaf) := by
  exact (Classical.choose_spec (projectiveLineBundle_classification P p L)).1

theorem projectiveLineDegree_iso (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (L M : LineBundle ProjectiveLine)
    (e : L.sheaf ≅ M.sheaf) :
    projectiveLineDegree P p L = projectiveLineDegree P p M := by
  obtain ⟨hM⟩ := projectiveLineDegree_spec P p M
  exact (projectiveLineBundle_classification P p L).unique
    (projectiveLineDegree_spec P p L) ⟨e.trans hM⟩

theorem projectiveLineDegree_independent (P : ProjectiveLineOverC)
    (p q : ProjectiveLinePoint P) (L : LineBundle ProjectiveLine) :
    projectiveLineDegree P p L = projectiveLineDegree P q L := by
  obtain ⟨eL⟩ := projectiveLineDegree_spec P q L
  obtain ⟨e⟩ := projectiveTwist_independent P q p (projectiveLineDegree P q L)
  exact (projectiveLineBundle_classification P p L).unique
    (projectiveLineDegree_spec P p L) ⟨eL ≪≫ e⟩

theorem projectiveLineDegree_tensor (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (L M : LineBundle ProjectiveLine) :
    projectiveLineDegree P p (tensorLine L M) =
      projectiveLineDegree P p L + projectiveLineDegree P p M := by
  obtain ⟨eL⟩ := projectiveLineDegree_spec P p L
  obtain ⟨eM⟩ := projectiveLineDegree_spec P p M
  obtain ⟨eadd⟩ := projectiveTwist_add P p (projectiveLineDegree P p L) (projectiveLineDegree P p M)
  exact (projectiveLineBundle_classification P p (tensorLine L M)).unique
    (projectiveLineDegree_spec P p _) ⟨(tensorIso eL eM).trans eadd⟩

theorem projectiveLineDegree_dual (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (L : LineBundle ProjectiveLine) :
    projectiveLineDegree P p (dualLine L) = -projectiveLineDegree P p L := by
  obtain ⟨eL⟩ := projectiveLineDegree_spec P p L
  obtain ⟨eD⟩ := projectiveTwist_dual P p (projectiveLineDegree P p L)
  exact (projectiveLineBundle_classification P p (dualLine L)).unique
    (projectiveLineDegree_spec P p (dualLine L))
    ⟨LineBundleClasses.dualCongrIso
      (L := L) (M := projectiveTwist P p (projectiveLineDegree P p L)) eL ≪≫ eD⟩

theorem projectiveTwist_degree (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    projectiveLineDegree P p (projectiveTwist P p d) = d := by
  exact (projectiveLineBundle_classification P p (projectiveTwist P p d)).unique
    (projectiveLineDegree_spec P p _) ⟨Iso.refl _⟩

theorem projectiveLineDegree_power (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (L : LineBundle ProjectiveLine) (k : ℕ) :
    projectiveLineDegree P p (linePower L k) =
      (k : ℤ) * projectiveLineDegree P p L := by
  induction k with
  | zero =>
    simpa [projectiveTwist, linePowerInt, linePower] using projectiveTwist_degree P p 0
  | succ k ih =>
    rw [linePower, projectiveLineDegree_tensor, ih]
    push_cast
    ring

theorem projectiveTwist_globallyGenerated_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) :
    IsGloballyGenerated (projectiveTwist P p d).sheaf ↔ 0 ≤ d := by
  exact P1TwistGeneration.globallyGenerated_iff P p d

theorem negativeTwist_noSections (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (d : ℤ) (hd : d < 0)
    (s : AlgebraicSection (projectiveTwist P p d).sheaf) : s = 0 := by
  exact P1TwistSections.algebraicSection_eq_zero_of_negative P p d hd s

theorem descendingDegree_noHom (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (a b : ℤ) (h : b < a)
    (f : (projectiveTwist P p a).sheaf ⟶ (projectiveTwist P p b).sheaf) :
    f = 0 := by
  obtain ⟨e⟩ := projectiveTwist_internalHom P p a b
  exact TwoChartSections.hom_eq_zero_of_section_vanishing e
    (fun s => negativeTwist_noSections P p (b - a) (by omega) s) f

theorem equalDegree_nonzeroHom_isIso (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (a : ℤ)
    (f : (projectiveTwist P p a).sheaf ⟶ (projectiveTwist P p a).sheaf)
    (hf : f ≠ 0) : IsIso f := by
  exact P1Endomorphisms.nonzero_endomorphism_isIso P p a f hf


section

set_option backward.isDefEq.respectTransparency false
open LeBrunSalamon.Skeleton LeBrunSalamon.P1Charts
attribute [local instance] MvPolynomial.gradedAlgebra

namespace CotangentTwistProof

/-- The actual change from canonical constants to the supplied base map. -/
def baseChangeIso (P : ProjectiveLineOverC) : ComplexBase ≅ ComplexBase :=
  (zeroDegreeSchemeIso 1).symm ≪≫ P.zeroDegreeIso

theorem baseMap_factor (P : ProjectiveLineOverC) :
    canonicalBaseMap ≫ (baseChangeIso P).hom = P.structureMap := by
  change (Proj.toSpecZero grading ≫ (zeroDegreeSchemeIso 1).hom) ≫
      ((zeroDegreeSchemeIso 1).inv ≫ P.zeroDegreeIso.hom) =
    Proj.toSpecZero grading ≫ P.zeroDegreeIso.hom
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The actual polynomial coefficient morphism is smooth of dimension one. -/
theorem polynomialC_smooth : SmoothOfRelativeDimension 1
    (Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ))) := by
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1 ℂ (Polynomial ℂ) :=
    Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
      (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1))
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  change RingHom.IsStandardSmoothOfRelativeDimension 1 (algebraMap ℂ (Polynomial ℂ))
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr inferInstance

/-- Source locality glues the two actual polynomial charts. -/
theorem canonicalBaseMap_smooth : SmoothOfRelativeDimension 1 canonicalBaseMap := by
  apply IsZariskiLocalAtSource.of_iSup_eq_top chartOpen chartOpen_cover
  intro i
  apply (MorphismProperty.cancel_left_of_respectsIso
    (@SmoothOfRelativeDimension 1) (polynomialChartIso i).inv
    ((chartOpen i).ι ≫ canonicalBaseMap)).mp
  rw [← Category.assoc]
  change SmoothOfRelativeDimension 1 (polynomialChartInclusion i ≫ canonicalBaseMap)
  rw [polynomialChartInclusion_baseMap]
  exact polynomialC_smooth

/-- The supplied base isomorphism preserves relative dimension one. -/
theorem structureMap_smooth (P : ProjectiveLineOverC) :
    SmoothOfRelativeDimension 1 P.structureMap := by
  rw [← baseMap_factor P]
  exact (MorphismProperty.cancel_right_of_respectsIso
    (@SmoothOfRelativeDimension 1) canonicalBaseMap (baseChangeIso P).hom).mpr
      canonicalBaseMap_smooth

end CotangentTwistProof

end

end LeBrunSalamon.PhaseThirtyTwo

/-! Actual derivative frames and their transition on the two polynomial
charts of the projective line. This file adds no published input. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.P1Charts LeBrunSalamon.P1TwistFrames
open LeBrunSalamon.LocalFrames LeBrunSalamon.P1PicardTranslation
open LeBrunSalamon.Skeleton
open scoped LaurentPolynomial

namespace LeBrunSalamon.P1TangentTranslation

def transportedDerivative {R : Type*} [CommRing R] (e : R ≃+* Polynomial ℂ)
    (a : R) : R := e.symm (e a).derivative

theorem transportedDerivative_zero {R : Type*} [CommRing R]
    (e : R ≃+* Polynomial ℂ) : transportedDerivative e 0 = 0 := by
  simp only [transportedDerivative, map_zero, Polynomial.derivative_zero]

theorem transportedDerivative_add {R : Type*} [CommRing R]
    (e : R ≃+* Polynomial ℂ) (a b : R) :
    transportedDerivative e (a + b) =
      transportedDerivative e a + transportedDerivative e b := by
  simp only [transportedDerivative, map_add, Polynomial.derivative_add]

theorem transportedDerivative_mul {R : Type*} [CommRing R]
    (e : R ≃+* Polynomial ℂ) (a b : R) :
    transportedDerivative e (a * b) =
      a * transportedDerivative e b + b * transportedDerivative e a := by
  simp only [transportedDerivative, map_mul, Polynomial.derivative_mul,
    map_add, RingEquiv.symm_apply_apply]
  ac_rfl

theorem derivation_reciprocal {R : Type*} [CommRing R]
    (D : R → R) (hmul : ∀ a b, D (a * b) = a * D b + b * D a)
    (z w : R) (hzw : z * w = 1) (hw : D w = 1) : D z = -(z ^ 2) := by
  have h1 : D 1 = 0 := by
    have h := hmul 1 1
    simp only [one_mul] at h
    linear_combination -h
  have h := hmul z w
  rw [hzw, h1, hw, mul_one] at h
  have hz := congrArg (fun a : R => z * a) h
  rw [mul_zero, mul_add, ← mul_assoc, hzw, one_mul] at hz
  linear_combination -hz

theorem unit_of_left_inverse {R : Type*} [CommRing R] (a b : R)
    (h : a * b = 1) : IsUnit b := by
  refine ⟨⟨b, a, ?_, h⟩, rfl⟩
  rw [mul_comm]
  exact h

def tangentLine (P : ProjectiveLineOverC) : LineBundle ProjectiveLine :=
  ⟨tangentSheaf P.structureMap,
    smooth_tangent_rank P.structureMap 1 (CotangentTwistProof.structureMap_smooth P)⟩

def coordinate (i : Fin 2) : RingSections ProjectiveLine (chartOpen i) :=
  (polynomialChartRingEquiv i).symm Polynomial.X

/-- A change of the supplied complex base isomorphism still maps constants
to constant polynomials on each actual affine chart. -/
theorem base_constants_polynomial (P : ProjectiveLineOverC) (i : Fin 2) (c : ℂ) :
    ∃ d : ℂ, polynomialChartRingEquiv i (complexConstant P.structureMap (chartOpen i) c) =
      Polynomial.C d := by
  let A := CotangentTwistProof.baseChangeIso P
  let d := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    (A.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))
  refine ⟨d, ?_⟩
  have hd : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv d =
      A.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) :=
    Iso.hom_inv_id_apply _ _
  rw [complexConstant, ← CotangentTwistProof.baseMap_factor P,
    Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply]
  rw [← hd]
  exact polynomialChartRingEquiv_canonical_constant i d

/-- The ordinary polynomial derivative realizes an actual local tangent
section, for every allowed complex base map. -/
theorem coordinate_vector_exists (P : ProjectiveLineOverC) (i : Fin 2) :
    ∃ v : SectionsOn (tangentSheaf P.structureMap) (chartOpen i),
      tangentActs P.structureMap (chartOpen i) v (coordinate i) = 1 := by
  let e := polynomialChartRingEquiv i
  let D := transportedDerivative e
  obtain ⟨v, hv⟩ := TangentAffine.affine_tangent_action_exists P.structureMap
    (chartOpen i) (chartOpen_affine i) D
    (transportedDerivative_zero e)
    (transportedDerivative_add e)
    (transportedDerivative_mul e)
    (by
      intro c
      obtain ⟨d, hd⟩ := base_constants_polynomial P i c
      change e.symm (e (complexConstant P.structureMap (chartOpen i) c)).derivative = 0
      rw [hd, Polynomial.derivative_C, map_zero])
  refine ⟨v, ?_⟩
  rw [hv]
  change e.symm (e (e.symm Polynomial.X)).derivative = 1
  rw [RingEquiv.apply_symm_apply, Polynomial.derivative_X, map_one]

/-- A chosen frame's derivative coefficient is an actual unit, since d/dz
exists and every vector is its frame coordinate times the frame generator. -/
theorem frame_coordinate_unit (P : ProjectiveLineOverC) (i : Fin 2)
    (e : OverFrame (tangentSheaf P.structureMap) (chartOpen i)) :
    IsUnit (tangentActs P.structureMap (chartOpen i) (generator e) (coordinate i)) := by
  obtain ⟨v, hv⟩ := coordinate_vector_exists P i
  have hmul : coordinates e v *
      tangentActs P.structureMap (chartOpen i) (generator e) (coordinate i) = 1 := by
    rw [← TangentActionProof.smul_field, reconstruct]
    exact hv
  exact unit_of_left_inverse _ _ hmul

/-- Units on Spec C[z] are nonzero constants. -/
theorem frame_coordinate_constant (P : ProjectiveLineOverC) (i : Fin 2)
    (e : OverFrame (tangentSheaf P.structureMap) (chartOpen i)) :
    ∃ c : ℂ, c ≠ 0 ∧
      polynomialChartRingEquiv i
        (tangentActs P.structureMap (chartOpen i) (generator e) (coordinate i)) =
          Polynomial.C c := by
  have h := (frame_coordinate_unit P i e).map (polynomialChartRingEquiv i).toRingHom
  obtain ⟨c, hc, he⟩ := Polynomial.isUnit_iff.mp h
  exact ⟨c, hc.ne_zero, he.symm⟩

theorem generator_scaleFrame {E : ProjectiveLine.Modules} {U : ProjectiveLine.Opens}
    (e : OverFrame E U) (c : ℂˣ) :
    generator (scaleFrame e c) = ProjectiveLine.presheaf.map
      (homOfLE (show U ≤ ⊤ from le_top)).op
      (P1Endomorphisms.canonicalConstantRingHom c.val) • generator e := by
  rfl

/-- Normalize the derivative coefficient to one using the proved global
constant automorphism, without changing the local tangent sheaf. -/
theorem normalized_frame_exists (P : ProjectiveLineOverC) (i : Fin 2) :
    ∃ e : OverFrame (tangentSheaf P.structureMap) (chartOpen i),
      tangentActs P.structureMap (chartOpen i) (generator e) (coordinate i) = 1 := by
  let e : OverFrame (tangentSheaf P.structureMap) (chartOpen i) :=
    chartFrame (tangentLine P) i
  obtain ⟨c, hc, he⟩ := frame_coordinate_constant P i e
  let u : ℂˣ := (Units.mk0 c hc)⁻¹
  refine ⟨scaleFrame e u, ?_⟩
  rw [generator_scaleFrame, TangentActionProof.smul_field]
  apply (polynomialChartRingEquiv i).injective
  have hu : polynomialChartRingEquiv i
      (ProjectiveLine.presheaf.map (homOfLE (show chartOpen i ≤ ⊤ from le_top)).op
        (P1Endomorphisms.canonicalConstantRingHom u.val)) = Polynomial.C u.val :=
    polynomialChartRingEquiv_canonical_constant i u.val
  rw [map_mul, hu, he, ← map_mul, map_one]
  change Polynomial.C (c⁻¹ * c) = 1
  rw [inv_mul_cancel₀ hc, map_one]

def derivativeFrame (P : ProjectiveLineOverC) (i : Fin 2) :
    OverFrame (tangentSheaf P.structureMap) (chartOpen i) :=
  (normalized_frame_exists P i).choose

theorem derivativeFrame_coordinate (P : ProjectiveLineOverC) (i : Fin 2) :
    tangentActs P.structureMap (chartOpen i) (generator (derivativeFrame P i))
      (coordinate i) = 1 := (normalized_frame_exists P i).choose_spec

abbrev overlap : ProjectiveLine.Opens := chartOpen 0 ⊓ chartOpen 1
def z : RingSections ProjectiveLine overlap :=
  ProjectiveLine.presheaf.map (homOfLE inf_le_left).op (coordinate 0)
def w : RingSections ProjectiveLine overlap :=
  ProjectiveLine.presheaf.map (homOfLE inf_le_right).op (coordinate 1)

theorem z_laurent : overlapRingCoordinates z = LaurentPolynomial.T 1 := by
  change zeroRestrictionRingHom Polynomial.X = _
  rw [zeroRestrictionRingHom_eq_toLaurent, Polynomial.toLaurent_X]

theorem w_laurent : overlapRingCoordinates w = LaurentPolynomial.T (-1) := by
  change oneRestrictionRingHom Polynomial.X = _
  rw [oneRestrictionRingHom_eq_invert_toLaurent, RingHom.comp_apply,
    Polynomial.toLaurent_X]
  exact LaurentPolynomial.invert_T 1

theorem z_mul_w : z * w = 1 := by
  apply overlapRingCoordinates.injective
  rw [map_mul, z_laurent, w_laurent, ← LaurentPolynomial.T_add, map_one]
  norm_num

def frameZero (P : ProjectiveLineOverC) : OverFrame (tangentSheaf P.structureMap) overlap :=
  restrict (homOfLE inf_le_left) (derivativeFrame P 0)

def frameOne (P : ProjectiveLineOverC) : OverFrame (tangentSheaf P.structureMap) overlap :=
  restrict (homOfLE inf_le_right) (derivativeFrame P 1)

theorem frameZero_z (P : ProjectiveLineOverC) :
    tangentActs P.structureMap overlap (generator (frameZero P)) z = 1 := by
  rw [frameZero, ← generator_restrict, z, ← TangentActionProof.naturality,
    derivativeFrame_coordinate, map_one]

theorem frameOne_w (P : ProjectiveLineOverC) :
    tangentActs P.structureMap overlap (generator (frameOne P)) w = 1 := by
  rw [frameOne, ← generator_restrict, w, ← TangentActionProof.naturality,
    derivativeFrame_coordinate, map_one]

/-- The actual coordinate change w=z⁻¹ gives d/dw=-z² d/dz. -/
theorem frameOne_z (P : ProjectiveLineOverC) :
    tangentActs P.structureMap overlap (generator (frameOne P)) z = -(z ^ 2) := by
  exact derivation_reciprocal
    (tangentActs P.structureMap overlap (generator (frameOne P)))
    (tangentActs_leibniz P.structureMap overlap (generator (frameOne P)))
    z w z_mul_w (frameOne_w P)

theorem derivative_transition (P : ProjectiveLineOverC) :
    overlapRingCoordinates (transition (frameZero P) (frameOne P)) =
      -LaurentPolynomial.T 2 := by
  have h := congrArg (fun v => tangentActs P.structureMap overlap v z)
    (reconstruct (frameZero P) (generator (frameOne P)))
  rw [TangentActionProof.smul_field, frameZero_z, mul_one, frameOne_z] at h
  change transition (frameZero P) (frameOne P) = -(z ^ 2) at h
  rw [h, map_neg, map_pow, z_laurent, LaurentPolynomial.T_pow]
  norm_num

/-- Exact agreement of the two transition functions after the sign change. -/
theorem normalized_transition (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (d : ℤ) (hd : d = 2) :
    transition
      (restrict (homOfLE inf_le_left) (scaleFrame (derivativeFrame P 0) (-1)))
      (restrict (homOfLE inf_le_right) (derivativeFrame P 1)) =
    transition
      (restrict (homOfLE inf_le_left) (twistOverFrame P p d 0))
      (restrict (homOfLE inf_le_right) (twistOverFrame P p d 1)) := by
  let c : ℂˣ := -1
  apply overlapRingCoordinates.injective
  rw [restricted_scale_transition, map_mul, overlap_constant]
  change LaurentPolynomial.C (c.inv) *
    overlapRingCoordinates (transition (frameZero P) (frameOne P)) =
      (laurentTransitionUnit P p d).val
  rw [derivative_transition, laurentTransitionUnit_eq_T, hd]
  simp [c]

/-- Glue the normalized derivative frames to the project's actual O(2)
frames, including the sign from the reciprocal coordinate change. -/
def tangentTwistIsoAt (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (d : ℤ) (hd : d = 2) :
    tangentSheaf P.structureMap ≅ (projectiveTwist P p d).sheaf :=
  isoOfTransition (E := tangentSheaf P.structureMap)
    (F := (projectiveTwist P p d).sheaf)
    (chartOpen 0) (chartOpen 1) chartOpen_zero_sup_one
    (scaleFrame (derivativeFrame P 0) (-1)) (derivativeFrame P 1)
    (twistOverFrame P p d 0) (twistOverFrame P p d 1) (normalized_transition P p d hd)

def tangentTwistIso (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) :
    tangentSheaf P.structureMap ≅ (projectiveTwist P p 2).sheaf :=
  tangentTwistIsoAt P p 2 rfl

theorem tangentTwist (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) :
    Nonempty (tangentSheaf P.structureMap ≅ (projectiveTwist P p 2).sheaf) :=
  ⟨tangentTwistIso P p⟩

end LeBrunSalamon.P1TangentTranslation

end

namespace LeBrunSalamon.PhaseThirtyTwo

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseEighteen
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight

/-- Actual derivative-frame proof of the marked tangent twist. -/
theorem _root_.LeBrunSalamon.PublishedInputs.ProjectiveLineGeometry.tangentTwist
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) :
    Nonempty (tangentSheaf P.structureMap ≅ (projectiveTwist P p 2).sheaf) := by
  exact LeBrunSalamon.P1TangentTranslation.tangentTwist P p

/-- Project wrapper for `T_{P¹} ≅ O(2)`. -/
theorem projectiveLine_tangent_twist (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) :
    Nonempty (tangentSheaf P.structureMap ≅ (projectiveTwist P p 2).sheaf) :=
  LeBrunSalamon.PublishedInputs.ProjectiveLineGeometry.tangentTwist P p


set_option backward.isDefEq.respectTransparency false in
theorem projectiveLine_cotangent_twist (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) :
    Nonempty (cotangentSheaf P.structureMap ≅ (projectiveTwist P p (-2)).sheaf) := by
  have hΩ : IsLocallyFreeOfRank (cotangentSheaf P.structureMap) 1 :=
    smooth_cotangent_rank P.structureMap 1 (CotangentTwistProof.structureMap_smooth P)
  obtain ⟨eBidual⟩ := locallyFree_doubleDual hΩ
  obtain ⟨eTangent⟩ := projectiveLine_tangent_twist P p
  obtain ⟨eTwistDual⟩ := projectiveTwist_dual P p 2
  let eDual : dualSheaf (tangentSheaf P.structureMap) ≅
      dualSheaf (projectiveTwist P p 2).sheaf :=
    (internalHomPresentation (tangentSheaf P.structureMap)
      (structureModule ProjectiveLine)).mapIso
      (internalHomPresentation (projectiveTwist P p 2).sheaf
        (structureModule ProjectiveLine)) eTangent (Iso.refl _)
  exact ⟨eBidual.symm ≪≫ eDual ≪≫ eTwistDual⟩

/-- The actual finite direct sum of O(a_i), in the sheaf category. -/
def splitSheaf (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) : OModule ProjectiveLine :=
  ∐ (fun i : Fin r => (projectiveTwist P p (a.degree i)).sheaf)

def RealizesSplitting (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (E : AlgebraicVectorBundle ProjectiveLine r)
    (a : TangentSplittingProfile r) : Prop :=
  Nonempty (E.sheaf ≅ splitSheaf P p a)

end LeBrunSalamon.PhaseThirtyTwo

/- BEGIN UNCOMPILED continuation split_bundle_basics.lean.txt -/
/-!
Actual finite sums of twists: rank and global generating sections.

Uncompiled continuation. Insert after the original splitSheaf and
RealizesSplitting definitions, before the original split-bundle targets.
The proof uses actual coproducts, their restriction comparison, and the
original GeneratingSections structure; no bundle classification is used.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseEighteen LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.P1Charts LeBrunSalamon.P1TwistFrames
open scoped BigOperators

namespace LeBrunSalamon.DirectSumGeometry

/-- Global generation is transported by the given actual sheaf isomorphism. -/
theorem globallyGenerated_iso_iff {X : Scheme} {E F : OModule X} (e : E ≅ F) :
    IsGloballyGenerated E ↔ IsGloballyGenerated F := by
  constructor
  · rintro ⟨G⟩
    exact ⟨G.ofEpi e.hom⟩
  · rintro ⟨G⟩
    exact ⟨G.ofEpi e.inv⟩

/-- The union of actual generating families gives actual generators of their
coproduct. Its free map is a coproduct of epis after a free-basis reindexing. -/
def coproductGenerators {X : Scheme} {I : Type} (E : I → OModule X)
    (G : ∀ i, SheafOfModules.GeneratingSections (E i)) :
    SheafOfModules.GeneratingSections (∐ E) := by
  let q : SheafOfModules.free (R := X.ringCatSheaf) (Σ i, (G i).I) ⟶ ∐ E :=
    (sigmaSigmaIso (fun i => (G i).I) (fun _ _ => structureModule X)).inv ≫
      CategoryTheory.Limits.Sigma.map (fun i => (G i).π)
  letI : Epi q := by
    dsimp [q]
    infer_instance
  exact (SheafOfModules.free.generatingSections (Σ i, (G i).I)).ofEpi q

/-- Every summand is an actual epi quotient of the coproduct, and generating
families can be combined in the other direction. The empty family is included. -/
theorem globallyGenerated_coproduct_iff {X : Scheme} {I : Type}
    (E : I → OModule X) : IsGloballyGenerated (∐ E) ↔ ∀ i, IsGloballyGenerated (E i) := by
  classical
  constructor
  · rintro ⟨G⟩ i
    exact ⟨G.ofEpi (Sigma.π E i)⟩
  · intro h
    exact ⟨coproductGenerators E (fun i => Classical.choice (h i))⟩

/-- Chosen frames of the summands on one open give an actual free frame of
their coproduct there. Restriction is the genuine over-site functor. -/
def coproductFrame {X : Scheme} {I : Type} (E : I → OModule X) (U : X.Opens)
    (e : ∀ i, LocalFrames.OverFrame (E i) U) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ (∐ E).over U :=
  Sigma.mapIso e ≪≫
    (PreservesCoproduct.iso (SheafOfModules.overFunctor X.ringCatSheaf U) E).symm

/-- The actual finite coproduct is reconstructed from its coordinate
projections. This equality is in the original module-sheaf category. -/
theorem coproduct_total {X : Scheme} {I : Type} [Fintype I] [DecidableEq I]
    (E : I → OModule X) :
    ∑ i, Sigma.π E i ≫ Sigma.ι E i = 𝟙 (∐ E) := by
  apply Sigma.hom_ext
  intro j
  rw [Preadditive.comp_sum, Category.comp_id, Finset.sum_eq_single j]
  · rw [← Category.assoc, Sigma.ι_π_eq_id, Category.id_comp]
  · intro i _ hij
    rw [← Category.assoc, Sigma.ι_π_of_ne E hij.symm, zero_comp]
  · simp

end LeBrunSalamon.DirectSumGeometry

namespace LeBrunSalamon.P1SplitBundles

/-- The original finite sum of twists has the prescribed rank, including
rank zero, by the already constructed actual frames on the two charts. -/
theorem splitSheaf_rank (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) :
    IsLocallyFreeOfRank (PhaseThirtyTwo.splitSheaf P p a) r := by
  apply SheafTensor.rank_of_free_cover (PhaseThirtyTwo.splitSheaf P p a) r
    chartOpen ((Opens.coversTop_iff ProjectiveLine chartOpen).mpr chartOpen_cover)
  intro j
  exact DirectSumGeometry.coproductFrame
    (fun i : Fin r => (projectiveTwist P p (a.degree i)).sheaf) (chartOpen j)
    (fun i => twistOverFrame P p (a.degree i) j)

/-- The numerical free condition is equivalent to actual global generation
of the original direct sum, without using classification of arbitrary bundles. -/
theorem splitSheaf_globallyGenerated_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (a : TangentSplittingProfile r) :
    IsGloballyGenerated (PhaseThirtyTwo.splitSheaf P p a) ↔ a.IsFree := by
  rw [PhaseThirtyTwo.splitSheaf, DirectSumGeometry.globallyGenerated_coproduct_iff]
  exact forall_congr' (fun i => projectiveTwist_globallyGenerated_iff P p (a.degree i))

/-- Transport along the given actual splitting closes the original bundle
criterion. No Birkhoff--Grothendieck existence theorem enters this proof. -/
theorem splitBundle_globallyGenerated_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ}
    (E : AlgebraicVectorBundle ProjectiveLine r) (a : TangentSplittingProfile r)
    (ha : RealizesSplitting P p E a) :
    IsGloballyGenerated E.sheaf ↔ a.IsFree := by
  obtain ⟨e⟩ := ha
  exact (DirectSumGeometry.globallyGenerated_iso_iff e).trans
    (splitSheaf_globallyGenerated_iff P p a)

end LeBrunSalamon.P1SplitBundles

end
/- END UNCOMPILED continuation split_bundle_basics.lean.txt -/

end
