import LSConePole
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Data.Finset.Lattice.Fold

/-!
## Construct the regular coordinate arcs at a maximal pole

SOURCE: `lines:cone-addition`, the paragraph defining `p = t^k a`
and `q = -t^k b`. The Laurent expansions are actual Hahn series over C.
The finite maximum pole order and both regular coordinate vectors are
constructed here. Their common special value is proved nonzero.

The input here explicitly says that one coordinate has negative Laurent
order. `LSAffineCurveSelection` and `LSCurveLaurentGeometry` subsequently
produce these Laurent coordinates from an actual curve in the addition
fiber, using the separately approved classical Laurent-pole input.
`LSConeRescaledArcs` supplies closed-cone factorization and localization
of the regular coordinate arcs constructed here.

SOURCE ONLY, UNCOMPILED. No compiler was invoked while preparing this file.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeBrunSalamon.Construction.Lines.LaurentRescaling

open ConePole

abbrev Meromorphic := LaurentSeries ℂ

/-- The actual inclusion of the complete regular local ring into its
Laurent-series fraction field, with its complex algebra structure. -/
def seriesInclusion : Series →ₐ[ℂ] Meromorphic :=
  { HahnSeries.ofPowerSeries ℤ ℂ with
    commutes' := fun _ => rfl }

theorem seriesInclusion_apply (f : Series) :
    seriesInclusion f = (f : Meromorphic) := rfl

theorem seriesInclusion_injective : Function.Injective seriesInclusion :=
  HahnSeries.ofPowerSeries_injective

@[simp]
theorem seriesInclusion_C (c : ℂ) :
    seriesInclusion (PowerSeries.C c) = algebraMap ℂ Meromorphic c :=
  seriesInclusion.commutes c

theorem seriesInclusion_X_pow (k : ℕ) :
    seriesInclusion ((PowerSeries.X : Series) ^ k) =
      HahnSeries.single (k : ℤ) (1 : ℂ) :=
  HahnSeries.ofPowerSeries_X_pow k

/-- Shift the coefficients by k. Under the explicit lower-order bound
below this is exactly multiplication of the Laurent series by t^k. -/
def regularRescaling (k : ℕ) (a : Meromorphic) : Series :=
  PowerSeries.mk fun m => a.coeff ((m : ℤ) - (k : ℤ))

@[simp]
theorem regularRescaling_coeff (k m : ℕ) (a : Meromorphic) :
    PowerSeries.coeff m (regularRescaling k a) =
      a.coeff ((m : ℤ) - (k : ℤ)) :=
  PowerSeries.coeff_mk _ _

theorem regularRescaling_constantCoeff (k : ℕ) (a : Meromorphic) :
    PowerSeries.constantCoeff (regularRescaling k a) =
      a.coeff (-(k : ℤ)) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, regularRescaling_coeff]
  simp only [Nat.cast_zero, zero_sub]

/-- The coefficient shift has no discarded negative terms once k
cancels the pole. The zero Laurent series is handled by the same proof. -/
theorem seriesInclusion_regularRescaling_single (k : ℕ) (a : Meromorphic)
    (ha : -(k : ℤ) ≤ a.order) :
    seriesInclusion (regularRescaling k a) =
      HahnSeries.single (k : ℤ) (1 : ℂ) * a := by
  apply HahnSeries.ext
  funext m
  change ((regularRescaling k a : Series) : Meromorphic).coeff m =
    (HahnSeries.single (k : ℤ) (1 : ℂ) * a).coeff m
  by_cases hm : 0 ≤ m
  · lift m to ℕ using hm
    rw [LaurentSeries.coeff_coe_powerSeries, regularRescaling_coeff,
      HahnSeries.coeff_single_mul, one_mul]
  · rw [PowerSeries.coeff_coe, if_pos (lt_of_not_ge hm),
      HahnSeries.coeff_single_mul, one_mul]
    symm
    exact HahnSeries.coeff_eq_zero_of_lt_order (by omega)

theorem seriesInclusion_regularRescaling (k : ℕ) (a : Meromorphic)
    (ha : -(k : ℤ) ≤ a.order) :
    seriesInclusion (regularRescaling k a) =
      seriesInclusion (PowerSeries.X : Series) ^ k * a := by
  rw [seriesInclusion_regularRescaling_single k a ha,
    ← seriesInclusion_X_pow, map_pow]

section FiniteCoordinates

variable {ι : Type*} [Fintype ι]

/-- The largest pole among the finitely many actual coordinate functions.
The Laurent order of zero is zero, so zero coordinates add no pole. -/
def maximalPoleOrder (a : ι → Meromorphic) : ℕ :=
  Finset.univ.sup fun i => (-(a i).order).toNat

theorem order_lower_bound (a : ι → Meromorphic) (i : ι) :
    -(maximalPoleOrder a : ℤ) ≤ (a i).order := by
  have hi : (-(a i).order).toNat ≤ maximalPoleOrder a :=
    Finset.le_sup (f := fun j => (-(a j).order).toNat) (Finset.mem_univ i)
  omega

theorem maximalPoleOrder_pos (a : ι → Meromorphic)
    (hpole : ∃ i, (a i).order < 0) : 0 < maximalPoleOrder a := by
  obtain ⟨i, hi⟩ := hpole
  have hb := order_lower_bound a i
  omega

/-- A coordinate actually attains the chosen pole order. This is what
prevents both rescaled special vectors from becoming the cone vertex. -/
theorem exists_coordinate_of_maximalPole (a : ι → Meromorphic)
    (hpole : ∃ i, (a i).order < 0) :
    ∃ i, (a i).order = -(maximalPoleOrder a : ℤ) := by
  classical
  have hne : (Finset.univ : Finset ι).Nonempty := by
    obtain ⟨i, _⟩ := hpole
    exact ⟨i, Finset.mem_univ i⟩
  obtain ⟨i, _hi, hm⟩ := Finset.exists_mem_eq_sup Finset.univ hne
    (fun j => (-(a j).order).toNat)
  have hk := maximalPoleOrder_pos a hpole
  change maximalPoleOrder a = (-(a i).order).toNat at hm
  exact ⟨i, by omega⟩

def firstRegularCoordinates (a : ι → Meromorphic) : ι → Series :=
  fun i => regularRescaling (maximalPoleOrder a) (a i)

/-- The fixed-sum equation constructs the other regular vector without
assuming a separate order bound on its Laurent coordinates. -/
def secondRegularCoordinates (a : ι → Meromorphic) (s : ι → ℂ) : ι → Series :=
  fun i => firstRegularCoordinates a i -
    (PowerSeries.X : Series) ^ maximalPoleOrder a * PowerSeries.C (s i)

theorem firstRegularCoordinates_spec (a : ι → Meromorphic) (i : ι) :
    seriesInclusion (firstRegularCoordinates a i) =
      seriesInclusion (PowerSeries.X : Series) ^ maximalPoleOrder a * a i :=
  seriesInclusion_regularRescaling _ _ (order_lower_bound a i)

theorem secondRegularCoordinates_spec
    (a b : ι → Meromorphic) (s : ι → ℂ)
    (hfixed : ∀ i, a i + b i = algebraMap ℂ Meromorphic (s i)) (i : ι) :
    seriesInclusion (secondRegularCoordinates a s i) =
      -(seriesInclusion (PowerSeries.X : Series) ^ maximalPoleOrder a * b i) := by
  rw [secondRegularCoordinates, map_sub, map_mul, map_pow,
    firstRegularCoordinates_spec, seriesInclusion_C, ← hfixed i]
  ring

/-- The full t^k coordinate congruence, before choosing any local chart. -/
theorem coordinate_rescaling_difference (a : ι → Meromorphic) (s : ι → ℂ)
    (i : ι) :
    firstRegularCoordinates a i - secondRegularCoordinates a s i =
      (PowerSeries.X : Series) ^ maximalPoleOrder a * PowerSeries.C (s i) := by
  dsimp only [secondRegularCoordinates]
  ring

theorem common_special_value (a : ι → Meromorphic) (s : ι → ℂ)
    (hpole : ∃ i, (a i).order < 0) :
    (fun i => PowerSeries.constantCoeff (firstRegularCoordinates a i)) =
      (fun i => PowerSeries.constantCoeff (secondRegularCoordinates a s i)) :=
  same_special_value_of_rescaling _ _ s _ (maximalPoleOrder_pos a hpole)
    (coordinate_rescaling_difference a s)

theorem first_special_value_ne_zero (a : ι → Meromorphic)
    (hpole : ∃ i, (a i).order < 0) :
    (fun i => PowerSeries.constantCoeff (firstRegularCoordinates a i)) ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_coordinate_of_maximalPole a hpole
  have hk := maximalPoleOrder_pos a hpole
  have hai : a i ≠ 0 := by
    intro hzero
    rw [hzero, HahnSeries.order_zero] at hi
    omega
  intro hzero
  have hvalue := congrFun hzero i
  change PowerSeries.constantCoeff (regularRescaling (maximalPoleOrder a) (a i)) = 0 at hvalue
  rw [regularRescaling_constantCoeff, ← hi] at hvalue
  exact (HahnSeries.coeff_order_eq_zero.not.mpr hai) hvalue

theorem second_special_value_ne_zero (a : ι → Meromorphic) (s : ι → ℂ)
    (hpole : ∃ i, (a i).order < 0) :
    (fun i => PowerSeries.constantCoeff (secondRegularCoordinates a s i)) ≠ 0 := by
  rw [← common_special_value a s hpole]
  exact first_special_value_ne_zero a hpole

/-- The rescaling paragraph of the manuscript, with the power-series
vectors and the positive pole order genuinely constructed from the
Laurent expansions. No regular arcs are supplied by the caller. -/
theorem regular_rescalings_exist
    (a b : ι → Meromorphic) (s : ι → ℂ)
    (hfixed : ∀ i, a i + b i = algebraMap ℂ Meromorphic (s i))
    (hpole : ∃ i, (a i).order < 0) :
    ∃ (k : ℕ) (p q : ι → Series), 0 < k ∧
      (∀ i, seriesInclusion (p i) =
        seriesInclusion (PowerSeries.X : Series) ^ k * a i) ∧
      (∀ i, seriesInclusion (q i) =
        -(seriesInclusion (PowerSeries.X : Series) ^ k * b i)) ∧
      (∀ i, p i - q i = (PowerSeries.X : Series) ^ k * PowerSeries.C (s i)) ∧
      (fun i => PowerSeries.constantCoeff (p i)) =
        (fun i => PowerSeries.constantCoeff (q i)) ∧
      (fun i => PowerSeries.constantCoeff (p i)) ≠ 0 := by
  exact ⟨maximalPoleOrder a, firstRegularCoordinates a, secondRegularCoordinates a s,
    maximalPoleOrder_pos a hpole, firstRegularCoordinates_spec a,
    secondRegularCoordinates_spec a b s hfixed, coordinate_rescaling_difference a s,
    common_special_value a s hpole, first_special_value_ne_zero a hpole⟩

end FiniteCoordinates

end LeBrunSalamon.Construction.Lines.LaurentRescaling

end
