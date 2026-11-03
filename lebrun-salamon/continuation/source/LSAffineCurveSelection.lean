import LSSuitableDirections
import LSConeLocalization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!
## Actual integral affine curves in positive-dimensional affine fibers

SOURCE: `lines:cone-addition`, selection of an integral curve in the
nonorthogonal part of a positive-dimensional addition fiber. The affine
curve is constructed as a prime quotient of dimension one. The finite
dimension and the existence of that prime are proved from the finite-type
algebra and order-theoretic Krull dimension APIs, without an added curve
selection axiom.

This file does not yet prove that nondominance of cone addition makes a
particular nonorthogonal fiber positive-dimensional. That is the separate
fiber-dimension step. `LSCurveLaurentGeometry` subsequently applies the
independently approved classical Laurent-pole theorem to this exact curve.

SOURCE ONLY, UNCOMPILED. No compiler was invoked while preparing this file.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace LeBrunSalamon.Construction.Lines.AffineCurveSelection

open DirectionCones

section PrimeOfCoheightOne

/-- A finite-dimensional partially ordered set of positive dimension
has an element of coheight exactly one. -/
theorem exists_coheight_one {α : Type*} [Preorder α]
    [FiniteDimensionalOrder α] (hdim : 1 ≤ Order.krullDim α) :
    ∃ p : α, Order.coheight p = 1 := by
  have hpositive : ∃ p : α, 0 < Order.coheight p := by
    by_contra h
    have hz : ∀ p : α, Order.coheight p = 0 := by
      intro p
      apply le_antisymm _ zero_le
      exact le_of_not_gt (fun hp => h ⟨p, hp⟩)
    have hdimzero : Order.krullDim α ≤ 0 := by
      rw [Order.krullDim_eq_iSup_coheight]
      apply iSup_le
      intro p
      rw [hz p]
      exact le_rfl
    have hbad : (1 : WithBot ℕ∞) ≤ 0 := hdim.trans hdimzero
    norm_num at hbad
  obtain ⟨p, hp⟩ := hpositive
  by_cases h : Order.coheight p = 1
  · exact ⟨p, h⟩
  · have hge : (1 : ℕ∞) ≤ Order.coheight p := Order.one_le_iff_pos.mpr hp
    have hgt : (1 : ℕ∞) < Order.coheight p := lt_of_le_of_ne hge (Ne.symm h)
    obtain ⟨q, _hpq, hq⟩ :=
      (Order.coe_lt_coheight_iff (Order.coheight_lt_top p)).mp hgt
    exact ⟨q, hq⟩

theorem finiteRingKrullDim_of_finiteType
    (B : Type*) [CommRing B] [Nontrivial B]
    [Algebra ℂ B] [Algebra.FiniteType ℂ B] : FiniteRingKrullDim B := by
  apply finiteRingKrullDim_iff_ne_bot_and_top.mpr
  constructor
  · intro h
    have hnonneg := ringKrullDim_nonneg_of_nontrivial (R := B)
    rw [h] at hnonneg
    norm_num at hnonneg
  · obtain ⟨n, f, hf⟩ :=
      (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := ℂ) (S := B)).mp
        inferInstance
    have hbound := ringKrullDim_le_of_surjective f.toRingHom hf
    have hpoly : ringKrullDim (MvPolynomial (Fin n) ℂ) = (n : WithBot ℕ∞) := by
      simp
    rw [hpoly] at hbound
    have hfinite : (n : WithBot ℕ∞) < ⊤ :=
      WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top n)
    exact ne_of_lt (lt_of_le_of_lt hbound hfinite)

/-- The quotient ring is the coordinate ring of the closure of the
prime point, so its dimension is that prime's coheight. -/
theorem ringKrullDim_quotient_eq_coheight
    {B : Type*} [CommRing B] (p : PrimeSpectrum B) :
    ringKrullDim (B ⧸ p.asIdeal) = (Order.coheight p : WithBot ℕ∞) := by
  rw [ringKrullDim_quotient]
  change Order.krullDim (Set.Ici p) = (Order.coheight p : WithBot ℕ∞)
  exact (Order.coheight_eq_krullDim_Ici p).symm

/-- Every positive-dimensional affine finite-type complex scheme has
an actual integral closed affine subscheme of dimension one. The prime
is selected in its coordinate ring, with no supplied curve certificate. -/
theorem exists_prime_quotient_dimension_one
    (B : Type*) [CommRing B] [Algebra ℂ B] [Algebra.FiniteType ℂ B]
    (hdim : 1 ≤ ringKrullDim B) :
    ∃ p : PrimeSpectrum B, ringKrullDim (B ⧸ p.asIdeal) = 1 := by
  letI : Nontrivial B := zero_le_ringKrullDim_iff_nontrivial.mp
    (le_trans (by norm_num) hdim)
  letI : FiniteRingKrullDim B := finiteRingKrullDim_of_finiteType B
  obtain ⟨p, hp⟩ := exists_coheight_one (α := PrimeSpectrum B) hdim
  refine ⟨p, ?_⟩
  rw [ringKrullDim_quotient_eq_coheight, hp]
  rfl

end PrimeOfCoheightOne

section ChosenAffineCurve

variable (B : Type) [CommRing B] [Algebra ℂ B] [Algebra.FiniteType ℂ B]
    (hdim : 1 ≤ ringKrullDim B)

def curvePrime : PrimeSpectrum B :=
  Classical.choose (exists_prime_quotient_dimension_one B hdim)

abbrev CurveRing := B ⧸ (curvePrime B hdim).asIdeal

instance curveRing_isDomain : IsDomain (CurveRing B hdim) := by
  letI : (curvePrime B hdim).asIdeal.IsPrime := (curvePrime B hdim).isPrime
  infer_instance

theorem curveRing_dimension : ringKrullDim (CurveRing B hdim) = 1 :=
  Classical.choose_spec (exists_prime_quotient_dimension_one B hdim)

instance curveRing_finiteType : Algebra.FiniteType ℂ (CurveRing B hdim) :=
  inferInstanceAs (Algebra.FiniteType ℂ (B ⧸ (curvePrime B hdim).asIdeal))

def curveQuotient : B →ₐ[ℂ] CurveRing B hdim :=
  Ideal.Quotient.mkₐ ℂ (curvePrime B hdim).asIdeal

theorem curveQuotient_surjective : Function.Surjective (curveQuotient B hdim) :=
  Ideal.Quotient.mkₐ_surjective ℂ _

abbrev curveScheme : Scheme := Spec (CommRingCat.of (CurveRing B hdim))

instance curveScheme_isIntegral : IsIntegral (curveScheme B hdim) :=
  inferInstanceAs (IsIntegral (Spec (CommRingCat.of (CurveRing B hdim))))

instance curveStructureMap_locallyOfFiniteType :
    LocallyOfFiniteType (affineBaseMap (CurveRing B hdim)) := by
  change LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (CurveRing B hdim))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

def curveInclusion : curveScheme B hdim ⟶ Spec (CommRingCat.of B) :=
  affineMap (curveQuotient B hdim)

instance curveInclusion_closed : IsClosedImmersion (curveInclusion B hdim) :=
  IsClosedImmersion.spec_of_surjective _ (curveQuotient_surjective B hdim)

theorem curveInclusion_overC :
    curveInclusion B hdim ≫ affineBaseMap B = affineBaseMap (CurveRing B hdim) :=
  affineMap_overC _

end ChosenAffineCurve

section NonconstantCoordinates

/-- If all algebra generators become complex scalars, every element
is a complex scalar. This will force dimension zero, contradicting the
dimension of the selected curve. -/
theorem algebraMap_surjective_of_generators_scalar
    {ι A : Type*} [CommRing A] [Algebra ℂ A]
    (r : ι → A) (hgen : Algebra.adjoin ℂ (Set.range r) = ⊤)
    (hr : ∀ i, ∃ c : ℂ, algebraMap ℂ A c = r i) :
    Function.Surjective (algebraMap ℂ A) := by
  have hle : Algebra.adjoin ℂ (Set.range r) ≤ (⊥ : Subalgebra ℂ A) := by
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact Algebra.mem_bot.mpr (hr i)
  rw [hgen] at hle
  intro a
  exact Algebra.mem_bot.mp (hle (show a ∈ (⊤ : Subalgebra ℂ A) from trivial))

theorem exists_nonconstant_generator_of_dimension_one
    {ι A : Type*} [CommRing A] [Algebra ℂ A]
    (r : ι → A) (hgen : Algebra.adjoin ℂ (Set.range r) = ⊤)
    (hdim : ringKrullDim A = 1) :
    ∃ i, ¬ ∃ c : ℂ, algebraMap ℂ A c = r i := by
  by_contra! h
  have hbound := ringKrullDim_le_of_surjective (algebraMap ℂ A)
    (algebraMap_surjective_of_generators_scalar r hgen h)
  rw [hdim, ringKrullDim_eq_zero_of_field] at hbound
  norm_num at hbound

end NonconstantCoordinates

section LocalizedNonconstantCoordinates

/-- Passing to a principal open cannot make a positive-dimensional
quotient depend only on inverted denominators while all original
coordinates become constants. The localization fraction equation proves
that its entire image would consist of complex scalars. -/
theorem algebraMap_surjective_of_localized_generators_scalar
    {ι A L D : Type*} [CommRing A] [CommRing L] [CommRing D] [Nontrivial D]
    [Algebra ℂ A] [Algebra A L] [Algebra ℂ L] [IsScalarTower ℂ A L]
    [Algebra ℂ D] (M : Submonoid A) [IsLocalization M L]
    (r : ι → A) (hgen : Algebra.adjoin ℂ (Set.range r) = ⊤)
    (f : L →ₐ[ℂ] D) (hf : Function.Surjective f)
    (hr : ∀ i, ∃ c : ℂ,
      algebraMap ℂ D c = f (algebraMap A L (r i))) :
    Function.Surjective (algebraMap ℂ D) := by
  let g : A →ₐ[ℂ] D := f.comp (Algebra.algHom ℂ A L)
  have hle : Algebra.adjoin ℂ (Set.range r) ≤
      (⊥ : Subalgebra ℂ D).comap g := by
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    change g (r i) ∈ (⊥ : Subalgebra ℂ D)
    exact Algebra.mem_bot.mpr (hr i)
  rw [hgen] at hle
  have hbase : ∀ a : A, ∃ c : ℂ,
      algebraMap ℂ D c = f (algebraMap A L a) := by
    intro a
    exact Algebra.mem_bot.mp
      (hle (show a ∈ (⊤ : Subalgebra ℂ A) from trivial))
  intro d
  obtain ⟨z, rfl⟩ := hf d
  obtain ⟨⟨num, den⟩, hfrac⟩ := IsLocalization.surj M z
  obtain ⟨cnum, hnum⟩ := hbase num
  obtain ⟨cden, hden⟩ := hbase den.val
  have hunit : IsUnit (f (algebraMap A L den.val)) :=
    (IsLocalization.map_units L den).map f.toRingHom
  have hcden : cden ≠ 0 := by
    intro hzero
    apply hunit.ne_zero
    rw [← hden, hzero, map_zero]
  have hrel : f z * algebraMap ℂ D cden = algebraMap ℂ D cnum := by
    have h := congrArg f hfrac
    simpa only [map_mul, ← hnum, ← hden] using h
  refine ⟨cnum * cden⁻¹, ?_⟩
  calc
    algebraMap ℂ D (cnum * cden⁻¹) =
        algebraMap ℂ D cnum * algebraMap ℂ D (cden⁻¹) := map_mul _ _ _
    _ = (f z * algebraMap ℂ D cden) * algebraMap ℂ D (cden⁻¹) := by
      rw [hrel]
    _ = f z := by
      rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hcden, map_one, mul_one]

end LocalizedNonconstantCoordinates

section AdditionFiber

variable {ι : Type}

/-- Substituting b=s-a in the equations of the second cone. -/
def fixedSumSubstitution (s : ι → ℂ) :
    CoordinatePolynomial ι →ₐ[ℂ] CoordinatePolynomial ι :=
  MvPolynomial.aeval (fun i => MvPolynomial.C (s i) - MvPolynomial.X i)

/-- The concrete fixed-sum fiber equations in the first coordinate a.
This includes equations of both original closed cone coordinate rings. -/
def fixedSumIdeal (S T : Set (ι → ℂ)) (s : ι → ℂ) :
    Ideal (CoordinatePolynomial ι) :=
  vanishingIdeal S ⊔
    Ideal.map (fixedSumSubstitution s).toRingHom (vanishingIdeal T)

abbrev FixedSumRing (S T : Set (ι → ℂ)) (s : ι → ℂ) :=
  CoordinatePolynomial ι ⧸ fixedSumIdeal S T s

def fixedFirst (S T : Set (ι → ℂ)) (s : ι → ℂ) :
    CoordinateRing S →ₐ[ℂ] FixedSumRing S T s :=
  Ideal.Quotient.liftₐ (vanishingIdeal S)
    (Ideal.Quotient.mkₐ ℂ (fixedSumIdeal S T s)) (by
      intro p hp
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact (le_sup_left : vanishingIdeal S ≤ fixedSumIdeal S T s) hp)

def fixedSecond (S T : Set (ι → ℂ)) (s : ι → ℂ) :
    CoordinateRing T →ₐ[ℂ] FixedSumRing S T s :=
  Ideal.Quotient.liftₐ (vanishingIdeal T)
    ((Ideal.Quotient.mkₐ ℂ (fixedSumIdeal S T s)).comp (fixedSumSubstitution s)) (by
      intro p hp
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact (le_sup_right :
        Ideal.map (fixedSumSubstitution s).toRingHom (vanishingIdeal T) ≤
          fixedSumIdeal S T s)
        (Ideal.mem_map_of_mem (fixedSumSubstitution s).toRingHom hp))

@[simp]
theorem fixedFirst_coordinate (S T : Set (ι → ℂ)) (s : ι → ℂ) (i : ι) :
    fixedFirst S T s (coordinate S i) =
      ConeArcs.quotientCoordinate (fixedSumIdeal S T s) i := rfl

@[simp]
theorem fixedSecond_coordinate (S T : Set (ι → ℂ)) (s : ι → ℂ) (i : ι) :
    fixedSecond S T s (coordinate T i) =
      algebraMap ℂ (FixedSumRing S T s) (s i) -
        ConeArcs.quotientCoordinate (fixedSumIdeal S T s) i := by
  change (Ideal.Quotient.mkₐ ℂ (fixedSumIdeal S T s))
    (fixedSumSubstitution s (MvPolynomial.X i)) = _
  rw [fixedSumSubstitution, MvPolynomial.aeval_X, map_sub]
  congr 1

theorem fixedSum_equation (S T : Set (ι → ℂ)) (s : ι → ℂ) (i : ι) :
    fixedFirst S T s (coordinate S i) + fixedSecond S T s (coordinate T i) =
      algebraMap ℂ (FixedSumRing S T s) (s i) := by
  rw [fixedFirst_coordinate, fixedSecond_coordinate]
  ring

theorem fixedFirstCoordinates_generate (S T : Set (ι → ℂ)) (s : ι → ℂ) :
    Algebra.adjoin ℂ (Set.range (fun i => fixedFirst S T s (coordinate S i))) = ⊤ := by
  simpa only [fixedFirst_coordinate] using
    ConeArcs.quotientCoordinates_generate (fixedSumIdeal S T s)

/-- Restriction of the cone coordinates to the actual selected curve. -/
def curveFirst [Finite ι] (S T : Set (ι → ℂ)) (s : ι → ℂ)
    (hdim : 1 ≤ ringKrullDim (FixedSumRing S T s)) :
    CoordinateRing S →ₐ[ℂ] CurveRing (FixedSumRing S T s) hdim :=
  (curveQuotient _ hdim).comp (fixedFirst S T s)

def curveSecond [Finite ι] (S T : Set (ι → ℂ)) (s : ι → ℂ)
    (hdim : 1 ≤ ringKrullDim (FixedSumRing S T s)) :
    CoordinateRing T →ₐ[ℂ] CurveRing (FixedSumRing S T s) hdim :=
  (curveQuotient _ hdim).comp (fixedSecond S T s)

theorem curve_fixedSum_equation [Finite ι] (S T : Set (ι → ℂ)) (s : ι → ℂ)
    (hdim : 1 ≤ ringKrullDim (FixedSumRing S T s)) (i : ι) :
    curveFirst S T s hdim (coordinate S i) +
      curveSecond S T s hdim (coordinate T i) =
        algebraMap ℂ (CurveRing (FixedSumRing S T s) hdim) (s i) := by
  change curveQuotient _ hdim (fixedFirst S T s (coordinate S i)) +
    curveQuotient _ hdim (fixedSecond S T s (coordinate T i)) = _
  rw [← map_add, fixedSum_equation, AlgHom.commutes]

theorem curveFirstCoordinates_generate [Finite ι]
    (S T : Set (ι → ℂ)) (s : ι → ℂ)
    (hdim : 1 ≤ ringKrullDim (FixedSumRing S T s)) :
    Algebra.adjoin ℂ (Set.range
      (fun i => curveFirst S T s hdim (coordinate S i))) = ⊤ := by
  let f := (curveQuotient (FixedSumRing S T s) hdim).comp
    (Ideal.Quotient.mkₐ ℂ (fixedSumIdeal S T s))
  have hf : Function.Surjective f :=
    (curveQuotient_surjective _ hdim).comp (Ideal.Quotient.mkₐ_surjective ℂ _)
  have hmap : MvPolynomial.aeval
      (fun i => curveFirst S T s hdim (coordinate S i)) = f := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [MvPolynomial.aeval_X, curveFirst, AlgHom.comp_apply,
      fixedFirst_coordinate, f, ConeArcs.quotientCoordinate,
      Ideal.Quotient.mkₐ_eq_mk]
  rw [Algebra.adjoin_range_eq_range_aeval, hmap]
  exact (AlgHom.range_eq_top f).mpr hf

/-- The curve coordinate a is genuinely nonconstant. This is deduced
from its dimension and the actual fixed-sum coordinate presentation. -/
theorem curveFirst_nonconstant [Finite ι]
    (S T : Set (ι → ℂ)) (s : ι → ℂ)
    (hdim : 1 ≤ ringKrullDim (FixedSumRing S T s)) :
    ∃ i, ¬ ∃ c : ℂ,
      algebraMap ℂ (CurveRing (FixedSumRing S T s) hdim) c =
        curveFirst S T s hdim (coordinate S i) :=
  exists_nonconstant_generator_of_dimension_one _
    (curveFirstCoordinates_generate S T s hdim) (curveRing_dimension _ hdim)

end AdditionFiber

section NonorthogonalAdditionFiber

variable {ι : Type} [Fintype ι]

/-- The actual pairing function restricted to the fixed-sum fiber. -/
def fixedPairing (S T : Set (ι → ℂ)) (s : ι → ℂ) (omega : ι → ι → ℂ) :
    FixedSumRing S T s :=
  ConePairing.pairing omega
    (fun i => fixedFirst S T s (coordinate S i))
    (fun i => fixedSecond S T s (coordinate T i))

/-- The principal open where the *same* pair of cone coordinates has
nonzero pairing. The subsequent curve is chosen inside this open. -/
abbrev NonorthogonalFiberRing (S T : Set (ι → ℂ))
    (s : ι → ℂ) (omega : ι → ι → ℂ) :=
  Localization.Away (fixedPairing S T s omega)

def nonorthogonalCurveFirst (S T : Set (ι → ℂ))
    (s : ι → ℂ) (omega : ι → ι → ℂ)
    (hdim : 1 ≤ ringKrullDim (NonorthogonalFiberRing S T s omega)) :
    CoordinateRing S →ₐ[ℂ] CurveRing (NonorthogonalFiberRing S T s omega) hdim :=
  ((curveQuotient _ hdim).comp
    (Algebra.algHom ℂ (FixedSumRing S T s) (NonorthogonalFiberRing S T s omega))).comp
      (fixedFirst S T s)

def nonorthogonalCurveSecond (S T : Set (ι → ℂ))
    (s : ι → ℂ) (omega : ι → ι → ℂ)
    (hdim : 1 ≤ ringKrullDim (NonorthogonalFiberRing S T s omega)) :
    CoordinateRing T →ₐ[ℂ] CurveRing (NonorthogonalFiberRing S T s omega) hdim :=
  ((curveQuotient _ hdim).comp
    (Algebra.algHom ℂ (FixedSumRing S T s) (NonorthogonalFiberRing S T s omega))).comp
      (fixedSecond S T s)

theorem nonorthogonalCurve_fixedSum_equation (S T : Set (ι → ℂ))
    (s : ι → ℂ) (omega : ι → ι → ℂ)
    (hdim : 1 ≤ ringKrullDim (NonorthogonalFiberRing S T s omega)) (i : ι) :
    nonorthogonalCurveFirst S T s omega hdim (coordinate S i) +
      nonorthogonalCurveSecond S T s omega hdim (coordinate T i) =
        algebraMap ℂ (CurveRing (NonorthogonalFiberRing S T s omega) hdim) (s i) := by
  let g := (curveQuotient (NonorthogonalFiberRing S T s omega) hdim).comp
    (Algebra.algHom ℂ (FixedSumRing S T s) (NonorthogonalFiberRing S T s omega))
  change g (fixedFirst S T s (coordinate S i)) +
    g (fixedSecond S T s (coordinate T i)) = _
  rw [← map_add, fixedSum_equation, AlgHom.commutes]

/-- The nonzero pairing condition survives on the whole selected
integral curve because it was inverted before the prime was selected. -/
theorem nonorthogonalCurve_pairing_isUnit (S T : Set (ι → ℂ))
    (s : ι → ℂ) (omega : ι → ι → ℂ)
    (hdim : 1 ≤ ringKrullDim (NonorthogonalFiberRing S T s omega)) :
    IsUnit (ConePairing.pairing omega
      (fun i => nonorthogonalCurveFirst S T s omega hdim (coordinate S i))
      (fun i => nonorthogonalCurveSecond S T s omega hdim (coordinate T i))) := by
  let q := curveQuotient (NonorthogonalFiberRing S T s omega) hdim
  let g : FixedSumRing S T s →ₐ[ℂ]
      CurveRing (NonorthogonalFiberRing S T s omega) hdim :=
    q.comp (Algebra.algHom ℂ (FixedSumRing S T s) (NonorthogonalFiberRing S T s omega))
  have hu : IsUnit
      (algebraMap (FixedSumRing S T s) (NonorthogonalFiberRing S T s omega)
        (fixedPairing S T s omega)) :=
    IsLocalization.Away.algebraMap_isUnit (fixedPairing S T s omega)
  have hq := hu.map q.toRingHom
  change IsUnit (g (fixedPairing S T s omega)) at hq
  change IsUnit (ConePairing.pairing omega
    (fun i => g (fixedFirst S T s (coordinate S i)))
    (fun i => g (fixedSecond S T s (coordinate T i))))
  simpa only [fixedPairing, ConePairing.pairing_map] using hq

theorem nonorthogonalCurve_pairing_ne_zero (S T : Set (ι → ℂ))
    (s : ι → ℂ) (omega : ι → ι → ℂ)
    (hdim : 1 ≤ ringKrullDim (NonorthogonalFiberRing S T s omega)) :
    ConePairing.pairing omega
      (fun i => nonorthogonalCurveFirst S T s omega hdim (coordinate S i))
      (fun i => nonorthogonalCurveSecond S T s omega hdim (coordinate T i)) ≠ 0 :=
  (nonorthogonalCurve_pairing_isUnit S T s omega hdim).ne_zero

/-- The selected curve is not generated only by an inverse denominator:
at least one original a-coordinate is nonconstant on that very curve. -/
theorem nonorthogonalCurveFirst_nonconstant (S T : Set (ι → ℂ))
    (s : ι → ℂ) (omega : ι → ι → ℂ)
    (hdim : 1 ≤ ringKrullDim (NonorthogonalFiberRing S T s omega)) :
    ∃ i, ¬ ∃ c : ℂ,
      algebraMap ℂ (CurveRing (NonorthogonalFiberRing S T s omega) hdim) c =
        nonorthogonalCurveFirst S T s omega hdim (coordinate S i) := by
  by_contra! h
  have hs : Function.Surjective
      (algebraMap ℂ (CurveRing (NonorthogonalFiberRing S T s omega) hdim)) := by
    apply algebraMap_surjective_of_localized_generators_scalar
      (Submonoid.powers (fixedPairing S T s omega))
      (fun i => fixedFirst S T s (coordinate S i))
      (fixedFirstCoordinates_generate S T s)
      (curveQuotient (NonorthogonalFiberRing S T s omega) hdim)
      (curveQuotient_surjective _ hdim)
    intro i
    exact h i
  have hbound := ringKrullDim_le_of_surjective _ hs
  rw [curveRing_dimension, ringKrullDim_eq_zero_of_field] at hbound
  norm_num at hbound

end NonorthogonalAdditionFiber

end LeBrunSalamon.Construction.Lines.AffineCurveSelection

end
