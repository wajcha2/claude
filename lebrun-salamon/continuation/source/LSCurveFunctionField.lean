import LSAffineCurveSelection
import LSCurvePairing
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Nullstellensatz

/-!
## The function field of the selected nonorthogonal curve

The coefficient field is the fraction field of the actual dimension-one
prime quotient constructed in `LSAffineCurveSelection`. Its canonical
comparison with the scheme's generic-point stalk is explicit. Both cone
maps, the fixed sum, nonzero pairing and nonconstant first coordinate are
transported through the injective fraction map. Finite generation is
proved as `EssFiniteType`, the correct property for a function field.

SOURCE ONLY, UNCOMPILED. There are no new literature admissions here.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace LeBrunSalamon.Construction.Lines.AffineCurveSelection

open DirectionCones

/-- A complex point of an actual nonzero finite-type complex algebra,
constructed from a maximal ideal and the proved weak Nullstellensatz. -/
def complexPointOfFiniteType (A : Type) [CommRing A] [Nontrivial A]
    [Algebra ℂ A] [Algebra.FiniteType ℂ A] : A →ₐ[ℂ] ℂ := by
  let m : Ideal A := Classical.choose (Ideal.exists_maximal A)
  letI : m.IsMaximal := Classical.choose_spec (Ideal.exists_maximal A)
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  letI : Module.Finite ℂ (A ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ m)
  let e : ℂ ≃ₐ[ℂ] (A ⧸ m) :=
    AlgEquiv.ofBijective (Algebra.ofId ℂ (A ⧸ m))
      IsAlgClosed.algebraMap_bijective_of_isIntegral
  exact e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ m)

section FunctionField

variable (B : Type) [CommRing B] [Algebra ℂ B] [Algebra.FiniteType ℂ B]
    (hdim : 1 ≤ ringKrullDim B)

abbrev CurveFunctionField := FractionRing (CurveRing B hdim)

def curveFunctionInclusion : CurveRing B hdim →ₐ[ℂ] CurveFunctionField B hdim :=
  Algebra.algHom ℂ (CurveRing B hdim) (CurveFunctionField B hdim)

def curveComplexPoint : CurveRing B hdim →ₐ[ℂ] ℂ :=
  complexPointOfFiniteType (CurveRing B hdim)

theorem curveFunctionInclusion_injective :
    Function.Injective (curveFunctionInclusion B hdim) :=
  IsFractionRing.injective (CurveRing B hdim) (CurveFunctionField B hdim)

theorem curveFunctionInclusion_ne_zero_of_point
    (x : CurveRing B hdim) (hx : curveComplexPoint B hdim x ≠ 0) :
    curveFunctionInclusion B hdim x ≠ 0 := by
  intro hz
  have hxzero : x = 0 := curveFunctionInclusion_injective B hdim
    (hz.trans (map_zero (curveFunctionInclusion B hdim)).symm)
  apply hx
  rw [hxzero, map_zero]

local instance :
    Algebra (CurveRing B hdim) (curveScheme B hdim).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec
    (CommRingCat.of (CurveRing B hdim))

/-- Identification with the actual generic-point stalk of the actual
integral affine curve, preserving its coordinate-ring map. -/
def curveFunctionField_schemeEquiv :
    CurveFunctionField B hdim ≃ₐ[CurveRing B hdim] (curveScheme B hdim).functionField := by
  letI : IsFractionRing (CurveRing B hdim) (curveScheme B hdim).functionField :=
    functionField_isFractionRing_of_affine (CommRingCat.of (CurveRing B hdim))
  exact FractionRing.algEquiv (CurveRing B hdim) (curveScheme B hdim).functionField

/-- A function field is finitely generated as a field. It is not
asserted to be a finite-type algebra over C. -/
instance curveFunctionField_essFiniteType :
    Algebra.EssFiniteType ℂ (CurveFunctionField B hdim) := by
  letI : Algebra.EssFiniteType (CurveRing B hdim) (CurveFunctionField B hdim) :=
    Algebra.EssFiniteType.of_isLocalization (CurveFunctionField B hdim)
      (nonZeroDivisors (CurveRing B hdim))
  exact Algebra.EssFiniteType.comp ℂ (CurveRing B hdim) (CurveFunctionField B hdim)

theorem curveFunctionField_finitelyGenerated :
    (⊤ : IntermediateField ℂ (CurveFunctionField B hdim)).FG :=
  IntermediateField.fg_top ℂ (CurveFunctionField B hdim)

end FunctionField

section NonorthogonalFunctionField

variable {ι : Type} [Fintype ι]
variable (S T : Set (ι → ℂ)) (s : ι → ℂ) (omega : ι → ι → ℂ)
    (hdim : 1 ≤ ringKrullDim (NonorthogonalFiberRing S T s omega))

abbrev NonorthogonalFunctionField :=
  CurveFunctionField (NonorthogonalFiberRing S T s omega) hdim

def functionFirst : CoordinateRing S →ₐ[ℂ] NonorthogonalFunctionField S T s omega hdim :=
  (curveFunctionInclusion _ hdim).comp (nonorthogonalCurveFirst S T s omega hdim)

def functionSecond : CoordinateRing T →ₐ[ℂ] NonorthogonalFunctionField S T s omega hdim :=
  (curveFunctionInclusion _ hdim).comp (nonorthogonalCurveSecond S T s omega hdim)

theorem function_fixedSum_equation (i : ι) :
    @Add.add (NonorthogonalFunctionField S T s omega hdim)
      (FractionRing.field (CurveRing (NonorthogonalFiberRing S T s omega) hdim)).toAdd
      (functionFirst S T s omega hdim (coordinate S i))
      (functionSecond S T s omega hdim (coordinate T i)) =
        algebraMap ℂ (NonorthogonalFunctionField S T s omega hdim) (s i) := by
  let f := curveFunctionInclusion (NonorthogonalFiberRing S T s omega) hdim
  exact (f.toRingHom.map_add
      (nonorthogonalCurveFirst S T s omega hdim (coordinate S i))
      (nonorthogonalCurveSecond S T s omega hdim (coordinate T i))).symm.trans
    ((congrArg f (nonorthogonalCurve_fixedSum_equation S T s omega hdim i)).trans
      (f.commutes (s i)))

theorem function_pairing_ne_zero :
    ConePairing.pairing omega
      (fun i => functionFirst S T s omega hdim (coordinate S i))
      (fun i => functionSecond S T s omega hdim (coordinate T i)) ≠ 0 := by
  have h := (nonorthogonalCurve_pairing_isUnit S T s omega hdim).map
    (curveFunctionInclusion (NonorthogonalFiberRing S T s omega) hdim).toRingHom
  change IsUnit (curveFunctionInclusion (NonorthogonalFiberRing S T s omega) hdim
    (ConePairing.pairing omega
      (fun i => nonorthogonalCurveFirst S T s omega hdim (coordinate S i))
      (fun i => nonorthogonalCurveSecond S T s omega hdim (coordinate T i)))) at h
  rw [ConePairing.pairing_map] at h
  exact h.ne_zero

theorem functionFirst_nonconstant :
    ∃ i, ¬ ∃ c : ℂ,
      algebraMap ℂ (NonorthogonalFunctionField S T s omega hdim) c =
        functionFirst S T s omega hdim (coordinate S i) := by
  obtain ⟨i, hi⟩ := nonorthogonalCurveFirst_nonconstant S T s omega hdim
  refine ⟨i, ?_⟩
  rintro ⟨c, hc⟩
  apply hi
  refine ⟨c, ?_⟩
  apply curveFunctionInclusion_injective (NonorthogonalFiberRing S T s omega) hdim
  rw [AlgHom.commutes]
  exact hc

/-- Over the algebraically closed base, the nonconstant coordinate is
transcendental. No transcendence-degree assertion is inserted. -/
theorem functionFirst_transcendental :
    ∃ i, Transcendental ℂ (functionFirst S T s omega hdim (coordinate S i)) := by
  obtain ⟨i, hi⟩ := functionFirst_nonconstant S T s omega hdim
  refine ⟨i, ?_⟩
  intro halg
  have hm : functionFirst S T s omega hdim (coordinate S i) ∈
      algebraicClosure ℂ (NonorthogonalFunctionField S T s omega hdim) :=
    mem_algebraicClosure_iff.mpr halg
  have hbot : algebraicClosure ℂ (NonorthogonalFunctionField S T s omega hdim) =
      (⊥ : IntermediateField ℂ (NonorthogonalFunctionField S T s omega hdim)) :=
    IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
  rw [hbot] at hm
  exact hi (IntermediateField.mem_bot.mp hm)

/-- The first coordinate map extends to any actual principal chart it
meets at the generic point, by inverting its nonzero chart denominator. -/
def functionFirstOnChart (u : CoordinateRing S)
    (hu : functionFirst S T s omega hdim u ≠ 0) :
    Localization.Away u →ₐ[ℂ] NonorthogonalFunctionField S T s omega hdim :=
  IsLocalization.Away.liftAlgHom u (f := functionFirst S T s omega hdim)
    (isUnit_iff_ne_zero.mpr hu)

def functionSecondOnChart (v : CoordinateRing T)
    (hv : functionSecond S T s omega hdim v ≠ 0) :
    Localization.Away v →ₐ[ℂ] NonorthogonalFunctionField S T s omega hdim :=
  IsLocalization.Away.liftAlgHom v (f := functionSecond S T s omega hdim)
    (isUnit_iff_ne_zero.mpr hv)

@[simp]
theorem functionFirstOnChart_coordinate (u : CoordinateRing S)
    (hu : functionFirst S T s omega hdim u ≠ 0) (i : ι) :
    functionFirstOnChart S T s omega hdim u hu
      (ConeRadial.localizedCoordinate (L := Localization.Away u) S i) =
        functionFirst S T s omega hdim (coordinate S i) :=
  IsLocalization.Away.lift_eq u (isUnit_iff_ne_zero.mpr hu) (coordinate S i)

@[simp]
theorem functionSecondOnChart_coordinate (v : CoordinateRing T)
    (hv : functionSecond S T s omega hdim v ≠ 0) (i : ι) :
    functionSecondOnChart S T s omega hdim v hv
      (ConeRadial.localizedCoordinate (L := Localization.Away v) T i) =
        functionSecond S T s omega hdim (coordinate T i) :=
  IsLocalization.Away.lift_eq v (isUnit_iff_ne_zero.mpr hv) (coordinate T i)

/-- For the actual selected curve, tangent isotropy on actual charts
forces the already nonzero pairing to be one nonzero complex constant.
No auxiliary complex point of the curve is needed: nonvanishing was
retained by the original localization before curve selection. -/
theorem function_pairing_eq_nonzero_complexScalar
    (hS : ConeRadial.IsCone S) (hT : ConeRadial.IsCone T)
    (hskew : ∀ i j, omega j i = -omega i j)
    (u : CoordinateRing S) (v : CoordinateRing T)
    (hu : functionFirst S T s omega hdim u ≠ 0)
    (hv : functionSecond S T s omega hdim v ≠ 0)
    [Algebra.FormallySmooth ℂ (Localization.Away u)]
    [Algebra.FormallySmooth ℂ (Localization.Away v)]
    (hU : ∀ (p : Localization.Away u →ₐ[ℂ] ℂ)
      (D E : Infinitesimal.Tangent (Localization.Away u) p),
      ConePairing.pairing omega
        (fun i => D.val (ConeRadial.localizedCoordinate (L := Localization.Away u) S i))
        (fun i => E.val (ConeRadial.localizedCoordinate (L := Localization.Away u) S i)) = 0)
    (hV : ∀ (p : Localization.Away v →ₐ[ℂ] ℂ)
      (D E : Infinitesimal.Tangent (Localization.Away v) p),
      ConePairing.pairing omega
        (fun i => D.val (ConeRadial.localizedCoordinate (L := Localization.Away v) T i))
        (fun i => E.val (ConeRadial.localizedCoordinate (L := Localization.Away v) T i)) = 0) :
    ∃ c : ℂ, c ≠ 0 ∧ ConePairing.pairing omega
      (fun i => functionFirst S T s omega hdim (coordinate S i))
      (fun i => functionSecond S T s omega hdim (coordinate T i)) =
        algebraMap ℂ (NonorthogonalFunctionField S T s omega hdim) c := by
  have hsum : ∀ i,
      @Add.add (NonorthogonalFunctionField S T s omega hdim)
        (FractionRing.field (CurveRing (NonorthogonalFiberRing S T s omega) hdim)).toAdd
        (functionFirstOnChart S T s omega hdim u hu
          (ConeRadial.localizedCoordinate (L := Localization.Away u) S i))
        (functionSecondOnChart S T s omega hdim v hv
          (ConeRadial.localizedCoordinate (L := Localization.Away v) T i)) =
        algebraMap ℂ (NonorthogonalFunctionField S T s omega hdim) (s i) := by
    intro i
    rw [functionFirstOnChart_coordinate, functionSecondOnChart_coordinate]
    exact function_fixedSum_equation S T s omega hdim i
  obtain ⟨c, hc⟩ := CurvePairing.fixedSum_pairing_eq_complexScalar
    (functionFirstOnChart S T s omega hdim u hu)
    (functionSecondOnChart S T s omega hdim v hv)
    (ConeRadial.localizedCoordinate (L := Localization.Away u) S)
    (ConeRadial.localizedCoordinate (L := Localization.Away v) T)
    omega hskew
    (ConeIsotropy.radialForm_eq_zero_of_tangent_isotropy S hS u omega hU)
    (ConeIsotropy.radialForm_eq_zero_of_tangent_isotropy T hT v omega hV)
    s hsum
  simp only [functionFirstOnChart_coordinate, functionSecondOnChart_coordinate] at hc
  refine ⟨c, ?_, hc⟩
  intro hz
  apply function_pairing_ne_zero S T s omega hdim
  simpa only [hz, map_zero] using hc

end NonorthogonalFunctionField

end LeBrunSalamon.Construction.Lines.AffineCurveSelection

end

