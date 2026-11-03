import LSLaurentRescaling
import LSSuitableDirections
import LSConeLocalization
import LSConeIsotropy
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
## The rescaled Laurent coordinates define actual arcs in the closed cones

SOURCE: `lines:cone-addition`, the maximal-pole paragraph. This file proves
the homogeneity of the actual vanishing ideal from scalar stability of the
point set, constructs the quotient algebra maps for the regular rescalings,
and extends arcs to a principal chart when its denominator is nonzero at
their common special point. No arc or localization map is supplied as an
unproved existence certificate.

The inputs here are genuine Laurent algebra points of the two cones.
`LSCurveLaurentGeometry` subsequently constructs them, with a coordinate
pole, from an actual positive-dimensional nonorthogonal addition fiber.
The final global contradiction is in `LSConeFiberRigidity`; the further
fiber-dimension-to-dominance implication remains a separate task.

SOURCE ONLY, UNCOMPILED. No compiler was invoked while preparing this file.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeBrunSalamon.Construction.Lines.LaurentRescaling

open ConePole DirectionCones

section HomogeneousEvaluation

variable {ι A : Type*} [CommRing A] [Algebra ℂ A]

/-- Evaluation of a homogeneous polynomial commutes with a scalar
rescaling over every complex algebra, including the Laurent field. -/
theorem aeval_mul_of_homogeneous (x : ι → A) (c : A)
    {p : MvPolynomial ι ℂ} {d : ℕ} (hp : p.IsHomogeneous d) :
    MvPolynomial.aeval (fun i => c * x i) p =
      c ^ d * MvPolynomial.aeval x p := by
  classical
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ hp hq =>
      simp only [map_add, hp, hq, mul_add]
  | monomial m r hm =>
      have hdegree : (∑ i ∈ m.support, m i) = d := by
        simpa only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul,
          mul_one, Finsupp.sum] using hm
      simp only [MvPolynomial.aeval_monomial, Finsupp.prod, mul_pow,
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdegree]
      ring

end HomogeneousEvaluation

section ScalarStableEquations

variable {ι : Type*}

/-- The polynomial in the scalar whose coefficients are evaluations of
the homogeneous components. Its identically zero evaluation will force
each homogeneous component to vanish on a scalar-stable point set. -/
def scalarEvaluationPolynomial (p : MvPolynomial ι ℂ) (v : ι → ℂ) :
    Polynomial ℂ :=
  ∑ d ∈ Finset.range (p.totalDegree + 1),
    Polynomial.monomial d
      (MvPolynomial.eval v (MvPolynomial.homogeneousComponent d p))

theorem scalarEvaluationPolynomial_eval (p : MvPolynomial ι ℂ)
    (v : ι → ℂ) (c : ℂ) :
    (scalarEvaluationPolynomial p v).eval c =
      MvPolynomial.eval (fun i => c * v i) p := by
  classical
  calc
    (scalarEvaluationPolynomial p v).eval c =
        ∑ d ∈ Finset.range (p.totalDegree + 1),
          c ^ d * MvPolynomial.eval v
            (MvPolynomial.homogeneousComponent d p) := by
      simp only [scalarEvaluationPolynomial, Polynomial.eval_finsetSum,
        Polynomial.eval_monomial, mul_comm]
    _ = ∑ d ∈ Finset.range (p.totalDegree + 1),
          MvPolynomial.eval (fun i => c * v i)
            (MvPolynomial.homogeneousComponent d p) := by
      apply Finset.sum_congr rfl
      intro d _hd
      exact (aeval_mul_of_homogeneous v c
        (MvPolynomial.homogeneousComponent_isHomogeneous d p)).symm
    _ = MvPolynomial.eval (fun i => c * v i)
          (∑ d ∈ Finset.range (p.totalDegree + 1),
            MvPolynomial.homogeneousComponent d p) := by
      rw [map_sum]
    _ = MvPolynomial.eval (fun i => c * v i) p := by
      rw [MvPolynomial.sum_homogeneousComponent]

theorem scalarEvaluationPolynomial_coeff (p : MvPolynomial ι ℂ)
    (v : ι → ℂ) (d : ℕ) :
    (scalarEvaluationPolynomial p v).coeff d =
      MvPolynomial.eval v (MvPolynomial.homogeneousComponent d p) := by
  classical
  by_cases hd : d < p.totalDegree + 1
  · simp [scalarEvaluationPolynomial, Polynomial.finsetSum_coeff,
      Polynomial.coeff_monomial, hd]
  · have hzero : MvPolynomial.homogeneousComponent d p = 0 :=
      MvPolynomial.homogeneousComponent_eq_zero d p (by omega)
    simp [scalarEvaluationPolynomial, Polynomial.finsetSum_coeff,
      Polynomial.coeff_monomial, hd, hzero]

/-- The actual ideal of a scalar-stable complex point set is closed
under every homogeneous projection. This is proved from infinitely many
scalar evaluations; homogeneity is not an additional cone hypothesis. -/
theorem homogeneousComponent_mem_vanishingIdeal {ι : Type}
    (S : Set (ι → ℂ))
    (hS : ∀ v ∈ S, ∀ c : ℂ, (fun i => c * v i) ∈ S)
    {p : MvPolynomial ι ℂ} (hp : p ∈ vanishingIdeal S) (d : ℕ) :
    MvPolynomial.homogeneousComponent d p ∈ vanishingIdeal S := by
  intro v hv
  have hzero : scalarEvaluationPolynomial p v = 0 := by
    apply Polynomial.funext
    intro c
    rw [scalarEvaluationPolynomial_eval, Polynomial.eval_zero]
    exact hp _ (hS v hv c)
  have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff d) hzero
  simpa only [scalarEvaluationPolynomial_coeff, Polynomial.coeff_zero] using hcoeff

/-- Polynomial equations of the complex cone remain valid after
rescaling a point over an arbitrary complex algebra by an arbitrary
scalar of that algebra. This includes a nonconstant Laurent scalar. -/
theorem aeval_mul_vanishes {ι : Type}
    (S : Set (ι → ℂ))
    (hS : ∀ v ∈ S, ∀ c : ℂ, (fun i => c * v i) ∈ S)
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (a : ι → A)
    (ha : ∀ p ∈ vanishingIdeal S, MvPolynomial.aeval a p = 0)
    (c : A) {p : MvPolynomial ι ℂ} (hp : p ∈ vanishingIdeal S) :
    MvPolynomial.aeval (fun i => c * a i) p = 0 := by
  classical
  calc
    MvPolynomial.aeval (fun i => c * a i) p =
        MvPolynomial.aeval (fun i => c * a i)
          (∑ d ∈ Finset.range (p.totalDegree + 1),
            MvPolynomial.homogeneousComponent d p) := by
      rw [MvPolynomial.sum_homogeneousComponent]
    _ = ∑ d ∈ Finset.range (p.totalDegree + 1),
          MvPolynomial.aeval (fun i => c * a i)
            (MvPolynomial.homogeneousComponent d p) := by
      rw [map_sum]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro d _hd
      rw [aeval_mul_of_homogeneous a c
        (MvPolynomial.homogeneousComponent_isHomogeneous d p),
        ha _ (homogeneousComponent_mem_vanishingIdeal S hS hp d), mul_zero]

end ScalarStableEquations

section ActualConeArcs

variable {ι : Type}

/-- An algebra point of the actual cone quotient satisfies its original
ambient polynomial equations, over every coefficient algebra. -/
theorem quotientMap_satisfiesEquations
    (S : Set (ι → ℂ)) {A : Type*} [CommRing A] [Algebra ℂ A]
    (a : CoordinateRing S →ₐ[ℂ] A) {p : CoordinatePolynomial ι}
    (hp : p ∈ vanishingIdeal S) :
    MvPolynomial.aeval (fun i => a (coordinate S i)) p = 0 := by
  have hmap : a.comp (Ideal.Quotient.mkₐ ℂ (vanishingIdeal S)) =
      MvPolynomial.aeval (fun i => a (coordinate S i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      MvPolynomial.aeval_X, coordinate]
  rw [← hmap]
  change a (Ideal.Quotient.mk (vanishingIdeal S) p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

/-- Factor the genuinely constructed regular coordinates through the
actual cone quotient. Injectivity of C[[t]] into C((t)) descends the
equations of the rescaled Laurent point. -/
def regularArcOfScaling
    (S : Set (ι → ℂ))
    (hS : ∀ v ∈ S, ∀ c : ℂ, (fun i => c * v i) ∈ S)
    (a : CoordinateRing S →ₐ[ℂ] Meromorphic)
    (c : Meromorphic) (r : ι → Series)
    (hr : ∀ i, seriesInclusion (r i) = c * a (coordinate S i)) :
    CoordinateRing S →ₐ[ℂ] Series :=
  Ideal.Quotient.liftₐ (vanishingIdeal S) (MvPolynomial.aeval r) (by
    intro p hp
    apply seriesInclusion_injective
    rw [map_zero, MvPolynomial.comp_aeval_apply]
    simp only [hr]
    exact aeval_mul_vanishes S hS (fun i => a (coordinate S i))
      (fun _ hp => quotientMap_satisfiesEquations S a hp) c hp)

@[simp]
theorem regularArcOfScaling_coordinate
    (S : Set (ι → ℂ))
    (hS : ∀ v ∈ S, ∀ c : ℂ, (fun i => c * v i) ∈ S)
    (a : CoordinateRing S →ₐ[ℂ] Meromorphic)
    (c : Meromorphic) (r : ι → Series)
    (hr : ∀ i, seriesInclusion (r i) = c * a (coordinate S i)) (i : ι) :
    regularArcOfScaling S hS a c r hr (coordinate S i) = r i := by
  change MvPolynomial.aeval r (MvPolynomial.X i) = r i
  exact MvPolynomial.aeval_X r i

/-- The special point of a formal arc, with its actual complex algebra
map, rather than a separately assigned limit vector. -/
def specialValue : Series →ₐ[ℂ] ℂ where
  __ := PowerSeries.constantCoeff
  commutes' c := by simp

@[simp]
theorem specialValue_apply (r : Series) :
    specialValue r = PowerSeries.constantCoeff r := rfl

theorem regularArcOfScaling_special_mem
    (S : Set (ι → ℂ))
    (hS : ∀ v ∈ S, ∀ c : ℂ, (fun i => c * v i) ∈ S)
    (hclosed : EquationClosed S)
    (a : CoordinateRing S →ₐ[ℂ] Meromorphic)
    (c : Meromorphic) (r : ι → Series)
    (hr : ∀ i, seriesInclusion (r i) = c * a (coordinate S i)) :
    (fun i => PowerSeries.constantCoeff (r i)) ∈ S := by
  have h := quotientPoint_mem S hclosed
    (specialValue.comp (regularArcOfScaling S hS a c r hr))
  simpa only [AlgHom.comp_apply, regularArcOfScaling_coordinate,
    specialValue_apply] using h

end ActualConeArcs

section ConstructedPair

variable {ι : Type} [Fintype ι]

/-- The first cone arc uses the actual maximum pole order of its
coordinate functions. -/
def firstConeArc
    (S : Set (ι → ℂ))
    (hS : ∀ v ∈ S, ∀ c : ℂ, (fun i => c * v i) ∈ S)
    (a : CoordinateRing S →ₐ[ℂ] Meromorphic) :
    CoordinateRing S →ₐ[ℂ] Series :=
  regularArcOfScaling S hS a
    (seriesInclusion (PowerSeries.X : Series) ^
      maximalPoleOrder (fun i => a (coordinate S i)))
    (firstRegularCoordinates (fun i => a (coordinate S i)))
    (firstRegularCoordinates_spec (fun i => a (coordinate S i)))

@[simp]
theorem firstConeArc_coordinate
    (S : Set (ι → ℂ))
    (hS : ∀ v ∈ S, ∀ c : ℂ, (fun i => c * v i) ∈ S)
    (a : CoordinateRing S →ₐ[ℂ] Meromorphic) (i : ι) :
    firstConeArc S hS a (coordinate S i) =
      firstRegularCoordinates (fun j => a (coordinate S j)) i :=
  regularArcOfScaling_coordinate _ _ _ _ _ _ i

/-- The second cone arc is constructed from the fixed-sum equation;
its regularity needs no independent lower-order assumption on b. -/
def secondConeArc
    (S T : Set (ι → ℂ))
    (hT : ∀ v ∈ T, ∀ c : ℂ, (fun i => c * v i) ∈ T)
    (a : CoordinateRing S →ₐ[ℂ] Meromorphic)
    (b : CoordinateRing T →ₐ[ℂ] Meromorphic) (s : ι → ℂ)
    (hfixed : ∀ i, a (coordinate S i) + b (coordinate T i) =
      algebraMap ℂ Meromorphic (s i)) :
    CoordinateRing T →ₐ[ℂ] Series :=
  regularArcOfScaling T hT b
    (-(seriesInclusion (PowerSeries.X : Series) ^
      maximalPoleOrder (fun i => a (coordinate S i))))
    (secondRegularCoordinates (fun i => a (coordinate S i)) s) (by
      intro i
      rw [secondRegularCoordinates_spec
        (fun i => a (coordinate S i)) (fun i => b (coordinate T i)) s hfixed]
      ring)

@[simp]
theorem secondConeArc_coordinate
    (S T : Set (ι → ℂ))
    (hT : ∀ v ∈ T, ∀ c : ℂ, (fun i => c * v i) ∈ T)
    (a : CoordinateRing S →ₐ[ℂ] Meromorphic)
    (b : CoordinateRing T →ₐ[ℂ] Meromorphic) (s : ι → ℂ)
    (hfixed : ∀ i, a (coordinate S i) + b (coordinate T i) =
      algebraMap ℂ Meromorphic (s i)) (i : ι) :
    secondConeArc S T hT a b s hfixed (coordinate T i) =
      secondRegularCoordinates (fun j => a (coordinate S j)) s i :=
  regularArcOfScaling_coordinate _ _ _ _ _ _ i

/-- Closedness now proves that the constructed nonzero limiting vector
belongs to both original cone point sets. The vectors are not merely
limits in an unspecified ambient completion. -/
theorem common_special_value_mem
    (S T : Set (ι → ℂ))
    (hS : ∀ v ∈ S, ∀ c : ℂ, (fun i => c * v i) ∈ S)
    (hT : ∀ v ∈ T, ∀ c : ℂ, (fun i => c * v i) ∈ T)
    (hclosedS : EquationClosed S) (hclosedT : EquationClosed T)
    (a : CoordinateRing S →ₐ[ℂ] Meromorphic)
    (b : CoordinateRing T →ₐ[ℂ] Meromorphic) (s : ι → ℂ)
    (hfixed : ∀ i, a (coordinate S i) + b (coordinate T i) =
      algebraMap ℂ Meromorphic (s i))
    (hpole : ∃ i, (a (coordinate S i)).order < 0) :
    let v := fun i => PowerSeries.constantCoeff
      (firstRegularCoordinates (fun j => a (coordinate S j)) i)
    v ≠ 0 ∧ v ∈ S ∩ T := by
  dsimp only
  refine ⟨first_special_value_ne_zero _ hpole, ?_, ?_⟩
  · have h := quotientPoint_mem S hclosedS
      (specialValue.comp (firstConeArc S hS a))
    simpa only [AlgHom.comp_apply, firstConeArc_coordinate,
      specialValue_apply] using h
  · have h := quotientPoint_mem T hclosedT
      (specialValue.comp (secondConeArc S T hT a b s hfixed))
    simp only [AlgHom.comp_apply, secondConeArc_coordinate,
      specialValue_apply] at h
    rw [← common_special_value _ s hpole] at h
    exact h

/-- All arc maps in the maximal-pole construction are obtained here
from the actual generic cone points. This is the input expected by the
existing diagonal-ideal pole contradiction, before choosing its chart. -/
theorem regular_cone_arcs_exist
    (S T : Set (ι → ℂ))
    (hS : ∀ v ∈ S, ∀ c : ℂ, (fun i => c * v i) ∈ S)
    (hT : ∀ v ∈ T, ∀ c : ℂ, (fun i => c * v i) ∈ T)
    (a : CoordinateRing S →ₐ[ℂ] Meromorphic)
    (b : CoordinateRing T →ₐ[ℂ] Meromorphic) (s : ι → ℂ)
    (hfixed : ∀ i, a (coordinate S i) + b (coordinate T i) =
      algebraMap ℂ Meromorphic (s i))
    (hpole : ∃ i, (a (coordinate S i)).order < 0) :
    ∃ (k : ℕ) (p : CoordinateRing S →ₐ[ℂ] Series)
      (q : CoordinateRing T →ₐ[ℂ] Series), 0 < k ∧
      (∀ i, seriesInclusion (p (coordinate S i)) =
        seriesInclusion (PowerSeries.X : Series) ^ k * a (coordinate S i)) ∧
      (∀ i, seriesInclusion (q (coordinate T i)) =
        -(seriesInclusion (PowerSeries.X : Series) ^ k * b (coordinate T i))) ∧
      (∀ i, p (coordinate S i) - q (coordinate T i) =
        (PowerSeries.X : Series) ^ k * PowerSeries.C (s i)) ∧
      (fun i => PowerSeries.constantCoeff (p (coordinate S i))) =
        (fun i => PowerSeries.constantCoeff (q (coordinate T i))) ∧
      (fun i => PowerSeries.constantCoeff (p (coordinate S i))) ≠ 0 := by
  refine ⟨maximalPoleOrder (fun i => a (coordinate S i)),
    firstConeArc S hS a, secondConeArc S T hT a b s hfixed,
    maximalPoleOrder_pos _ hpole, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [firstConeArc_coordinate]
    exact firstRegularCoordinates_spec _ i
  · intro i
    rw [secondConeArc_coordinate]
    exact secondRegularCoordinates_spec _ _ s hfixed i
  · intro i
    rw [firstConeArc_coordinate, secondConeArc_coordinate]
    exact coordinate_rescaling_difference _ s i
  · simpa only [firstConeArc_coordinate, secondConeArc_coordinate] using
      common_special_value (fun i => a (coordinate S i)) s hpole
  · simpa only [firstConeArc_coordinate] using
      first_special_value_ne_zero (fun i => a (coordinate S i)) hpole

end ConstructedPair

section PrincipalChart

variable {A L : Type*} [CommRing A] [CommRing L]
    [Algebra ℂ A] [Algebra A L] [Algebra ℂ L] [IsScalarTower ℂ A L]

/-- A denominator nonzero at the special point is an actual unit in
C[[t]], so the arc factors through that principal affine chart. -/
def localizeArcAt (p : A →ₐ[ℂ] Series) (u : A)
    (hu : PowerSeries.constantCoeff (p u) ≠ 0)
    [IsLocalization.Away u L] : L →ₐ[ℂ] Series :=
  IsLocalization.Away.liftAlgHom u (f := p)
    (PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hu))

@[simp]
theorem localizeArcAt_algebraMap (p : A →ₐ[ℂ] Series) (u : A)
    (hu : PowerSeries.constantCoeff (p u) ≠ 0)
    [IsLocalization.Away u L] (v : A) :
    localizeArcAt p u hu (algebraMap A L v) = p v := by
  exact IsLocalization.Away.lift_eq u
    (PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hu)) v

end PrincipalChart

section ConstructedContradiction

variable {ι : Type} [Fintype ι]

/-- The local pole contradiction now takes genuine Laurent points,
not already constructed regular arcs, rescaling orders or chart maps.
The chart must contain the constructed special point; its tangent
isotropy and smoothness are the remaining actual geometric inputs. -/
theorem laurent_nonorthogonal_fixed_sum_impossible
    (S : Set (ι → ℂ))
    (hS : ∀ v ∈ S, ∀ c : ℂ, (fun i => c * v i) ∈ S)
    (a b : CoordinateRing S →ₐ[ℂ] Meromorphic) (s : ι → ℂ)
    (hfixed : ∀ i, a (coordinate S i) + b (coordinate S i) =
      algebraMap ℂ Meromorphic (s i))
    (hpole : ∃ i, (a (coordinate S i)).order < 0)
    (u : CoordinateRing S)
    (hu : PowerSeries.constantCoeff (firstConeArc S hS a u) ≠ 0)
    {L : Type*} [CommRing L] [Algebra (CoordinateRing S) L]
    [Algebra ℂ L] [IsScalarTower ℂ (CoordinateRing S) L]
    [IsLocalization.Away u L] [Algebra.FormallySmooth ℂ L]
    (omega : ι → ι → ℂ) (hskew : ∀ i j, omega j i = -omega i j)
    (hisotropic : ∀ (z : L →ₐ[ℂ] ℂ) (D E : Infinitesimal.Tangent L z),
      ConePairing.pairing omega
        (fun i => D.val (ConeRadial.localizedCoordinate (L := L) S i))
        (fun i => E.val (ConeRadial.localizedCoordinate (L := L) S i)) = 0)
    (c : ℂ) (hc : c ≠ 0)
    (hpair : ConePairing.pairing omega
      (fun i => a (coordinate S i)) (fun i => b (coordinate S i)) =
        algebraMap ℂ Meromorphic c) : False := by
  let p : CoordinateRing S →ₐ[ℂ] Series := firstConeArc S hS a
  let q : CoordinateRing S →ₐ[ℂ] Series := secondConeArc S S hS a b s hfixed
  have hspecial : specialValue.comp p = specialValue.comp q := by
    apply quotientPoint_ext S
    intro i
    change PowerSeries.constantCoeff (p (coordinate S i)) =
      PowerSeries.constantCoeff (q (coordinate S i))
    simpa only [p, q, firstConeArc_coordinate, secondConeArc_coordinate] using
      congrFun (common_special_value (fun i => a (coordinate S i)) s hpole) i
  have hqu : PowerSeries.constantCoeff (q u) ≠ 0 := by
    have heq : PowerSeries.constantCoeff (p u) =
        PowerSeries.constantCoeff (q u) :=
      congrArg (fun f : CoordinateRing S →ₐ[ℂ] ℂ => f u) hspecial
    rw [← heq]
    exact hu
  let P : L →ₐ[ℂ] Series := localizeArcAt p u hu
  let Q : L →ₐ[ℂ] Series := localizeArcAt q u hqu
  let k : ℕ := maximalPoleOrder (fun i => a (coordinate S i))
  have hk : 0 < k := maximalPoleOrder_pos _ hpole
  have hp : ∀ i, seriesInclusion
      (P (ConeRadial.localizedCoordinate (L := L) S i)) =
      seriesInclusion (PowerSeries.X : Series) ^ k * a (coordinate S i) := by
    intro i
    change seriesInclusion
      (localizeArcAt p u hu (algebraMap (CoordinateRing S) L (coordinate S i))) = _
    rw [localizeArcAt_algebraMap]
    change seriesInclusion (firstConeArc S hS a (coordinate S i)) = _
    rw [firstConeArc_coordinate]
    exact firstRegularCoordinates_spec _ i
  have hq : ∀ i, seriesInclusion
      (Q (ConeRadial.localizedCoordinate (L := L) S i)) =
      -(seriesInclusion (PowerSeries.X : Series) ^ k * b (coordinate S i)) := by
    intro i
    change seriesInclusion
      (localizeArcAt q u hqu (algebraMap (CoordinateRing S) L (coordinate S i))) = _
    rw [localizeArcAt_algebraMap]
    change seriesInclusion (secondConeArc S S hS a b s hfixed (coordinate S i)) = _
    rw [secondConeArc_coordinate]
    exact secondRegularCoordinates_spec _ _ s hfixed i
  have hrescale : ∀ i,
      P (ConeRadial.localizedCoordinate (L := L) S i) -
      Q (ConeRadial.localizedCoordinate (L := L) S i) =
        (PowerSeries.X : Series) ^ k * PowerSeries.C (s i) := by
    intro i
    change localizeArcAt p u hu
      (algebraMap (CoordinateRing S) L (coordinate S i)) -
      localizeArcAt q u hqu
        (algebraMap (CoordinateRing S) L (coordinate S i)) = _
    rw [localizeArcAt_algebraMap, localizeArcAt_algebraMap]
    change firstConeArc S hS a (coordinate S i) -
      secondConeArc S S hS a b s hfixed (coordinate S i) = _
    rw [firstConeArc_coordinate, secondConeArc_coordinate]
    exact coordinate_rescaling_difference _ s i
  have hcone : ConeRadial.IsCone S := by
    intro v hv d
    change (fun i => d * v i) ∈ S
    exact hS v hv d
  exact ConeIsotropy.rescaled_nonorthogonal_arcs_impossible_of_tangent_isotropy
    S hcone u omega hskew hisotropic P Q k hk s hrescale
    seriesInclusion seriesInclusion_injective
    (fun i => a (coordinate S i)) (fun i => b (coordinate S i)) c hc hp hq hpair

end ConstructedContradiction

end LeBrunSalamon.Construction.Lines.LaurentRescaling

end
