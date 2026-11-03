import LSCurveFunctionField
import LSCurveLaurentStandardInputs
import LSConeRescaledArcs
import LSConeOpen

/-!
## Laurent coordinates and regular cone arcs of the selected curve

The only new literature boundary used here is the independently reviewed
classical Laurent expansion theorem in `LSCurveLaurentStandardInputs`.
The curve, its function field, both cone maps, the fixed sum, and the
nonconstant coordinate have already been constructed. This file chooses
that coordinate's Laurent expansion and builds both actual regular arcs
by maximal-pole rescaling. Their common nonzero special value lies in the
original cones. For disjoint projective components it identifies the
component indices.

SOURCE ONLY, UNCOMPILED. This file introduces no admissions.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace LeBrunSalamon.Construction.Lines.AffineCurveSelection

open DirectionCones LaurentRescaling

section LaurentCurve

variable {ι : Type} [Fintype ι]
variable (S T : Set (ι → ℂ)) (s : ι → ℂ) (omega : ι → ι → ℂ)
    (hdim : 1 ≤ ringKrullDim (NonorthogonalFiberRing S T s omega))

/-- The classical input is applied to the actual dimension-one prime
quotient and an original cone coordinate proved nonconstant there. -/
theorem curveLaurentEmbedding_exists :
    ∃ j : NonorthogonalFunctionField S T s omega hdim →ₐ[ℂ] Meromorphic,
      ∃ i, (j (functionFirst S T s omega hdim (coordinate S i))).order < 0 := by
  obtain ⟨i, hi⟩ := nonorthogonalCurveFirst_nonconstant S T s omega hdim
  obtain ⟨j, hj⟩ := CurveStandardInputs.exists_laurent_expansion_with_pole
    (CurveRing (NonorthogonalFiberRing S T s omega) hdim)
    (curveRing_dimension _ hdim)
    (nonorthogonalCurveFirst S T s omega hdim (coordinate S i)) hi
  exact ⟨j, i, hj⟩

def curveLaurentEmbedding :
    NonorthogonalFunctionField S T s omega hdim →ₐ[ℂ] Meromorphic :=
  Classical.choose (curveLaurentEmbedding_exists S T s omega hdim)

theorem curveLaurentEmbedding_injective :
    Function.Injective (curveLaurentEmbedding S T s omega hdim) :=
  (curveLaurentEmbedding S T s omega hdim).injective

def laurentFirst : CoordinateRing S →ₐ[ℂ] Meromorphic :=
  (curveLaurentEmbedding S T s omega hdim).comp (functionFirst S T s omega hdim)

def laurentSecond : CoordinateRing T →ₐ[ℂ] Meromorphic :=
  (curveLaurentEmbedding S T s omega hdim).comp (functionSecond S T s omega hdim)

theorem laurentFirst_has_pole :
    ∃ i, (laurentFirst S T s omega hdim (coordinate S i)).order < 0 :=
  Classical.choose_spec (curveLaurentEmbedding_exists S T s omega hdim)

theorem laurent_fixedSum_equation (i : ι) :
    laurentFirst S T s omega hdim (coordinate S i) +
      laurentSecond S T s omega hdim (coordinate T i) =
        algebraMap ℂ Meromorphic (s i) := by
  let j := curveLaurentEmbedding S T s omega hdim
  exact (RingHom.map_add j.toRingHom
      (functionFirst S T s omega hdim (coordinate S i))
      (functionSecond S T s omega hdim (coordinate T i))).symm.trans
    ((congrArg j (function_fixedSum_equation S T s omega hdim i)).trans
      (j.commutes (s i)))

theorem laurent_pairing_ne_zero :
    ConePairing.pairing omega
      (fun i => laurentFirst S T s omega hdim (coordinate S i))
      (fun i => laurentSecond S T s omega hdim (coordinate T i)) ≠ 0 := by
  intro hzero
  apply function_pairing_ne_zero S T s omega hdim
  apply curveLaurentEmbedding_injective S T s omega hdim
  rw [ConePairing.pairing_map, map_zero]
  exact hzero

theorem laurent_pairing_eq_scalar (c : ℂ)
    (hc : ConePairing.pairing omega
      (fun i => functionFirst S T s omega hdim (coordinate S i))
      (fun i => functionSecond S T s omega hdim (coordinate T i)) =
        algebraMap ℂ (NonorthogonalFunctionField S T s omega hdim) c) :
    ConePairing.pairing omega
      (fun i => laurentFirst S T s omega hdim (coordinate S i))
      (fun i => laurentSecond S T s omega hdim (coordinate T i)) =
        algebraMap ℂ Meromorphic c := by
  change ConePairing.pairing omega
    (fun i => curveLaurentEmbedding S T s omega hdim
      (functionFirst S T s omega hdim (coordinate S i)))
    (fun i => curveLaurentEmbedding S T s omega hdim
      (functionSecond S T s omega hdim (coordinate T i))) =
    algebraMap ℂ Meromorphic c
  have h := congrArg (curveLaurentEmbedding S T s omega hdim) hc
  simpa only [ConePairing.pairing_map, AlgHom.commutes] using h

/-- The positive integer is computed from the orders of the actual
Laurent coordinates; it is not supplied by a geometric certificate. -/
def curvePoleOrder : ℕ :=
  maximalPoleOrder (fun i => laurentFirst S T s omega hdim (coordinate S i))

theorem curvePoleOrder_pos : 0 < curvePoleOrder S T s omega hdim :=
  maximalPoleOrder_pos _ (laurentFirst_has_pole S T s omega hdim)

def curveFirstArc
    (hS : ∀ v ∈ S, ∀ c : ℂ, (fun i => c * v i) ∈ S) :
    CoordinateRing S →ₐ[ℂ] ConePole.Series :=
  firstConeArc S hS (laurentFirst S T s omega hdim)

def curveSecondArc
    (hT : ∀ v ∈ T, ∀ c : ℂ, (fun i => c * v i) ∈ T) :
    CoordinateRing T →ₐ[ℂ] ConePole.Series :=
  secondConeArc S T hT (laurentFirst S T s omega hdim)
    (laurentSecond S T s omega hdim) s (laurent_fixedSum_equation S T s omega hdim)

def curveLimit : ι → ℂ :=
  fun i => PowerSeries.constantCoeff
    (firstRegularCoordinates (fun j => laurentFirst S T s omega hdim (coordinate S j)) i)

theorem curveLimit_ne_zero : curveLimit S T s omega hdim ≠ 0 :=
  first_special_value_ne_zero _ (laurentFirst_has_pole S T s omega hdim)

theorem curveLimit_mem
    (hS : ∀ v ∈ S, ∀ c : ℂ, (fun i => c * v i) ∈ S)
    (hT : ∀ v ∈ T, ∀ c : ℂ, (fun i => c * v i) ∈ T)
    (hclosedS : EquationClosed S) (hclosedT : EquationClosed T) :
    curveLimit S T s omega hdim ∈ S ∩ T :=
  (common_special_value_mem S T hS hT hclosedS hclosedT
    (laurentFirst S T s omega hdim) (laurentSecond S T s omega hdim) s
    (laurent_fixedSum_equation S T s omega hdim)
    (laurentFirst_has_pole S T s omega hdim)).2

/-- Complete curve-to-arc construction. The regular maps and common
nonzero cone point are produced from a positive-dimensional actual fiber. -/
theorem curve_regular_arcs
    (hS : ∀ v ∈ S, ∀ c : ℂ, (fun i => c * v i) ∈ S)
    (hT : ∀ v ∈ T, ∀ c : ℂ, (fun i => c * v i) ∈ T) :
    let k := curvePoleOrder S T s omega hdim
    let p := curveFirstArc S T s omega hdim hS
    let q := curveSecondArc S T s omega hdim hT
    0 < k ∧
      (∀ i, seriesInclusion (p (coordinate S i)) =
        seriesInclusion (PowerSeries.X : ConePole.Series) ^ k *
          laurentFirst S T s omega hdim (coordinate S i)) ∧
      (∀ i, seriesInclusion (q (coordinate T i)) =
        -(seriesInclusion (PowerSeries.X : ConePole.Series) ^ k *
          laurentSecond S T s omega hdim (coordinate T i))) ∧
      (∀ i, p (coordinate S i) - q (coordinate T i) =
        (PowerSeries.X : ConePole.Series) ^ k * PowerSeries.C (s i)) ∧
      (fun i => PowerSeries.constantCoeff (p (coordinate S i))) =
        (fun i => PowerSeries.constantCoeff (q (coordinate T i))) ∧
      (fun i => PowerSeries.constantCoeff (p (coordinate S i))) ≠ 0 := by
  dsimp only
  refine ⟨curvePoleOrder_pos S T s omega hdim, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    change seriesInclusion
      (firstConeArc S hS (laurentFirst S T s omega hdim) (coordinate S i)) = _
    rw [firstConeArc_coordinate]
    exact firstRegularCoordinates_spec _ i
  · intro i
    change seriesInclusion (secondConeArc S T hT
      (laurentFirst S T s omega hdim) (laurentSecond S T s omega hdim) s
      (laurent_fixedSum_equation S T s omega hdim) (coordinate T i)) = _
    rw [secondConeArc_coordinate]
    exact secondRegularCoordinates_spec _ _ s
      (laurent_fixedSum_equation S T s omega hdim) i
  · intro i
    change firstConeArc S hS (laurentFirst S T s omega hdim) (coordinate S i) -
      secondConeArc S T hT (laurentFirst S T s omega hdim)
        (laurentSecond S T s omega hdim) s
        (laurent_fixedSum_equation S T s omega hdim) (coordinate T i) = _
    rw [firstConeArc_coordinate, secondConeArc_coordinate]
    exact coordinate_rescaling_difference _ s i
  · simpa only [curveFirstArc, curveSecondArc,
      firstConeArc_coordinate, secondConeArc_coordinate] using
      common_special_value
        (fun i => laurentFirst S T s omega hdim (coordinate S i)) s
        (laurentFirst_has_pole S T s omega hdim)
  · simpa only [curveFirstArc, firstConeArc_coordinate] using
      first_special_value_ne_zero
        (fun i => laurentFirst S T s omega hdim (coordinate S i))
        (laurentFirst_has_pole S T s omega hdim)

end LaurentCurve

section ProjectiveComponents

variable {N : ℕ} (D : ReducedProjectiveDirections N)
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (e : V ≃ₗ[ℂ] (Fin (N+1) → ℂ))

/-- If a nonorthogonal fixed-sum fiber of two component cones had
positive dimension, its actual rescaled curve limit would force the
component indices to agree. This uses projective component separation,
not a premise that the entire direction variety is irreducible. -/
theorem component_eq_of_positive_nonorthogonalFiber
    (hdisj : Pairwise (fun C E : D.Component => Disjoint C.val E.val))
    (C E : D.Component)
    (hclosedC : EquationClosed (D.componentConePoints e C))
    (hclosedE : EquationClosed (D.componentConePoints e E))
    (s : Fin (N+1) → ℂ) (omega : Fin (N+1) → Fin (N+1) → ℂ)
    (hdim : 1 ≤ ringKrullDim (NonorthogonalFiberRing
      (D.componentConePoints e C) (D.componentConePoints e E) s omega)) : C = E := by
  have hscale (A : D.Component) : ∀ v ∈ D.componentConePoints e A,
      ∀ c : ℂ, (fun i => c * v i) ∈ D.componentConePoints e A := by
    intro v hv c
    exact D.componentConePoints_smul e A hv c
  have hv := curveLimit_mem (D.componentConePoints e C) (D.componentConePoints e E)
    s omega hdim (hscale C) (hscale E) hclosedC hclosedE
  exact ConeGeometry.component_eq_of_common_nonzero D e hdisj
    (curveLimit_ne_zero _ _ s omega hdim) hv.1 hv.2

end ProjectiveComponents

end LeBrunSalamon.Construction.Lines.AffineCurveSelection

end

