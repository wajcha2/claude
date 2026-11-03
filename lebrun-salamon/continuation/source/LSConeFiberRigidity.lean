import LSAdditionFiberPresentation
import LSCurveLaurentGeometry

/-!
## Positive-dimensional nonorthogonal cone fibers are impossible

This is the global curve-and-pole argument from `lines:cone-addition`,
starting from the actual nonorthogonal fiber ring. The integral curve,
its complex point, its function field, a Laurent expansion with a pole,
regular rescaled arcs, and the common nonzero limit are all constructed.
The constant pairing is proved by the existing characteristic-zero
field-differential theorem and actual smooth isotropic cone charts.

The remaining geometric hypotheses are exactly closed projective
component cones, component separation, and smooth isotropic principal
charts away from the cone vertex. They are not dominance, pole, arc, or
curve certificates. Their production from the actual VMRT remains an
independent construction. The fiber-dimension-to-dominance step is also
not asserted by this file.

SOURCE ONLY, UNCOMPILED. No new admission occurs in this file.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace LeBrunSalamon.Construction.Lines.AffineCurveSelection

open DirectionCones LaurentRescaling

section GenericChartSelection

variable {ι : Type} [Fintype ι]

/-- Smooth isotropic principal charts at actual nonzero complex points
suffice to prove constant pairing on the function field of the selected
curve. The two generic chart maps are constructed, not supplied. -/
theorem selectedFunction_pairing_constant_of_chart_geometry
    (S T : Set (ι → ℂ)) (hS : ConeRadial.IsCone S) (hT : ConeRadial.IsCone T)
    (s : ι → ℂ) (omega : ι → ι → ℂ)
    (hskew : ∀ i j, omega j i = -omega i j)
    (hchartsS : ∀ p : CoordinateRing S →ₐ[ℂ] ℂ,
      (fun i => p (coordinate S i)) ≠ 0 →
        ∃ u : CoordinateRing S, p u ≠ 0 ∧
          Algebra.FormallySmooth ℂ (Localization.Away u) ∧
          ∀ (z : Localization.Away u →ₐ[ℂ] ℂ)
            (D E : Infinitesimal.Tangent (Localization.Away u) z),
            ConePairing.pairing omega
              (fun i => D.val (ConeRadial.localizedCoordinate (L := Localization.Away u) S i))
              (fun i => E.val (ConeRadial.localizedCoordinate (L := Localization.Away u) S i)) = 0)
    (hchartsT : ∀ p : CoordinateRing T →ₐ[ℂ] ℂ,
      (fun i => p (coordinate T i)) ≠ 0 →
        ∃ v : CoordinateRing T, p v ≠ 0 ∧
          Algebra.FormallySmooth ℂ (Localization.Away v) ∧
          ∀ (z : Localization.Away v →ₐ[ℂ] ℂ)
            (D E : Infinitesimal.Tangent (Localization.Away v) z),
            ConePairing.pairing omega
              (fun i => D.val (ConeRadial.localizedCoordinate (L := Localization.Away v) T i))
              (fun i => E.val (ConeRadial.localizedCoordinate (L := Localization.Away v) T i)) = 0)
    (hdim : 1 ≤ ringKrullDim (NonorthogonalFiberRing S T s omega)) :
    ∃ c : ℂ, c ≠ 0 ∧ ConePairing.pairing omega
      (fun i => functionFirst S T s omega hdim (coordinate S i))
      (fun i => functionSecond S T s omega hdim (coordinate T i)) =
        algebraMap ℂ (NonorthogonalFunctionField S T s omega hdim) c := by
  let p := curveComplexPoint (NonorthogonalFiberRing S T s omega) hdim
  let a : CoordinateRing S →ₐ[ℂ] ℂ :=
    p.comp (nonorthogonalCurveFirst S T s omega hdim)
  let b : CoordinateRing T →ₐ[ℂ] ℂ :=
    p.comp (nonorthogonalCurveSecond S T s omega hdim)
  have hab := CurvePairing.coordinates_nonzero_at_every_point omega
    (fun i => nonorthogonalCurveFirst S T s omega hdim (coordinate S i))
    (fun i => nonorthogonalCurveSecond S T s omega hdim (coordinate T i))
    (nonorthogonalCurve_pairing_isUnit S T s omega hdim) p
  have ha : (fun i => a (coordinate S i)) ≠ 0 := hab.1
  have hb : (fun i => b (coordinate T i)) ≠ 0 := hab.2
  obtain ⟨u, hu, hsmoothU, hisotropicU⟩ := hchartsS a ha
  obtain ⟨v, hv, hsmoothV, hisotropicV⟩ := hchartsT b hb
  letI : Algebra.FormallySmooth ℂ (Localization.Away u) := hsmoothU
  letI : Algebra.FormallySmooth ℂ (Localization.Away v) := hsmoothV
  have huField : functionFirst S T s omega hdim u ≠ 0 := by
    exact curveFunctionInclusion_ne_zero_of_point
      (NonorthogonalFiberRing S T s omega) hdim
      (nonorthogonalCurveFirst S T s omega hdim u) hu
  have hvField : functionSecond S T s omega hdim v ≠ 0 := by
    exact curveFunctionInclusion_ne_zero_of_point
      (NonorthogonalFiberRing S T s omega) hdim
      (nonorthogonalCurveSecond S T s omega hdim v) hv
  exact function_pairing_eq_nonzero_complexScalar S T s omega hdim hS hT hskew
    u v huField hvField hisotropicU hisotropicV

end GenericChartSelection

section OneCone

variable {ι : Type} [Fintype ι]

/-- For one actual cone smooth and isotropic away from its vertex,
every nonorthogonal fixed-sum fiber has dimension less than one. This is
the manuscript's complete curve-and-pole contradiction for that cone. -/
theorem nonorthogonalFiber_not_positiveDim_of_chart_geometry
    (S : Set (ι → ℂ)) (hS : ConeRadial.IsCone S)
    (omega : ι → ι → ℂ) (hskew : ∀ i j, omega j i = -omega i j)
    (hcharts : ∀ p : CoordinateRing S →ₐ[ℂ] ℂ,
      (fun i => p (coordinate S i)) ≠ 0 →
        ∃ u : CoordinateRing S, p u ≠ 0 ∧
          Algebra.FormallySmooth ℂ (Localization.Away u) ∧
          ∀ (z : Localization.Away u →ₐ[ℂ] ℂ)
            (D E : Infinitesimal.Tangent (Localization.Away u) z),
            ConePairing.pairing omega
              (fun i => D.val (ConeRadial.localizedCoordinate (L := Localization.Away u) S i))
              (fun i => E.val (ConeRadial.localizedCoordinate (L := Localization.Away u) S i)) = 0)
    (s : ι → ℂ) :
    ¬ 1 ≤ ringKrullDim (NonorthogonalFiberRing S S s omega) := by
  intro hdim
  have hscale : ∀ v ∈ S, ∀ c : ℂ, (fun i => c * v i) ∈ S := by
    intro v hv c
    exact hS v hv c
  obtain ⟨c, hc, hpair⟩ := selectedFunction_pairing_constant_of_chart_geometry
    S S hS hS s omega hskew hcharts hcharts hdim
  let a := laurentFirst S S s omega hdim
  let b := laurentSecond S S s omega hdim
  let p : CoordinateRing S →ₐ[ℂ] ℂ :=
    specialValue.comp (firstConeArc S hscale a)
  have hp : (fun i => p (coordinate S i)) ≠ 0 := by
    change (fun i => PowerSeries.constantCoeff
      (firstConeArc S hscale a (coordinate S i))) ≠ 0
    simpa only [firstConeArc_coordinate] using
      (first_special_value_ne_zero (fun i => a (coordinate S i))
        (laurentFirst_has_pole S S s omega hdim))
  obtain ⟨u, hu, hsmooth, hisotropic⟩ := hcharts p hp
  letI : Algebra.FormallySmooth ℂ (Localization.Away u) := hsmooth
  exact laurent_nonorthogonal_fixed_sum_impossible S hscale a b s
    (laurent_fixedSum_equation S S s omega hdim)
    (laurentFirst_has_pole S S s omega hdim) u hu
    (L := Localization.Away u) omega hskew hisotropic c hc
    (laurent_pairing_eq_scalar S S s omega hdim c hpair)

end OneCone

section ProjectiveComponents

variable {N : ℕ} (D : ReducedProjectiveDirections N)
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (e : V ≃ₗ[ℂ] (Fin (N+1) → ℂ))

/-- The conclusion retains the original two component indices. A
positive-dimensional fiber first constructs a common nonzero limit and
hence proves equality of those indices; the same-cone pole contradiction
then applies. No irreducibility of the full VMRT is used. -/
theorem component_nonorthogonalFiber_not_positiveDim
    (hdisj : Pairwise (fun C E : D.Component => Disjoint C.val E.val))
    (hclosed : ∀ C : D.Component, EquationClosed (D.componentConePoints e C))
    (omega : Fin (N+1) → Fin (N+1) → ℂ)
    (hskew : ∀ i j, omega j i = -omega i j)
    (hcharts : ∀ (C : D.Component) (p : CoordinateRing (D.componentConePoints e C) →ₐ[ℂ] ℂ),
      (fun i => p (coordinate (D.componentConePoints e C) i)) ≠ 0 →
        ∃ u : CoordinateRing (D.componentConePoints e C), p u ≠ 0 ∧
          Algebra.FormallySmooth ℂ (Localization.Away u) ∧
          ∀ (z : Localization.Away u →ₐ[ℂ] ℂ)
            (A B : Infinitesimal.Tangent (Localization.Away u) z),
            ConePairing.pairing omega
              (fun i => A.val (ConeRadial.localizedCoordinate (L := Localization.Away u)
                (D.componentConePoints e C) i))
              (fun i => B.val (ConeRadial.localizedCoordinate (L := Localization.Away u)
                (D.componentConePoints e C) i)) = 0)
    (C E : D.Component) (s : Fin (N+1) → ℂ) :
    ¬ 1 ≤ ringKrullDim (NonorthogonalFiberRing
      (D.componentConePoints e C) (D.componentConePoints e E) s omega) := by
  intro hdim
  have hCE : C = E := component_eq_of_positive_nonorthogonalFiber D e hdisj
    C E (hclosed C) (hclosed E) s omega hdim
  subst E
  exact nonorthogonalFiber_not_positiveDim_of_chart_geometry
    (D.componentConePoints e C) (fun v hv c => D.componentConePoints_smul e C hv c)
    omega hskew (hcharts C) s hdim

end ProjectiveComponents

end LeBrunSalamon.Construction.Lines.AffineCurveSelection

end

