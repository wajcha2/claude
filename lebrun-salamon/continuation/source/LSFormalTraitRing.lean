import Mathlib

/-! The actual power-series coefficient ring satisfies the algebraic
hypotheses of the strictly Henselian conic normal-form theorem. All facts
are proved from the pinned Mathlib completeness, Hensel, and residue-field
APIs. No conic classification or geometric normal form is included here.
No admission. -/

noncomputable section
set_option autoImplicit false

namespace LeBrunSalamon.FormalTraitRing

variable (K : Type) [Field K]

theorem completeAtMaximal :
    IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries K)) (PowerSeries K) := by
  rw [PowerSeries.maximalIdeal_eq_span_X]
  infer_instance

/-- Hensel lifting in the original power-series ring, through its actual
maximal ideal. This retains nilpotent orders and arbitrary smoothing units. -/
theorem henselian : HenselianLocalRing (PowerSeries K) := by
  letI := completeAtMaximal K
  exact {
    toIsLocalRing := inferInstance
    is_henselian := fun f hf a ha hder =>
      HenselianRing.is_henselian f hf a ha
        (hder.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (PowerSeries K)))) }

theorem noetherian : IsNoetherianRing (PowerSeries K) := inferInstance

def residueEquiv : IsLocalRing.ResidueField (PowerSeries K) ≃+* K :=
  PowerSeries.residueFieldOfPowerSeries

theorem residue_algebraicallyClosed [IsAlgClosed K] :
    IsAlgClosed (IsLocalRing.ResidueField (PowerSeries K)) :=
  IsAlgClosed.of_ringEquiv K _ (residueEquiv K).symm

/-- The residue-zero condition in the source theorem is literally zero
constant coefficient in the frozen trait statement. -/
theorem mem_maximal_iff_constantCoeff (a : PowerSeries K) :
    a ∈ IsLocalRing.maximalIdeal (PowerSeries K) ↔ PowerSeries.constantCoeff a = 0 := by
  rw [← PowerSeries.ker_coeff_eq_max_ideal]
  rfl

theorem complex_residue_two_ne_zero :
    (2 : IsLocalRing.ResidueField (PowerSeries ℂ)) ≠ 0 := by
  intro h
  have hh : (2 : ℂ) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (residueEquiv ℂ) h
  norm_num at hh

end LeBrunSalamon.FormalTraitRing
end
