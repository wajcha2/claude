import LSHomVelocity

/-!
# The actual epsilon structure sequence on every thickened open

The maps below are multiplication by the fixed epsilon followed by the
actual source pullback, and the actual zero-section restriction.  This is
the sectionwise algebra needed to assemble the sheaf short exact sequence.
There are no new admissions in this file.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

open CategoryTheory AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.Skeleton
open LeBrunSalamon.Construction.Lines.DualThickening

namespace LeBrunSalamon.DualHomVanishing

variable {Y : Scheme} (sY : Y ⟶ ComplexBase)

/-- The fixed epsilon inclusion on the inverse image of an arbitrary open. -/
def epsilonInclusion (U : Y.Opens) (a : RingSections Y U) :
    RingSections (space sY) (projection sY ⁻¹ᵁ U) :=
  epsilonOn sY U * (projection sY).app U a

theorem epsilonInclusion_normalForm (U : Y.Opens) (a : RingSections Y U) :
    epsilonInclusion sY U a = normalForm sY U 0 a := by
  simp only [epsilonInclusion, normalForm, map_zero, zero_add]

theorem epsilonInclusion_injective (U : Y.Opens) :
    Function.Injective (epsilonInclusion sY U) := by
  intro a b h
  have hc := congrArg (coefficient sY U) h
  simpa only [epsilonInclusion_normalForm, coefficient_normalForm] using hc

theorem reductionHom_surjective (U : Y.Opens) :
    Function.Surjective (reductionHom sY U) := by
  intro a
  exact ⟨(projection sY).app U a, reductionHom_projection sY U a⟩

/-- The kernel is precisely the image of the prescribed epsilon map. -/
theorem reductionHom_zero_iff (U : Y.Opens)
    (z : RingSections (space sY) (projection sY ⁻¹ᵁ U)) :
    reductionHom sY U z = 0 ↔ ∃ a : RingSections Y U, epsilonInclusion sY U a = z := by
  constructor
  · intro hz
    refine ⟨coefficient sY U z, ?_⟩
    conv_rhs => rw [reconstruct sY U z, reductionCoefficient_eq_reductionHom, hz]
    exact epsilonInclusion_normalForm sY U _
  · rintro ⟨a, rfl⟩
    rw [epsilonInclusion_normalForm, reductionHom_normalForm]

/-- The source of epsilon inclusion carries the scalar action through
actual zero-section restriction. This is its required O-linearity. -/
theorem epsilonInclusion_scalar (U : Y.Opens)
    (r : RingSections (space sY) (projection sY ⁻¹ᵁ U)) (a : RingSections Y U) :
    epsilonInclusion sY U (reductionHom sY U r * a) = r * epsilonInclusion sY U a := by
  rw [epsilonInclusion_normalForm, epsilonInclusion_normalForm]
  conv_rhs => rw [reconstruct sY U r, normalForm_mul]
  simp only [mul_zero, zero_mul, add_zero, reductionCoefficient_eq_reductionHom]

theorem epsilonInclusion_restrict {U V : Y.Opens} (i : U ⟶ V)
    (a : RingSections Y V) :
    (space sY).presheaf.map
      (((TopologicalSpace.Opens.map (projection sY).base).map i).op)
      (epsilonInclusion sY V a) =
        epsilonInclusion sY U (Y.presheaf.map i.op a) := by
  rw [epsilonInclusion_normalForm, normalForm_restrict, map_zero,
    epsilonInclusion_normalForm]

end LeBrunSalamon.DualHomVanishing
end
