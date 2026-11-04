import LSAffineFrame

/-!
An actual sheaf section restricted to a power of a scheme-theoretic kernel
vanishes exactly when its coefficient in the specified affine frame is zero
in the actual ideal quotient.  This is a proved map comparison; no affine
diagonal or project-specific statement is admitted.  Native checking pending.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.ClosedIdealCoefficients

theorem kernelPower_app_kernel {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f]
    (U : Y.Opens) (hU : IsAffineOpen U) (k : ℕ) :
    RingHom.ker (((f.ker ^ k).subschemeι).app U).hom =
      (RingHom.ker (f.app U).hom) ^ k := by
  rw [(f.ker ^ k).ker_subschemeι_app ⟨U, hU⟩]
  change (f.ker.ideal ⟨U, hU⟩) ^ k = _
  rw [f.ker_apply ⟨U, hU⟩]

theorem kernelPower_app_surjective {X Y : Scheme} (f : X ⟶ Y)
    (U : Y.Opens) (hU : IsAffineOpen U) (k : ℕ) :
    Function.Surjective (((f.ker ^ k).subschemeι).app U).hom :=
  (f.ker ^ k).subschemeι_app_surjective ⟨U, hU⟩

def kernelPowerQuotientEquiv {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f]
    (U : Y.Opens) (hU : IsAffineOpen U) (k : ℕ) :
    (RingSections Y U ⧸ (RingHom.ker (f.app U).hom) ^ k) ≃+*
      RingSections (f.ker ^ k).subscheme ((f.ker ^ k).subschemeι ⁻¹ᵁ U) :=
  (Ideal.quotEquivOfEq (kernelPower_app_kernel f U hU k).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := (((f.ker ^ k).subschemeι).app U).hom)
      (kernelPower_app_surjective f U hU k))

@[simp] theorem kernelPowerQuotientEquiv_mk {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f]
    (U : Y.Opens) (hU : IsAffineOpen U) (k : ℕ) (a : RingSections Y U) :
    kernelPowerQuotientEquiv f U hU k
      (Ideal.Quotient.mk ((RingHom.ker (f.app U).hom) ^ k) a) =
        (((f.ker ^ k).subschemeι).app U).hom a := by
  simp only [kernelPowerQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

theorem kernelPower_app_eq_zero_iff {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f]
    (U : Y.Opens) (hU : IsAffineOpen U) (k : ℕ) (a : RingSections Y U) :
    (((f.ker ^ k).subschemeι).app U).hom a = 0 ↔
      Ideal.Quotient.mk ((RingHom.ker (f.app U).hom) ^ k) a = 0 := by
  rw [← kernelPowerQuotientEquiv_mk f U hU k a,
    ← map_zero (kernelPowerQuotientEquiv f U hU k),
    (kernelPowerQuotientEquiv f U hU k).injective.eq_iff]

/-- This keeps both the actual ambient section and the actual restriction
map to V(ker(f)^k), for every k including zero. -/
theorem section_zero_iff_quotient {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f]
    {E : OModule Y} (U : Y.Opens) (hU : IsAffineOpen U)
    (e : LocalFrames.OverFrame E U) (a : AlgebraicSection E) (k : ℕ) :
    (Scheme.Modules.pullback
      ((((f.ker ^ k).subschemeι) ⁻¹ᵁ U).ι ≫ (f.ker ^ k).subschemeι)).map a = 0 ↔
      Ideal.Quotient.mk ((RingHom.ker (f.app U).hom) ^ k)
        (LocalFrames.coordinates e (Scheme.Modules.Hom.app a U (1 : RingSections Y U))) = 0 := by
  rw [AffineFrameProof.pullbackOnOpen_eq_zero_iff_coefficient]
  exact kernelPower_app_eq_zero_iff f U hU k _

end LeBrunSalamon.ClosedIdealCoefficients

end
