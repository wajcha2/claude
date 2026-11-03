import RecompileExtensionsPart01

/-!
Auxiliary actual-scheme comparisons for the Step 3c diagonal restriction proof.
This work file is outside the source graph until native checking. It does not
replace the unproved frame/tensor-coordinate comparison by an admission.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.Core

namespace LeBrunSalamon.DiagonalLocalProof

/-- The affine quotient kernel for the actual power of an arbitrary closed
immersion's scheme-theoretic kernel. This includes the diagonal and all k. -/
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

/-- The ring isomorphism retains the actual ambient restriction map. -/
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

/-- The same frame is used in both factors; these opens need only cover the
support of the diagonal thickening, not the entire product. -/
def frameSquareOpen {X : Scheme} (s : X ⟶ ComplexBase) {L : LineBundle X}
    (F : AffineLineFrame L) : (SelfProduct s).Opens :=
  firstProjection s ⁻¹ᵁ F.openSet ⊓ secondProjection s ⁻¹ᵁ F.openSet

theorem diagonal_frameSquare_mem {X : Scheme} (s : X ⟶ ComplexBase)
    {L : LineBundle X} (F : AffineLineFrame L) (x : X)
    (hx : x ∈ F.openSet) : diagonal s x ∈ frameSquareOpen s F := by
  constructor
  · change (diagonal s ≫ firstProjection s) x ∈ F.openSet
    rw [pullback.diagonal_fst]
    exact hx
  · change (diagonal s ≫ secondProjection s) x ∈ F.openSet
    rw [pullback.diagonal_snd]
    exact hx

theorem diagonalThickening_frameSquares_cover {X : Scheme}
    (s : X ⟶ ComplexBase) [IsSeparated s] (L : LineBundle X)
    (k : ℕ) (hk : k ≠ 0) :
    (⨆ F : AffineLineFrame L,
      diagonalPowerInclusion s k ⁻¹ᵁ frameSquareOpen s F) = ⊤ := by
  apply top_unique
  intro z _
  have hz : diagonalPowerInclusion s k z ∈ Set.range (diagonal s) := by
    rw [← FatPointOpenFactorizationProof.kernelPowerInclusion_range (diagonal s) k hk]
    exact ⟨z, rfl⟩
  obtain ⟨x, hx⟩ := hz
  obtain ⟨F, hF⟩ := affineLineFrames_cover L x
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨F, ?_⟩
  change diagonalPowerInclusion s k z ∈ frameSquareOpen s F
  rw [← hx]
  exact diagonal_frameSquare_mem s F x hF

end LeBrunSalamon.DiagonalLocalProof

end
