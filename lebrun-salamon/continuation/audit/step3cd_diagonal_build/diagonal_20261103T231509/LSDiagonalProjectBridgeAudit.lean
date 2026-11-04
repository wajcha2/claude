import RecompileExtensionsPart01
import LSExternalFrameCoefficients

/-!
Candidate replacement for the exact original Step 3c diagonal wrapper.
The imported historical admission is not used in this proof.  This file is
only a diagnostic candidate until the generic helper chain compiles; the
proof will then be transplanted into the original declaration.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open scoped TensorProduct

namespace LeBrunSalamon.Core.ExternalTensorCoordinates

theorem diagonalRestriction_iff_quotientCoefficients_proved {Y : Scheme}
    (s : Y ⟶ ComplexBase) [IsSeparated s] (L : LineBundle Y)
    (t : ComplexSections s L.sheaf ⊗[ℂ] ComplexSections s L.sheaf) (k : ℕ) :
    VanishesToOrderAlongDiagonal s (externalSquareLine s L).sheaf
      (sectionFromValue (globalTensorMap s L.sheaf L.sheaf t)) k ↔
    ∀ F : AffineLineFrame L,
      Ideal.Quotient.mk ((KaehlerDifferential.ideal ℂ (Coefficients s F.openSet)) ^ k)
        (coefficientTensorMap s L F t) = 0 := by
  letI : L.sheaf.IsQuasicoherent :=
    KunnethDegreeZero.quasicoherent_of_locallyFreeRank L.locallyFree
  let e (F : AffineLineFrame L) : LocalFrames.OverFrame L.sheaf F.openSet :=
    AffineFrameProof.frame F.openSet F.isAffine F.coefficient
  have hcover : (⨆ F : AffineLineFrame L, F.openSet) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨F, hxF⟩ := affineLineFrames_cover L x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨F, hxF⟩
  have hlinear (F : AffineLineFrame L) :
      ExternalFrameCoefficients.coefficientLinear s (e F) = coefficientLinear s L F := by
    ext a
    exact AffineFrameProof.frame_coordinates F.openSet F.isAffine F.coefficient _
  have htensor (F : AffineLineFrame L) :
      ExternalFrameCoefficients.coefficientTensorMap s (e F) (e F) =
        coefficientTensorMap s L F := by
    change TensorProduct.map (ExternalFrameCoefficients.coefficientLinear s (e F))
      (ExternalFrameCoefficients.coefficientLinear s (e F)) = _
    rw [hlinear]
    rfl
  have h := ExternalFrameCoefficients.vanishes_iff_cover_coefficients s
    (fun F : AffineLineFrame L => F.openSet) hcover (fun F => F.isAffine) e e t k
  have hglobal : globalTensorMap s L.sheaf L.sheaf =
      KunnethDegreeZero.canonicalMap s s L.sheaf L.sheaf := by rfl
  change VanishesToOrderAlongDiagonal s (externalTensor s L.sheaf L.sheaf)
    (sectionFromValue (globalTensorMap s L.sheaf L.sheaf t)) k ↔
      ∀ F : AffineLineFrame L,
        Ideal.Quotient.mk
          ((KaehlerDifferential.ideal ℂ (OpenProductCoordinates.Coefficients s F.openSet)) ^ k)
          (coefficientTensorMap s L F t) = 0
  rw [hglobal]
  refine h.trans ?_
  apply forall_congr'
  intro F
  rw [htensor]
  rfl

end LeBrunSalamon.Core.ExternalTensorCoordinates

end
