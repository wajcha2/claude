import LSFamilyReparamExpansionStages

noncomputable section
set_option autoImplicit false
set_option profiler true
set_option stderrAsMessages false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.PhaseTwentyEight.ExternalExchangeCoherenceProof

namespace LeBrunSalamon.Construction.FamilyBivectors


-- Normalize the existing P1/contact carrier aliases for the same actual maps.
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety identityCurveContact intrinsicTangentBundle

namespace Reparametrization

variable (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
variable (he : e.hom ≫ P.structureMap = P.structureMap)

variable {n : ℕ} (X : ContactFanoManifold n) (f g : RationalCurve P X.variety)
variable (hg : g.map = e.hom ≫ f.map)

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "LEFT_WRAPPER_ENTER_original_left"
  err.flush

/-- Reparametrization invariance in the actual target bundle, including
all the canonical composition and external-product comparisons. -/
theorem leftSection :
    pullSection (curveSquareMap P (curve P e he)) (Curve.leftSection P X f) ≫
      (compositionPullback (curveSquareMap P (curve P e he)) (curveSquareMap P f)
        (curveSquareMap P g) (square_comp P e he X f g hg)
        (movingPairBundleLeft X.variety X.contact)).hom = Curve.leftSection P X g := by
  run_tac
    let err ← IO.getStderr
    err.putStrLn "LEFT_WRAPPER_STEP_ENTER"
    err.flush
  obtain ⟨E⟩ := externalExpansion_exists (projectiveLineVariety P)
    (identityCurveContact P).sequence.line (sourceBivector P)
  run_tac
    let err ← IO.getStderr
    err.putStrLn "LEFT_WRAPPER_STEP_AFTER_OBTAIN"
    err.flush
  have hB : Curve.leftRaw P X f = ∑ i,
      externalProductSection P.structureMap
        (E.left i ≫ Curve.differential P X f)
        (E.right i ≫ curveContactVelocity P X.contact f) := by
    letI := curveExternalComparison_isIso P f
      (tangentSheaf X.variety.structureMap) X.contact.sequence.line.sheaf
    run_tac
      let err ← IO.getStderr
      err.putStrLn "LEFT_WRAPPER_STEP_HB_AFTER_INSTANCE"
      err.flush
    apply (cancel_mono (curveExternalComparison P f
      (tangentSheaf X.variety.structureMap) X.contact.sequence.line.sheaf)).mp
    run_tac
      let err ← IO.getStderr
      err.putStrLn "LEFT_WRAPPER_STEP_HB_AFTER_CANCEL"
      err.flush
    simpa only [Curve.leftSection, Preadditive.sum_comp] using
      Curve.leftSection_expansion P X f E
  run_tac
    let err ← IO.getStderr
    err.putStrLn "LEFT_WRAPPER_STEP_AFTER_HB"
    err.flush
  rw [Curve.leftSection, compared_of_expansion P e he X f g hg
    (Curve.leftRaw P X f) _ _ hB, leftRaw P e he X f g hg]
  run_tac
    let err ← IO.getStderr
    err.putStrLn "LEFT_WRAPPER_STEP_AFTER_RW"
    err.flush
  rfl
#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "LEFT_WRAPPER_EXIT_original_left"
  err.flush


end Reparametrization

end LeBrunSalamon.Construction.FamilyBivectors

end
