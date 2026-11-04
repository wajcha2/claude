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
  err.putStrLn "LEFT_WRAPPER_ENTER_raw_expansion"
  err.flush

namespace ExpansionProof

theorem left_raw_expansion
    (E : ExternalExpansion (projectiveLineVariety P)
      (identityCurveContact P).sequence.line (sourceBivector P)) :
    Curve.leftRaw P X f = ∑ i,
      externalProductSection P.structureMap
        (E.left i ≫ Curve.differential P X f)
        (E.right i ≫ curveContactVelocity P X.contact f) := by
  run_tac
    let err ← IO.getStderr
    err.putStrLn "LEFT_WRAPPER_STEP_RAW_ENTER"
    err.flush
  letI := curveExternalComparison_isIso P f
    (tangentSheaf X.variety.structureMap) X.contact.sequence.line.sheaf
  run_tac
    let err ← IO.getStderr
    err.putStrLn "LEFT_WRAPPER_STEP_RAW_AFTER_INSTANCE"
    err.flush
  apply (cancel_mono (curveExternalComparison P f
    (tangentSheaf X.variety.structureMap) X.contact.sequence.line.sheaf)).mp
  run_tac
    let err ← IO.getStderr
    err.putStrLn "LEFT_WRAPPER_STEP_RAW_AFTER_CANCEL"
    err.flush
  simpa only [Curve.leftSection, Preadditive.sum_comp] using
    Curve.leftSection_expansion P X f E

end ExpansionProof
#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "LEFT_WRAPPER_EXIT_raw_expansion"
  err.flush


end Reparametrization

end LeBrunSalamon.Construction.FamilyBivectors

end
