import RecompileExtensionsPart04Geometry
import LSAffineSectionRepresentability
import Lean.Util.CollectAxioms

/-! Check the exact replacement body against the original TotalLine record.
This diagnostic theorem does not call the old projection_affine admission. -/

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix

namespace LeBrunSalamon.Construction.Descent.TotalLine

theorem projection_affine_constructed {Z : Scheme} {L : LineBundle Z}
    (T : TotalLine L) : IsAffineHom T.projection := by
  exact LeBrunSalamon.SectionRepresentability.affine_of_data L.locallyFree
    T.projection T.tautological T.universal

end LeBrunSalamon.Construction.Descent.TotalLine

#print axioms LeBrunSalamon.Construction.Descent.TotalLine.projection_affine_constructed

open Lean Elab Command
set_option maxHeartbeats 0

run_cmd do
  let env := (← getEnv).setExporting false
  let root := ``LeBrunSalamon.Construction.Descent.TotalLine.projection_affine_constructed
  let mut todo := #[root]
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut cursor := 0
  let mut leaves : Array Name := #[]
  while cursor < todo.size do
    let name := todo[cursor]!
    cursor := cursor + 1
    let some ci := env.checked.get.find? name | throwError "Missing dependency {name}"
    let mut deps := ci.type.getUsedConstants
    if let some value := ci.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if let .inductInfo value := ci then
      deps := deps ++ value.ctors.toArray
    if let .axiomInfo _ := ci then
      unless #[``propext, ``Classical.choice, ``Quot.sound, ``sorryAx].contains name do
        throwError "Unexpected custom axiom {name}"
    if deps.contains ``sorryAx then
      leaves := leaves.push name
      logInfo m!"AFFINE_DIRECT_LEAF {name}\nTYPE {ci.type}"
    for dep in deps do
      if !seen.contains dep then
        seen := seen.insert dep
        todo := todo.push dep
  unless leaves == #[``LeBrunSalamon.PublishedInputs.SectionRepresentability.finiteFree_affine] do
    throwError "Unexpected affine projection admission boundary {leaves}"
  logInfo m!"AFFINE_PROJECTION_AUDIT constants={seen.toArray.size} direct_leaves=1 missing=0 custom_axioms=0 original_projection_admission=0"

end
