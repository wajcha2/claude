import LSP1BivectorAssembly
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let target := ``LeBrunSalamon.P1BivectorAssembly.existsUnique
  let mut todo : Array Name := #[target]
  let mut cursor := 0
  let mut seen : NameSet := ({} : NameSet).insert target
  let mut directSorry : Array Name := #[]
  let mut customAxioms : Array Name := #[]
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
        customAxioms := customAxioms.push name
    if deps.contains ``sorryAx then
      directSorry := directSorry.push name
    for dep in deps do
      if !seen.contains dep then
        seen := seen.insert dep
        todo := todo.push dep
  let old : Name := `LeBrunSalamon.PublishedInputs.ProjectiveLineGeometry.normalizedSourceBivector
  if seen.contains old then
    throwError "The old normalized source-bivector admission occurs in the new proof closure."
  if !customAxioms.isEmpty then
    throwError "Unexpected custom axioms: {customAxioms}"
  logInfo m!"SOURCE_BIVECTOR_DEPENDENCIES all_constants={seen.toArray.size} old_admission_used={seen.contains old} custom_axioms={customAxioms.size}"
  logInfo m!"DIRECT_SORRY_DECLARATIONS\n{String.intercalate "\n" (directSorry.toList.map Name.toString)}"
