import LSFormalTraitModel
import Lean.Util.CollectAxioms

/-! Evidence-only exhaustive traversal of the actual original theorem
proofs. The compiler receipt determines whether this audit uses a frozen
diagnostic interface or a completely validated current dependency graph. -/

open Lean Elab Command
set_option maxHeartbeats 0

run_cmd do
  let env := (← getEnv).setExporting false
  let moduleFor (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => .anonymous
  let original := #[
    ``LeBrunSalamon.PublishedInputs.Step3f.formalTrait_twoComponent_lineNormalForm,
    ``LeBrunSalamon.PublishedInputs.Step3f.formalTrait_smooth_lineNormalForm]
  for root in original do
    let mut todo : Array (Name × List Name) := #[(root, [root])]
    let mut cursor := 0
    let mut seen : NameSet := ({} : NameSet).insert root
    let mut directSorry : Array Name := #[]
    let mut customAxioms : Array Name := #[]
    while cursor < todo.size do
      let (name, path) := todo[cursor]!
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
        logInfo m!"DIRECT_SORRY {name}\nMODULE {moduleFor name}\nSHORTEST_PATH {String.intercalate " -> " (path.reverse.map Name.toString)}\nTYPE {ci.type}"
      for dep in deps do
        if !seen.contains dep then
          seen := seen.insert dep
          todo := todo.push (dep, dep :: path)
    if original.any directSorry.contains then
      throwError "An original composite formal-trait admission remains in the proof closure."
    if !customAxioms.isEmpty then
      throwError "Unexpected custom axioms: {customAxioms}"
    logInfo m!"FORMAL_TRAIT_SUMMARY root={root} all_constants={seen.toArray.size} direct_sorry_count={directSorry.size} missing_count=0 custom_axiom_count={customAxioms.size} original_composite_admissions=0"
    logInfo m!"FORMAL_TRAIT_LEAVES root={root}\n{String.intercalate "\n" (directSorry.toList.map Name.toString)}"

#print axioms LeBrunSalamon.PublishedInputs.Step3f.formalTrait_twoComponent_lineNormalForm
#print axioms LeBrunSalamon.PublishedInputs.Step3f.formalTrait_smooth_lineNormalForm
