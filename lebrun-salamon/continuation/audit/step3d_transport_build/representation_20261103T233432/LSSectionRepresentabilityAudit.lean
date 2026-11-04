import LSSectionBundleAdapters
import LSSectionRepresentability
import Lean.Util.CollectAxioms

open Lean Elab Command

set_option pp.fullNames true
set_option pp.universes true
set_option maxHeartbeats 0

run_cmd do
  let env := (← getEnv).setExporting false
  let moduleFor (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => .anonymous
  let isProject (n : Name) : Bool :=
    let m := (moduleFor n).toString
    m.startsWith "Recompile" || m.startsWith "LS"
  for root in #[``LeBrunSalamon.SectionRepresentability.represented_section_data,
      ``LeBrunSalamon.SectionBundleAdapters.totalLine_exists,
      ``LeBrunSalamon.SectionBundleAdapters.totalBundle_exists] do
    let mut todo : Array Name := #[root]
    let mut cursor := 0
    let mut seen : NameSet := ({} : NameSet).insert root
    let mut directSorry : Array Name := #[]
    let mut missing : Array Name := #[]
    let mut customAxioms : Array Name := #[]
    while cursor < todo.size do
      let n := todo[cursor]!
      cursor := cursor + 1
      let some ci := env.checked.get.find? n | do
        missing := missing.push n
        logInfo m!"MISSING_CONSTANT {n}"
        continue
      let mut deps := ci.type.getUsedConstants
      if let some value := ci.value? (allowOpaque := true) then
        deps := deps ++ value.getUsedConstants
      if let .inductInfo v := ci then
        deps := deps ++ v.ctors.toArray
      if let .axiomInfo _ := ci then
        if isProject n then customAxioms := customAxioms.push n
      if deps.contains ``sorryAx then
        directSorry := directSorry.push n
        logInfo m!"DIRECT_SORRY {n}\nMODULE {moduleFor n}\nTYPE {ci.type}"
      for dep in deps do
        if !seen.contains dep then
          seen := seen.insert dep
          todo := todo.push dep
    logInfo m!"SUMMARY root={root} all_constants={seen.toArray.size} direct_sorry_count={directSorry.size} missing_count={missing.size} custom_project_axiom_count={customAxioms.size}"
    if !missing.isEmpty || !customAxioms.isEmpty then
      throwError "Missing constants or custom project axioms in exactness proof"
    let expected : Array Name := #[``LeBrunSalamon.PublishedInputs.SectionRepresentability.finiteFree]
    if directSorry.size != expected.size || !(directSorry.all expected.contains) then
      throwError m!"Unexpected admission boundary: {directSorry}"

#print axioms LeBrunSalamon.SectionRepresentability.represented_section_data
