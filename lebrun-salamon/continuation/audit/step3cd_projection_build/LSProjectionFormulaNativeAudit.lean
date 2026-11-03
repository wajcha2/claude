import LSProjectionFormula
import LSDiagonalLocalProof
import Lean.Util.CollectAxioms

open Lean Elab Command

/- Evidence-only transitive closure audit of the new projection-formula and
   diagonal quotient/cover proofs. All dependencies, types and bodies are traversed. -/
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
  let root := ``LeBrunSalamon.ProjectionFormulaProof.sections_bijective
  let mut todo : Array (Name × List Name) := #[(root, [root])]
  let mut cursor := 0
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut projectSeen : NameSet := {}
  let mut directSorry : Array Name := #[]
  let mut missing : Array Name := #[]
  let mut customAxioms : Array Name := #[]
  while cursor < todo.size do
    let (n, path) := todo[cursor]!
    cursor := cursor + 1
    if isProject n then projectSeen := projectSeen.insert n
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
      if isProject n then
        customAxioms := customAxioms.push n
        logInfo m!"PROJECT_AXIOM {n}\nMODULE {moduleFor n}\nTYPE {ci.type}"
    if deps.contains ``sorryAx then
      directSorry := directSorry.push n
      let route := String.intercalate " -> " (path.reverse.map Name.toString)
      logInfo m!"DIRECT_SORRY {n}\nMODULE {moduleFor n}\nSHORTEST_PATH {route}\nTYPE {ci.type}"
    for dep in deps do
      if !seen.contains dep then
        seen := seen.insert dep
        todo := todo.push (dep, dep :: path)
  let names := projectSeen.toArray.qsort Name.lt
  let suspects := names.filter fun n =>
    let s := n.toString
    s.endsWith "symplecticDeterminant" || s.endsWith "alternatingDiscriminantTrivial" ||
      s.endsWith "polarizedEmbedding_firstJets" || s.endsWith "nonprimitiveBranch"
  logInfo m!"SUMMARY root={root} all_constants={seen.toArray.size} project_constants={names.size} direct_sorry_count={directSorry.size} missing_count={missing.size} custom_project_axiom_count={customAxioms.size}"
  logInfo m!"CHECKED_SPECIAL_NAMES\n{String.intercalate "\n" (suspects.toList.map Name.toString)}"
  logInfo m!"PROJECT_CLOSURE\n{String.intercalate "\n" (names.toList.map Name.toString)}"

#print axioms LeBrunSalamon.DiagonalLocalProof.kernelPower_app_eq_zero_iff
#print axioms LeBrunSalamon.DiagonalLocalProof.diagonalThickening_frameSquares_cover

