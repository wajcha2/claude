import LSLineCohomologyBaseChange
import Lean.Util.CollectAxioms

open Lean Elab Command

/- Evidence-only audit of the actual H0 map, hypothesis transports, and
   original finite section-tuple lift. It traverses all constant types and values,
   including nonproject dependencies and inductive constructors. Diagnostic
   ancestors are frozen cdf4d8a5/CI41732181431, not live-source acceptance. -/
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
  for root in #[``LeBrunSalamon.CanonicalSectionBaseChange.lift_finite_tuple,
      ``LeBrunSalamon.CohomologyHypotheses.finitePresentation_of_locallyFreeRank,
      ``LeBrunSalamon.YonedaExtensionSplitting.classesRepresented,
      ``LeBrunSalamon.LineStalkFlat.relativelyFlat,
      ``LeBrunSalamon.CohomologyBaseChange.lift_line_tuple,
      ``LeBrunSalamon.CohomologyBaseChange.fibre_restriction_surjective_of_h1,
      ``LeBrunSalamon.CohomologyBaseChange.powerSeries_fibre_restriction_surjective] do
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
      s.endsWith "h0_residue_baseChange_bijective" ||
        s.endsWith "coherent_iff_finitePresentation" || s.endsWith "ext1_unit_h1" ||
        s.endsWith "lift_line_tuple" || s.endsWith "polarizedEmbedding_firstJets" ||
        s.endsWith "symplecticDeterminant"
    logInfo m!"SUMMARY root={root} all_constants={seen.toArray.size} project_constants={names.size} direct_sorry_count={directSorry.size} missing_count={missing.size} custom_project_axiom_count={customAxioms.size}"
    logInfo m!"CHECKED_SPECIAL_NAMES\n{String.intercalate "\n" (suspects.toList.map Name.toString)}"
    logInfo m!"PROJECT_CLOSURE\n{String.intercalate "\n" (names.toList.map Name.toString)}"

#print axioms LeBrunSalamon.CanonicalSectionBaseChange.lift_finite_tuple
#print axioms LeBrunSalamon.YonedaExtensionSplitting.classesRepresented
#print axioms LeBrunSalamon.LineStalkFlat.relativelyFlat
#print axioms LeBrunSalamon.CohomologyBaseChange.lift_line_tuple
