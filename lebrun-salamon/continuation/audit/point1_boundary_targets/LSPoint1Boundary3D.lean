import LSNodalFixedEnds
import RecompileExtensionsPart01
import RecompileExtensionsPart02
import RecompileExtensionsPart03
import RecompileExtensionsPart04Geometry
import Lean.Util.CollectAxioms

/-! Prepared evidence program, not yet executed.
Original Point1 coverage is the 43 Step3c–Step3g obligations.
OBL-069, when present, is a separate inherited Step3k dependency and earns no Point1 unit.
Run only with a coherent, source-ancestry-validated dependency graph.
The closure inventory and source-publication eligibility are separate acceptance gates. -/

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
  for (auditId, auditScope, root) in #[
    ("OBL-007", "point1", ``LeBrunSalamon.StandardInputs.cotangentPullback_isIso),
    ("OBL-008", "point1", ``LeBrunSalamon.Skeleton.dualBaseChange_isIso),
    ("OBL-009", "point1", ``LeBrunSalamon.Construction.fiber_dimension),
    ("OBL-010", "point1", ``LeBrunSalamon.Construction.fiber_finite),
    ("OBL-011", "point1", ``LeBrunSalamon.Construction.vectorBundle_fiber_exact),
    ("OBL-012", "point1", ``LeBrunSalamon.Construction.StandardInputs.BundleGeometry.vectorBundle_pullback_shortExact),
    ("OBL-013", "point1", ``LeBrunSalamon.Construction.StandardInputs.BundleGeometry.homFiberEvaluation_injective_of_locallyFree),
    ("OBL-014", "point1", ``LeBrunSalamon.Construction.StandardInputs.BundleGeometry.homBaseChange_isIso),
    ("OBL-015", "point1", ``LeBrunSalamon.Construction.Smoothing.CoordinateCharts.StandardInputs.spec_pullback_isPushout),
    ("OBL-016", "point1", ``LeBrunSalamon.Construction.Smoothing.CoordinateCharts.StandardInputs.generating_sections_unitOpen),
    ("OBL-017", "point1", ``LeBrunSalamon.Construction.Normalization.totalBundle_exists)
  ] do
    logInfo m!"AUDIT_SCOPE id={auditId} scope={auditScope}"
    logInfo m!"ROOT {root}"
    if let some rootInfo := env.checked.get.find? root then
      logInfo m!"ROOT_SIGNATURE {root}\nLEVEL_PARAMS {String.intercalate "," (rootInfo.levelParams.map Name.toString)}\nTYPE {rootInfo.type}"
    let mut todo : Array (Name × List Name) := #[(root, [root])]
    let mut cursor := 0
    let mut seen : NameSet := ({} : NameSet).insert root
    let mut projectSeen : NameSet := {}
    let mut directSorry : Array Name := #[]
    let mut missing : Array Name := #[]
    let mut customAxioms : Array Name := #[]
    let mut nonstandardAxioms : Array Name := #[]
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
        if !(#[``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]).contains n then
          nonstandardAxioms := nonstandardAxioms.push n
          logInfo m!"NONSTANDARD_AXIOM {n}\nMODULE {moduleFor n}\nTYPE {ci.type}"
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
    logInfo m!"SUMMARY root={root} all_constants={seen.toArray.size} project_constants={names.size} direct_sorry_count={directSorry.size} missing_count={missing.size} custom_project_axiom_count={customAxioms.size} nonstandard_axiom_count={nonstandardAxioms.size}"
    logInfo m!"PROJECT_CLOSURE\n{String.intercalate "\n" (names.toList.map Name.toString)}"

#print axioms LeBrunSalamon.StandardInputs.cotangentPullback_isIso
#print axioms LeBrunSalamon.Skeleton.dualBaseChange_isIso
#print axioms LeBrunSalamon.Construction.fiber_dimension
#print axioms LeBrunSalamon.Construction.fiber_finite
#print axioms LeBrunSalamon.Construction.vectorBundle_fiber_exact
#print axioms LeBrunSalamon.Construction.StandardInputs.BundleGeometry.vectorBundle_pullback_shortExact
#print axioms LeBrunSalamon.Construction.StandardInputs.BundleGeometry.homFiberEvaluation_injective_of_locallyFree
#print axioms LeBrunSalamon.Construction.StandardInputs.BundleGeometry.homBaseChange_isIso
#print axioms LeBrunSalamon.Construction.Smoothing.CoordinateCharts.StandardInputs.spec_pullback_isPushout
#print axioms LeBrunSalamon.Construction.Smoothing.CoordinateCharts.StandardInputs.generating_sections_unitOpen
#print axioms LeBrunSalamon.Construction.Normalization.totalBundle_exists
