import LSAffineDerivations
import LSClassicalReduction
import LSContactLineTests
import LSCurveLaurentStandardInputs
import LSFormalTraitModel
import LSHomVelocity
import LSNodalFixedEnds
import LSNodalTangent
import LSStandardConicDifferential
import RecompileBasePart04
import RecompileBasePart05A
import RecompileBasePart05C
import RecompileBasePart06
import RecompileBasePart07
import RecompileExtensionCore
import RecompileExtensionsPart01
import RecompileExtensionsPart02
import RecompileExtensionsPart03
import RecompileExtensionsPart04Geometry
import RecompileSections
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
    ("OBL-001", "point1", ``LeBrunSalamon.PhaseTwentyEight.externalSection_finiteSum),
    ("OBL-002", "point1", ``LeBrunSalamon.PhaseTwentyEight.locallyFree_sections_descend),
    ("OBL-003", "point1", ``LeBrunSalamon.PhaseTwentyEight.nonvanishingOpen_pullback),
    ("OBL-004", "point1", ``LeBrunSalamon.Core.ExternalTensorCoordinates.globalTensorMap_injective),
    ("OBL-005", "point1", ``LeBrunSalamon.Core.ExternalTensorCoordinates.diagonalRestriction_iff_quotientCoefficients),
    ("OBL-006", "point1", ``LeBrunSalamon.Core.ExternalTensorCoordinates.smooth_diagonal_square_detected),
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
    ("OBL-017", "point1", ``LeBrunSalamon.Construction.Normalization.totalBundle_exists),
    ("OBL-018", "point1", ``LeBrunSalamon.ClassicalReduction.StandardInputs.polarizedEmbedding_firstJets),
    ("OBL-019", "point1", ``LeBrunSalamon.PhaseTwentyFive.smooth_cotangent_rank),
    ("OBL-020", "point1", ``LeBrunSalamon.PhaseTwentySix.tangentDeterminant_anticanonical),
    ("OBL-021", "point1", ``LeBrunSalamon.PhaseTwentySix.ample_positivePower_iff),
    ("OBL-022", "point1", ``LeBrunSalamon.PhaseTwentySix.determinant_shortExact),
    ("OBL-023", "point1", ``LeBrunSalamon.PhaseTwentySeven.contact_distribution_determinant),
    ("OBL-024", "point1", ``LeBrunSalamon.PhaseThirtyFive.contactFano_hasProjectiveEmbedding),
    ("OBL-025", "point1", ``LeBrunSalamon.StandardInputs.formalTrait_twoComponent_lineNormalForm),
    ("OBL-026", "point1", ``LeBrunSalamon.StandardInputs.formalTrait_smooth_lineNormalForm),
    ("OBL-027", "point1", ``LeBrunSalamon.Construction.StandardInputs.InfinitesimalGeometry.dualThickening_zeroSection_surjective),
    ("OBL-028", "point1", ``LeBrunSalamon.Construction.StandardInputs.InfinitesimalGeometry.dualThickening_normalForm_unique),
    ("OBL-029", "point1", ``LeBrunSalamon.StandardInputs.affineLine_section_divisible),
    ("OBL-030", "point1", ``LeBrunSalamon.StandardInputs.dualThickening_hom_vanishing),
    ("OBL-031", "point1", ``LeBrunSalamon.Construction.StandardInputs.InfinitesimalGeometry.firstOrder_cotangentHom_bijective),
    ("OBL-032", "point1", ``LeBrunSalamon.StandardInputs.standardConic_fundamentalClass_exists),
    ("OBL-033", "point1", ``LeBrunSalamon.StandardInputs.affine_localDerivation_exists),
    ("OBL-034", "point1", ``LeBrunSalamon.StandardInputs.affine_localDerivation_ext),
    ("OBL-035", "point1", ``LeBrunSalamon.Refinement.Boundary.regular_of_heightOne),
    ("OBL-036", "point1", ``LeBrunSalamon.StandardInputs.projectiveLineFamily_degree_constant),
    ("OBL-037", "point1", ``LeBrunSalamon.CurveStandardInputs.exists_laurent_expansion_with_pole),
    ("OBL-038", "point1", ``LeBrunSalamon.PhaseThirty.nonconstant_complexCurve_differential_ne_zero),
    ("OBL-039", "point1", ``LeBrunSalamon.PhaseThirtyTwo.birkhoffGrothendieck),
    ("OBL-040", "point1", ``LeBrunSalamon.Skeleton.sourceBivector_existsUnique),
    ("OBL-041", "point1", ``LeBrunSalamon.Skeleton.projectiveCoordinates_exists),
    ("OBL-042", "point1", ``LeBrunSalamon.PhaseThirtyTwo.projectiveLineBundle_classification),
    ("OBL-043", "point1", ``LeBrunSalamon.PhaseThirtyTwo.projectiveLine_tangent_twist),
    ("OBL-069", "additional_inherited_step3k", ``LeBrunSalamon.Construction.Descent.TotalLine.projection_affine)
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

#print axioms LeBrunSalamon.PhaseTwentyEight.externalSection_finiteSum
#print axioms LeBrunSalamon.PhaseTwentyEight.locallyFree_sections_descend
#print axioms LeBrunSalamon.PhaseTwentyEight.nonvanishingOpen_pullback
#print axioms LeBrunSalamon.Core.ExternalTensorCoordinates.globalTensorMap_injective
#print axioms LeBrunSalamon.Core.ExternalTensorCoordinates.diagonalRestriction_iff_quotientCoefficients
#print axioms LeBrunSalamon.Core.ExternalTensorCoordinates.smooth_diagonal_square_detected
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
#print axioms LeBrunSalamon.ClassicalReduction.StandardInputs.polarizedEmbedding_firstJets
#print axioms LeBrunSalamon.PhaseTwentyFive.smooth_cotangent_rank
#print axioms LeBrunSalamon.PhaseTwentySix.tangentDeterminant_anticanonical
#print axioms LeBrunSalamon.PhaseTwentySix.ample_positivePower_iff
#print axioms LeBrunSalamon.PhaseTwentySix.determinant_shortExact
#print axioms LeBrunSalamon.PhaseTwentySeven.contact_distribution_determinant
#print axioms LeBrunSalamon.PhaseThirtyFive.contactFano_hasProjectiveEmbedding
#print axioms LeBrunSalamon.StandardInputs.formalTrait_twoComponent_lineNormalForm
#print axioms LeBrunSalamon.StandardInputs.formalTrait_smooth_lineNormalForm
#print axioms LeBrunSalamon.Construction.StandardInputs.InfinitesimalGeometry.dualThickening_zeroSection_surjective
#print axioms LeBrunSalamon.Construction.StandardInputs.InfinitesimalGeometry.dualThickening_normalForm_unique
#print axioms LeBrunSalamon.StandardInputs.affineLine_section_divisible
#print axioms LeBrunSalamon.StandardInputs.dualThickening_hom_vanishing
#print axioms LeBrunSalamon.Construction.StandardInputs.InfinitesimalGeometry.firstOrder_cotangentHom_bijective
#print axioms LeBrunSalamon.StandardInputs.standardConic_fundamentalClass_exists
#print axioms LeBrunSalamon.StandardInputs.affine_localDerivation_exists
#print axioms LeBrunSalamon.StandardInputs.affine_localDerivation_ext
#print axioms LeBrunSalamon.Refinement.Boundary.regular_of_heightOne
#print axioms LeBrunSalamon.StandardInputs.projectiveLineFamily_degree_constant
#print axioms LeBrunSalamon.CurveStandardInputs.exists_laurent_expansion_with_pole
#print axioms LeBrunSalamon.PhaseThirty.nonconstant_complexCurve_differential_ne_zero
#print axioms LeBrunSalamon.PhaseThirtyTwo.birkhoffGrothendieck
#print axioms LeBrunSalamon.Skeleton.sourceBivector_existsUnique
#print axioms LeBrunSalamon.Skeleton.projectiveCoordinates_exists
#print axioms LeBrunSalamon.PhaseThirtyTwo.projectiveLineBundle_classification
#print axioms LeBrunSalamon.PhaseThirtyTwo.projectiveLine_tangent_twist
#print axioms LeBrunSalamon.Construction.Descent.TotalLine.projection_affine
