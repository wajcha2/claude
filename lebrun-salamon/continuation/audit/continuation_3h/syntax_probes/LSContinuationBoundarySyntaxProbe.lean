import RecompileBasePart06
import Lean.Util.CollectAxioms

/-! Generated audit only. Not a production module or an additional obligation.
Native output is authoritative only with its exact receipt and parent contexts. -/
open Lean Elab Command
set_option pp.all true
set_option pp.maxSteps 10000000

run_cmd do
  let env := (← getEnv).setExporting false
  let moduleFor (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => .anonymous
  for root in #[
    ``LeBrunSalamon.PhaseThirty.openImmersion_cotangentMap_isIso
  ] do
    let some ci := env.checked.get.find? root | throwError m!"Missing audit constant {root}"
    logInfo m!"CI_SIGNATURE {root}
LEVEL_PARAMS {String.intercalate "," (ci.levelParams.map Name.toString)}
MODULE {moduleFor root}
TYPE {ci.type}"
  logInfo "CI_SIGNATURES_COMPLETE"

run_cmd do
  let env := (← getEnv).setExporting false
  let moduleFor (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => .anonymous
  let projectModules : Array String := #["FieldDifferentials", "LSAdditionFiberPresentation", "LSAffineCotangentHom", "LSAffineCurveSelection", "LSAffineDerivations", "LSAffineFiberDivisibility", "LSAffineFrame", "LSAffineProductRing", "LSAffineSectionRepresentability", "LSArcParametrization", "LSBoundedLines", "LSBranchAlgebra", "LSBranchRamification", "LSCanonicalSectionBaseChange", "LSCartesianSourceDifferential", "LSCartierQuadraticExtraction", "LSCharacteristicZeroSeparability", "LSClassicalActions", "LSClassicalReduction", "LSClosedIdealCoefficients", "LSClosedImmersionLocus", "LSCohomologyHypotheses", "LSCompletedTargets", "LSComplexQuadraticCoordinates", "LSComplexQuadraticMatrix", "LSConeAdditionAlgebra", "LSConeArcs", "LSConeDiagonal", "LSConeDominance", "LSConeFiberRigidity", "LSConeIsotropy", "LSConeLocalization", "LSConeOpen", "LSConePole", "LSConeRadial", "LSConeRescaledArcs", "LSConeTangents", "LSConicChartDerivations", "LSConicCotangentExt", "LSConicCotangentTools", "LSConicFundamentalClassConstruction", "LSConicGeneratingTuples", "LSConicJets", "LSConicLogAlgebra", "LSConicModelSections", "LSConicOverlapAlgebra", "LSConicOverlapCoordinates", "LSConicScalarCompatibility", "LSConicScalarTransport", "LSConicSplitting", "LSConicTupleChange", "LSContactCompletion", "LSContactDirections", "LSContactGeneration", "LSContactHomBaseChange", "LSContactHorizontal", "LSContactLineTests", "LSContactStandardInputs", "LSContactVelocityTarget", "LSCotangentDeformations", "LSCotangentScalarAlgebra", "LSCurveFunctionField", "LSCurveLaurentGeometry", "LSCurveLaurentStandardInputs", "LSCurvePairing", "LSDescentAssembly", "LSDualBaseChangeAlgebra", "LSDualHomVanishing", "LSDualStructureExact", "LSDualThickeningNormalForm", "LSEffectiveCartierInputs", "LSEffectiveCartierIso", "LSEpsilonStructureSequence", "LSExternalFrameCoefficients", "LSFamilyAdditiveExpansion", "LSFamilyBaseChange", "LSFamilyBivectorDescent", "LSFamilyBivectors", "LSFamilyCurveProductDirect", "LSFamilyDerivativeRestriction", "LSFamilyDescentFibres", "LSFamilyDescentReparametrization", "LSFamilyDescentTransport", "LSFamilyExternalProductMap", "LSFamilyReparamExpansionStages", "LSFamilyReparamProductTransport", "LSFamilyReparametrization", "LSFamilyReparametrizationFibres", "LSFamilyReparametrizationFieldBaseChange", "LSFamilyReparametrizationLeftFiniteType", "LSFamilyReparametrizationRightFiniteType", "LSFamilySchemeTransport", "LSFamilySectionSums", "LSFamilySmoothCoordinates", "LSFamilySmoothDescent", "LSFamilySmoothNormalization", "LSFamilySmoothPointValues", "LSFibreIsomorphism", "LSFieldParametrization", "LSFiniteFreeBaseChange", "LSFiniteFreeHomBaseChange", "LSFiniteTypeDominance", "LSFiniteTypeSpreading", "LSFirstCohomologyIso", "LSFirstJetEmbedding", "LSFirstJetEmbeddingGeometry", "LSFlatSectionDescent", "LSFormalArcComparison", "LSFormalArcFamilyComparison", "LSFormalArcModelNormalization", "LSFormalArcModelTransport", "LSFormalArcRegularity", "LSFormalArcSections", "LSFormalQuadraticConditions", "LSFormalTraitModel", "LSFormalTraitParameters", "LSFormalTraitProjectivity", "LSFormalTraitRing", "LSFormalTraitSourceComparison", "LSFrameTransport", "LSFunctionFieldPlaces", "LSGeneratingUnitOpens", "LSGenericFamilyCartesianComparison", "LSGenericFamilyCartesianFieldComparison", "LSGenericFamilyComparison", "LSGenericFamilyFieldTransport", "LSGenericFamilyPointComparison", "LSGenericGlobalFunctions", "LSGenericSheets", "LSGlobalVelocity", "LSHamiltonianJets", "LSHomDegree", "LSHomFiberInjectivity", "LSHomVelocity", "LSIntrinsicVelocity", "LSKunnethDegreeZero", "LSLaurentRescaling", "LSLeviFiber", "LSLeviOpen", "LSLiftedProjectiveTuple", "LSLineCohomologyBaseChange", "LSLineEvaluation", "LSLineStalkFlat", "LSLineValueDescent", "LSMilestoneStatement", "LSMilestoneTarget", "LSMilestoneTopology", "LSModelBivector", "LSModelContactFactor", "LSModelDifferential", "LSModelGenericComparison", "LSModelGenericNormalization", "LSModelGenericParametrization", "LSModelGeometry", "LSModelNumeratorTransport", "LSModelSourceNumerator", "LSModelSourceProductTransport", "LSModelTensorScalar", "LSModuleHomGluing", "LSMovingPairAssembly", "LSMovingPairConstruction", "LSNilpotentTopology", "LSNodalConic", "LSNodalFibreComparison", "LSNodalFixedEnds", "LSNodalLineCohomology", "LSNodalLineTriviality", "LSNodalTangent", "LSNodalTraitNormalForm", "LSNodalTraitQuadraticPresentation", "LSNonvanishingPullback", "LSNormalizedSegre", "LSNormalizedSegrePairs", "LSNormalizedSegreQuotients", "LSOpenCotangentScalar", "LSOpenModuleCoherence", "LSOpenProductCoordinates", "LSOpenSectionTransport", "LSP1BivectorCoordinates", "LSP1CoordinateGauge", "LSP1FamilyDegree", "LSP1PointTransport", "LSP1SourceAlgebra", "LSP1TangentSections", "LSP1TensorSquare", "LSP1TensorTaylor", "LSParametrizedBaseChange", "LSPlaneConicPresentation", "LSPlaneConicZeroPresentation", "LSPlaneEmbeddingCartier", "LSPlaneFamilyQuadratic", "LSPlaneQuadratic", "LSPlaneQuadraticBaseChange", "LSPlaneQuadraticEquation", "LSPlaneQuadraticPublished", "LSPolarizedEmbeddingLift", "LSPolarizedOverIso", "LSPolarizedProjectiveEmbedding", "LSPositiveHom", "LSPositiveIndependence", "LSPositiveNodeImage", "LSPositiveQuotient", "LSPositiveSplit", "LSPositiveVariation", "LSProductGeometry", "LSProjectAssembly", "LSProjectionFormula", "LSProjectiveFibreLineRigidity", "LSProjectiveLineReparametrization", "LSProjectiveLinearAction", "LSProjectiveTransport", "LSProjectivityDefinitions", "LSProperLocalTopology", "LSProperSections", "LSPublishedCohomologyBaseChange", "LSPublishedDirections", "LSPublishedPicard", "LSPublishedProjectiveSpace", "LSQuadraticFibreCartier", "LSQuadraticFibreCriteria", "LSQuadraticLinearTransport", "LSQuadraticPolarizedModels", "LSQuadraticPolynomial", "LSQuadraticPrimitive", "LSQuadraticSchemeBaseChange", "LSQuadraticSectionEvaluation", "LSQuadraticVeronese", "LSRadialDetection", "LSRationalOpenTransport", "LSReducedCover", "LSReducedPushout", "LSRegularModelPair", "LSRelativeCartier", "LSRelativeDifferential", "LSRelativeGeneration", "LSRelativeGenericSmoothness", "LSRelativeVeroneseModel", "LSResidueFibreGeometry", "LSResidueFieldPresentation", "LSResidueTensorLift", "LSScaledVelocities", "LSScaledVelocityDifferential", "LSSecondDiagonalAlgebra", "LSSectionCover", "LSSectionRepresentability", "LSSelectedPair", "LSSheafSectionExact", "LSSmoothFibreCartier", "LSSmoothFibreComparison", "LSSmoothTraitNormalForm", "LSSmoothingAssembly", "LSStableFamilyTraits", "LSStableMapFamily", "LSStandardCentralPlane", "LSStandardConicDifferential", "LSStandardConicFrames", "LSStandardConicTriple", "LSStandardConicZeroComparison", "LSStandardProjectiveBaseChange", "LSStandardProjectiveComposition", "LSStandardProjectiveNonempty", "LSStandardProjectivePicard", "LSStandardProjectiveProper", "LSStandardProjectiveReduced", "LSStandardProjectiveSmooth", "LSStandardSourceBaseChange", "LSStandardTautological", "LSStandardTautologicalP1", "LSSuitableDirections", "LSSuitableLinear", "LSSuitablePair", "LSTangentComparison", "LSTangentFrameCoordinates", "LSTensorLineTransport", "LSTensorLocallyFreeExact", "LSTraitContact", "LSTraitFibreCohomology", "LSTraitQuadraticPresentation", "LSVectorBundlePullback", "LSVelocityAdditionFamily", "LSVeroneseZeroModel", "LSYonedaClassesRepresented", "LSYonedaExtensionSplitting", "RecompileBase", "RecompileBasePart01", "RecompileBasePart02", "RecompileBasePart03", "RecompileBasePart04", "RecompileBasePart05", "RecompileBasePart05A", "RecompileBasePart05B", "RecompileBasePart05C", "RecompileBasePart06", "RecompileBasePart07", "RecompileExtensionCore", "RecompileExtensions", "RecompileExtensionsPart01", "RecompileExtensionsPart02", "RecompileExtensionsPart03", "RecompileExtensionsPart04", "RecompileExtensionsPart04Geometry", "RecompileExtensionsPart04Gluing", "RecompileExtensionsPart04GluingPrefix", "RecompileExtensionsPart04GluingSections", "RecompileExtensionsPart04Nodes", "RecompileSections", "RecompileTail"]
  let isProject (n : Name) : Bool := projectModules.contains (moduleFor n).toString
  for (auditId, root) in #[
    ("OBL-044", ``LeBrunSalamon.PhaseThirty.openImmersion_cotangentMap_isIso)
  ] do
    logInfo m!"CI_ROOT {auditId} {root}"
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
        logInfo m!"CI_MISSING {root} {n}"
        continue
      let mut deps := ci.type.getUsedConstants
      if let some value := ci.value? (allowOpaque := true) then
        deps := deps ++ value.getUsedConstants
      if let .inductInfo v := ci then
        deps := deps ++ v.ctors.toArray
      if let .axiomInfo _ := ci then
        if !(#[``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]).contains n then
          nonstandardAxioms := nonstandardAxioms.push n
          logInfo m!"CI_NONSTANDARD_AXIOM {root} {n}"
        if isProject n then
          customAxioms := customAxioms.push n
          logInfo m!"CI_PROJECT_AXIOM {root} {n}"
      if deps.contains ``sorryAx then
        directSorry := directSorry.push n
        let route := String.intercalate " -> " (path.reverse.map Name.toString)
        logInfo m!"CI_DIRECT_SORRY {root}
NAME {n}
MODULE {moduleFor n}
SHORTEST_PATH {route}
TYPE {ci.type}"
      for dep in deps do
        if !seen.contains dep then
          seen := seen.insert dep
          todo := todo.push (dep, dep :: path)
    logInfo m!"CI_SUMMARY root={root} all_constants={seen.toArray.size} project_constants={projectSeen.toArray.size} direct_sorry_count={directSorry.size} missing_count={missing.size} custom_project_axiom_count={customAxioms.size} nonstandard_axiom_count={nonstandardAxioms.size}"
  logInfo "CI_BOUNDARIES_COMPLETE"

#print axioms LeBrunSalamon.PhaseThirty.openImmersion_cotangentMap_isIso
