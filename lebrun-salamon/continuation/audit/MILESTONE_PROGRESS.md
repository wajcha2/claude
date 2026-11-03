# Milestone progress ledger

**Conservative evidence-backed checklist completion: 30 of 133 units = 22.56%, rounded to 23%.** The first milestone remains open.

This is a count of closed acceptance items. It is not an estimate of mathematical effort completed, hours remaining, proof length, or source lines. Large mathematical obligations and small retirement items each have one fixed unit; the percentage cannot measure their relative difficulty.

The 30 credited units are 22 admissions retired in Step 3a and 8 wrappers accepted in the historical Step 3b checkpoint. Their source treatment remains preserved. New proof modules and diagnostic checks provide substantive partial progress, described below, but do not yet close another whole acceptance item.

## Fixed denominator

| Category | Units | Accepted | Pending |
| --- | ---: | ---: | ---: |
| Step 3a unused-admission retirements | 22 | 22 | 0 |
| Step 3b sheaf wrappers | 8 | 8 | 0 |
| Original obligations in Steps 3c–3n | 91 | 0 | 91 |
| Step 2 definition validations | 8 | 0 | 8 |
| Final gates | 4 | 0 | 4 |
| **Total** | **133** | **30** | **103** |

The original plan contained 122 inventory entries. `LeBrunSalamon.Project.stageDescription` was a false positive caused by descriptive text, so the actual original obligation count is 121. It partitions as 22 retired + 8 accepted + 91 pending. The two-point evaluation declaration was retained after liveness checking and remains in the 91; Step 3i therefore has 8 survivors.

**Publication audits are included in the obligations they support.** The 50 published-namespace candidates observed at takeover are not 50 additional units. Each original obligation requires approval of its admitted dependencies and proof of every nondefinitional project translation. Shared leaf reviews may support several obligations. Merely relocating or splitting an admission earns no credit. This 133-unit ledger supersedes the earlier provisional 153-unit suggestion in the target-integration report.

An obligation closes only with the required implementation or justified retirement, exact publication/hypothesis review where needed, and matching build evidence. Newly discovered subtasks attach to their governing obligation or gate; the denominator changes only through an explicit scope revision.

## What the 30 accepted units mean

Step 3a records 22 deletions, zero native references to the deleted constants, and passing compile groups. Three groups reused results after exact source-hash comparison; one group was rerun. Step 3b records successful compilation of the two changed modules and a compatibility import of 73 prior artifacts, together with its published-input boundary check. These are historical incremental acceptance records, not a clean build of the entire current source.

The current lexical comparison confirms that all 22 retired declarations remain absent. Each of the 8 Step 3b wrapper declaration spans remains free of direct admission and identical to its accepted version after comments and whitespace are removed. That preservation check is static; it does not certify new dependencies introduced elsewhere.

### Step 3a: 22 retained retirements

| ID | Original declaration | Original source |
| --- | --- | --- |
| RET-01 | `LeBrunSalamon.StandardInputs.proper_flat_connectedReduced_globalFunctions` | `LSFormalTraitModel.lean` |
| RET-02 | `LeBrunSalamon.PhaseTwentyFive.cotangent_openRestriction` | `RecompileBasePart04.lean` |
| RET-03 | `LeBrunSalamon.PhaseTwentySix.symmetricSheaf_locallyFree` | `RecompileBasePart04.lean` |
| RET-04 | `LeBrunSalamon.PhaseTwentySix.symmetricSheaf_pullback` | `RecompileBasePart04.lean` |
| RET-05 | `LeBrunSalamon.PhaseTwentySix.ample_tensor` | `RecompileBasePart04.lean` |
| RET-06 | `LeBrunSalamon.PhaseTwentySix.ample_closedPullback` | `RecompileBasePart04.lean` |
| RET-07 | `LeBrunSalamon.PhaseTwentySix.ample_affineBasis` | `RecompileBasePart04.lean` |
| RET-08 | `LeBrunSalamon.PhaseTwentySix.ample_eventualGlobalGeneration` | `RecompileBasePart04.lean` |
| RET-09 | `LeBrunSalamon.PhaseTwentyEight.firstPrincipalParts_exact` | `RecompileBasePart05C.lean` |
| RET-10 | `LeBrunSalamon.PhaseTwentyEight.principalParts_locallyFree` | `RecompileBasePart05C.lean` |
| RET-11 | `LeBrunSalamon.PhaseTwentyEight.principalParts_higher_exact` | `RecompileBasePart05C.lean` |
| RET-12 | `LeBrunSalamon.PhaseTwentyNine.nodeAlgebra_integrallyClosed` | `RecompileBasePart06.lean` |
| RET-13 | `LeBrunSalamon.PhaseThirty.smooth_cotangent_transitivity_shortExact` | `RecompileBasePart06.lean` |
| RET-14 | `LeBrunSalamon.PhaseThirty.etale_cotangentMap_isIso` | `RecompileBasePart06.lean` |
| RET-15 | `LeBrunSalamon.PhaseThirty.closedImmersion_cotangentMap_epi` | `RecompileBasePart06.lean` |
| RET-16 | `LeBrunSalamon.PhaseThirtyTwo.splitting_unique_upToPermutation` | `RecompileExtensionCore.lean` |
| RET-17 | `LeBrunSalamon.PhaseThirtyTwo.ample_positiveDegreeOnCurve` | `RecompileExtensionsPart01.lean` |
| RET-18 | `LeBrunSalamon.Skeleton.minimalNilpotent_exists` | `RecompileExtensionsPart01.lean` |
| RET-19 | `LeBrunSalamon.Construction.Descent.genericDegree_existsUnique` | `RecompileExtensionsPart04Geometry.lean` |
| RET-20 | `LeBrunSalamon.Construction.Descent.genericDegree_positive` | `RecompileExtensionsPart04Geometry.lean` |
| RET-21 | `LeBrunSalamon.Construction.Descent.ramificationIndex_existsUnique` | `RecompileExtensionsPart04Geometry.lean` |
| RET-22 | `LeBrunSalamon.PhaseThirtyTwo.projectiveTwist_ample_iff` | `RecompileSections.lean` |

These units record removal of unused admitted declarations. They do not claim a proof of each deleted theorem.

### Step 3b: 8 accepted wrapper boundaries

| ID | Wrapper | Accepted published leaf |
| --- | --- | --- |
| SHF-01 | `LeBrunSalamon.PhaseTwentyFive.cotangentPresentation_exists` | `LeBrunSalamon.PublishedInputs.SheafFunctoriality.cotangentPresentation` |
| SHF-02 | `LeBrunSalamon.PhaseTwentyFive.dualSheaf_pullback` | `LeBrunSalamon.PublishedInputs.SheafFunctoriality.pullback_dual` |
| SHF-03 | `LeBrunSalamon.PhaseTwentyFive.tensorSheaf_pullback` | `LeBrunSalamon.PublishedInputs.SheafFunctoriality.pullback_tensorProduct` |
| SHF-04 | `LeBrunSalamon.PhaseTwentySix.exteriorPresentation_exists` | `LeBrunSalamon.PublishedInputs.SheafFunctoriality.exteriorPresentation` |
| SHF-05 | `LeBrunSalamon.PhaseTwentySix.exteriorSheaf_locallyFree` | `LeBrunSalamon.PublishedInputs.SheafFunctoriality.exterior_locallyFree` |
| SHF-06 | `LeBrunSalamon.PhaseTwentySix.exteriorSheaf_pullback` | `LeBrunSalamon.PublishedInputs.SheafFunctoriality.pullback_exterior` |
| SHF-07 | `LeBrunSalamon.PhaseTwentySix.pullback_locallyFree` | `LeBrunSalamon.PublishedInputs.SheafFunctoriality.pullback_locallyFree` |
| SHF-08 | `LeBrunSalamon.PhaseTwentySix.symmetricPresentation_exists` | `LeBrunSalamon.PublishedInputs.SheafFunctoriality.symmetricPresentation` |

The exact historical publication locators, source checks, and evidence boundaries appear in the companion [JSON ledger](MILESTONE_PROGRESS.json). They are not represented here as 8 fresh literature audits.

## New work with partial credit only

The independent [targeted CI run](https://github.com/wajcha2/claude/actions/runs/41680976758) succeeded on `RecompileBasePart01`, `LSMilestoneStatement`, `LSMilestoneTopology`, and `LSNilpotentTopology`. Its receipt records current matching sources and a successful check of that selected graph. It does not compile the full theorem graph. See [the CI receipt](ci/41680976758/CI_RECEIPT.json).

The first [full current-source attempt](https://github.com/wajcha2/claude/actions/runs/41682674689) freshly passed 19 modules, including the repaired determinant module and its complete current ancestor graph. `RecompileBasePart07` then hit the compiler's 7200 MB memory cap, and 115 later dependent modules were blocked. This is a failed full run with real partial passes, not a cumulative acceptance. A 12000 MB replay on identical Lean sources is pending. No new whole acceptance unit is awarded for a blocked reverse-dependency cone.

The determinant result has also been upgraded beyond the baseline diagnostics: a [native audit of the fresh current artifacts](current_determinant_build/README.md) independently validates all five ancestors, identifies exactly five direct admitted dependencies, and confirms that the false old symplectic input is absent. The current proof module is checked, while acceptance of its later reverse-dependency cone remains pending.

The homothety/topology module constructs the actual diffeomorphism and homeomorphism, proves preservation of simple connectedness, and proves that a Wolf homothety forces the source to be simply connected. The native axiom print for the last theorem contains only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. This is real compiled progress within the endpoint and definition work. It does not close the full equivalence between the project point-symmetry predicate and the standard globally symmetric-space condition.

`RecompileBasePart05A`, `LSFirstJetEmbedding`, `LSFirstJetEmbeddingGeometry`, `LSClassicalReduction`, and `LSHomVelocity` all passed pinned compiler diagnostics against recovered baseline interfaces. Those checks validate the candidate proof terms under those imports; they do not validate the current cumulative dependency graph. Native axiom inspection finds no `sorryAx` in the actual dual-thickening zero-section theorem. The first-jet theorem has inherited admissions, which remain part of its transitive acceptance check. See [diagnostic scope](proof_batch_build/DIAGNOSTIC_SCOPE.json).

The completed native first-jet audit traversed all 78,870 reachable constants, including 583 project constants, and found exactly one direct admitted dependency: the generic pullback-rank theorem retained from Step 3b. There are no missing constants, custom project axioms, old first-jet assumptions or defective determinant inputs in that closure. The actual first-jet use has rank one and is explicitly covered by Vakil's Exercise 14.1.B(b); the companion [reference comparison](PULLBACK_RANK_REFERENCE.md) records the full-rank references and their publication types. This is a precise checked boundary for the diagnostic proof; the required current dependency-cone check is still separate.

Three elementary Step 3f leaves were identified as direct published directions by comparing their actual hypotheses and conclusions with primary sources. That comparison is part of the original obligations; it is not another 3 completion units. The first-order cotangent-Hom bijection still needs its generic conormal/canonical-map identification. See [the leaf-eligibility ledger](STEP3F_ELEMENTARY_LEAF_ELIGIBILITY.md).

The source of `LSMilestoneTarget` assembles the exact frozen conclusion conditionally on `PositiveQKSimpleConnectedness`, without adding an admitted proof of that full project claim. This conditional assembly has not passed the full current graph and does not satisfy the unconditional endpoint gate.

| Partial work | Governing units | Newly accepted units |
| --- | --- | ---: |
| Importable frozen statement and actual homothety/topology transports compiled on current dependencies, independently in CI. | DEF-07, GATE-01, GATE-02 | 0 |
| Generic split nilpotent-thickening topology proved in LSNilpotentTopology and compiled on current dependencies. Its project application in LSHomVelocity passed a baseline-interface diagnostic. | OBL-027 | 0 |
| The determinant repair and its complete current ancestor graph passed fresh CI; a native current-artifact audit confirms its remaining inputs and excludes the defective old input. The later reverse-dependency cone and final publication acceptance remain open. | OBL-023 | 0 |
| The actual first-jet proof in LSFirstJetEmbedding and LSFirstJetEmbeddingGeometry, and its public application in LSClassicalReduction, all passed pinned native diagnostics against recovered interfaces. Full current dependency and inherited-admission acceptance remain open. | OBL-018 | 0 |
| Three Step 3f leaf statements are eligible direct published directions after primary-source comparison. The cotangent-Hom bijection still needs its generic canonical-map/conormal bridge. Publication eligibility alone does not close these original obligations. | OBL-035, OBL-033, OBL-034, OBL-031 | 0 |
| No-sorry source assembly reaches the exact frozen endpoint conditionally on PositiveQKSimpleConnectedness. No admitted proof of that full project statement was introduced, and the complete assembly is not yet compiled. | GATE-01 | 0 |

## Earlier completion announcements

The recovered conversation reports Steps 3c–3e as “Passed cumulatively” on 2 November 2026 at 20:35 CET and Step 3f as “completed — PASSED” at 22:46 CET. These were completion announcements. Their source work is retained, and the lack of a recovered matching final certificate does not prove that later work never happened.

Their acceptance remains unrevalidated in this ledger because matching completion evidence and identified source repairs are still outstanding. The 30-unit floor measures the evidence currently sufficient for acceptance; it is not a claim that all later development work was lost or never performed.

## Pending original obligations: 91 fixed rows

IDs `OBL-001`–`OBL-091` follow the immutable data-row order in [ORIGINAL_OBLIGATIONS.csv](ORIGINAL_OBLIGATIONS.csv); CSV file line equals data row + 1. All rows remain pending acceptance. The JSON records the recovered source status and the current lexical admission status separately. A body with no direct `sorry` is not by itself an accepted unit.

| ID | Batch | Declaration |
| --- | --- | --- |
| OBL-001 | 3c | `LeBrunSalamon.PhaseTwentyEight.externalSection_finiteSum` |
| OBL-002 | 3c | `LeBrunSalamon.PhaseTwentyEight.locallyFree_sections_descend` |
| OBL-003 | 3c | `LeBrunSalamon.PhaseTwentyEight.nonvanishingOpen_pullback` |
| OBL-004 | 3c | `LeBrunSalamon.Core.ExternalTensorCoordinates.globalTensorMap_injective` |
| OBL-005 | 3c | `LeBrunSalamon.Core.ExternalTensorCoordinates.diagonalRestriction_iff_quotientCoefficients` |
| OBL-006 | 3c | `LeBrunSalamon.Core.ExternalTensorCoordinates.smooth_diagonal_square_detected` |
| OBL-007 | 3d | `LeBrunSalamon.StandardInputs.cotangentPullback_isIso` |
| OBL-008 | 3d | `LeBrunSalamon.Skeleton.dualBaseChange_isIso` |
| OBL-009 | 3d | `LeBrunSalamon.Construction.fiber_dimension` |
| OBL-010 | 3d | `LeBrunSalamon.Construction.fiber_finite` |
| OBL-011 | 3d | `LeBrunSalamon.Construction.vectorBundle_fiber_exact` |
| OBL-012 | 3d | `LeBrunSalamon.Construction.StandardInputs.BundleGeometry.vectorBundle_pullback_shortExact` |
| OBL-013 | 3d | `LeBrunSalamon.Construction.StandardInputs.BundleGeometry.homFiberEvaluation_injective_of_locallyFree` |
| OBL-014 | 3d | `LeBrunSalamon.Construction.StandardInputs.BundleGeometry.homBaseChange_isIso` |
| OBL-015 | 3d | `LeBrunSalamon.Construction.Smoothing.CoordinateCharts.StandardInputs.spec_pullback_isPushout` |
| OBL-016 | 3d | `LeBrunSalamon.Construction.Smoothing.CoordinateCharts.StandardInputs.generating_sections_unitOpen` |
| OBL-017 | 3d | `LeBrunSalamon.Construction.Normalization.totalBundle_exists` |
| OBL-018 | 3e | `LeBrunSalamon.ClassicalReduction.StandardInputs.polarizedEmbedding_firstJets` |
| OBL-019 | 3e | `LeBrunSalamon.PhaseTwentyFive.smooth_cotangent_rank` |
| OBL-020 | 3e | `LeBrunSalamon.PhaseTwentySix.tangentDeterminant_anticanonical` |
| OBL-021 | 3e | `LeBrunSalamon.PhaseTwentySix.ample_positivePower_iff` |
| OBL-022 | 3e | `LeBrunSalamon.PhaseTwentySix.determinant_shortExact` |
| OBL-023 | 3e | `LeBrunSalamon.PhaseTwentySeven.contact_distribution_determinant` |
| OBL-024 | 3e | `LeBrunSalamon.PhaseThirtyFive.contactFano_hasProjectiveEmbedding` |
| OBL-025 | 3f | `LeBrunSalamon.StandardInputs.formalTrait_twoComponent_lineNormalForm` |
| OBL-026 | 3f | `LeBrunSalamon.StandardInputs.formalTrait_smooth_lineNormalForm` |
| OBL-027 | 3f | `LeBrunSalamon.Construction.StandardInputs.InfinitesimalGeometry.dualThickening_zeroSection_surjective` |
| OBL-028 | 3f | `LeBrunSalamon.Construction.StandardInputs.InfinitesimalGeometry.dualThickening_normalForm_unique` |
| OBL-029 | 3f | `LeBrunSalamon.StandardInputs.affineLine_section_divisible` |
| OBL-030 | 3f | `LeBrunSalamon.StandardInputs.dualThickening_hom_vanishing` |
| OBL-031 | 3f | `LeBrunSalamon.Construction.StandardInputs.InfinitesimalGeometry.firstOrder_cotangentHom_bijective` |
| OBL-032 | 3f | `LeBrunSalamon.StandardInputs.standardConic_fundamentalClass_exists` |
| OBL-033 | 3f | `LeBrunSalamon.StandardInputs.affine_localDerivation_exists` |
| OBL-034 | 3f | `LeBrunSalamon.StandardInputs.affine_localDerivation_ext` |
| OBL-035 | 3f | `LeBrunSalamon.Refinement.Boundary.regular_of_heightOne` |
| OBL-036 | 3g | `LeBrunSalamon.StandardInputs.projectiveLineFamily_degree_constant` |
| OBL-037 | 3g | `LeBrunSalamon.CurveStandardInputs.exists_laurent_expansion_with_pole` |
| OBL-038 | 3g | `LeBrunSalamon.PhaseThirty.nonconstant_complexCurve_differential_ne_zero` |
| OBL-039 | 3g | `LeBrunSalamon.PhaseThirtyTwo.birkhoffGrothendieck` |
| OBL-040 | 3g | `LeBrunSalamon.Skeleton.sourceBivector_existsUnique` |
| OBL-041 | 3g | `LeBrunSalamon.Skeleton.projectiveCoordinates_exists` |
| OBL-042 | 3g | `LeBrunSalamon.PhaseThirtyTwo.projectiveLineBundle_classification` |
| OBL-043 | 3g | `LeBrunSalamon.PhaseThirtyTwo.projectiveLine_tangent_twist` |
| OBL-044 | 3h | `LeBrunSalamon.PhaseThirty.openImmersion_cotangentMap_isIso` |
| OBL-045 | 3h | `LeBrunSalamon.PhaseThirty.smoothClosedImmersion_conormal_rank` |
| OBL-046 | 3h | `LeBrunSalamon.Construction.Charts.smooth_differential_surjective` |
| OBL-047 | 3h | `LeBrunSalamon.Construction.Charts.differential_surjective_implies_smooth` |
| OBL-048 | 3h | `LeBrunSalamon.Construction.Charts.tangent_dimension_of_smooth` |
| OBL-049 | 3i | `LeBrunSalamon.StandardInputs.homOpen_sourceFirstJet_dominant` |
| OBL-050 | 3i | `LeBrunSalamon.Construction.Lines.HomDegree.StandardInputs.degree_open` |
| OBL-051 | 3i | `LeBrunSalamon.Skeleton.homSpacePresentation_exists` |
| OBL-052 | 3i | `LeBrunSalamon.StandardInputs.homOpen_twoPointEvaluation_dominant` |
| OBL-053 | 3i | `LeBrunSalamon.Construction.HomNeighborhood.StandardInputs.free_neighborhood` |
| OBL-054 | 3i | `LeBrunSalamon.Construction.Smoothing.HomDeformationInput.StandardInputs.presentation_exists_of_projectiveProduct` |
| OBL-055 | 3i | `LeBrunSalamon.Construction.Smoothing.HomDeformationInput.StandardInputs.locallyOfFinitePresentation` |
| OBL-056 | 3i | `LeBrunSalamon.Construction.Smoothing.HomDeformationInput.StandardInputs.smooth_of_firstCohomology_vanishes` |
| OBL-057 | 3j | `LeBrunSalamon.StandardInputs.smooth_connected_complex_geometricallyIntegral` |
| OBL-058 | 3j | `LeBrunSalamon.StandardInputs.proper_flat_normal_generic_globalFunctions` |
| OBL-059 | 3j | `LeBrunSalamon.Construction.Smoothing.DegreeSpecialization.StandardInputs.degree_near_twoComponent_fibre` |
| OBL-060 | 3j | `LeBrunSalamon.StandardInputs.isNodalCurve_pullback` |
| OBL-061 | 3j | `LeBrunSalamon.StandardInputs.stableMapSchemeCover_exists` |
| OBL-062 | 3j | `LeBrunSalamon.StandardInputs.nodalCurveSquare_normal` |
| OBL-063 | 3j | `LeBrunSalamon.StandardInputs.heightOne_regular_of_formalArcs` |
| OBL-064 | 3j | `LeBrunSalamon.SchemeStandardInputs.smooth_complex_reduced` |
| OBL-065 | 3k | `LeBrunSalamon.StandardInputs.proper_automorphism_spreads_with_parameter` |
| OBL-066 | 3k | `LeBrunSalamon.StandardInputs.finite_generic_trivialization_spreads` |
| OBL-067 | 3k | `LeBrunSalamon.Construction.Descent.FiniteCoverStandardInputs.finite_dominant_genericEtale` |
| OBL-068 | 3k | `LeBrunSalamon.Construction.Descent.totalLine_exists` |
| OBL-069 | 3k | `LeBrunSalamon.Construction.Descent.TotalLine.projection_affine` |
| OBL-070 | 3k | `LeBrunSalamon.Construction.Descent.TotalLine.projection_lfp` |
| OBL-071 | 3k | `LeBrunSalamon.Construction.Descent.normalizedImage_exists` |
| OBL-072 | 3k | `LeBrunSalamon.Construction.Descent.ramification_le_degree` |
| OBL-073 | 3l | `LeBrunSalamon.StandardInputs.finite_normal_branch_divisor_formalModel` |
| OBL-074 | 3l | `LeBrunSalamon.StandardInputs.smooth_projectiveLineFamily_transverse_divisor` |
| OBL-075 | 3l | `LeBrunSalamon.StandardInputs.finite_curvePullback_normalization_at_dvr` |
| OBL-076 | 3l | `LeBrunSalamon.Construction.Descent.purity_over_contactSquare` |
| OBL-077 | 3l | `LeBrunSalamon.Construction.Descent.finiteEtale_contactSquare_trivial` |
| OBL-078 | 3l | `LeBrunSalamon.Construction.NormalExtension.extend_from_heightOne` |
| OBL-079 | 3m | `LeBrunSalamon.StandardInputs.finiteType_nondominant_positiveFiber` |
| OBL-080 | 3m | `LeBrunSalamon.StandardInputs.finiteType_tensorProduct_geometry` |
| OBL-081 | 3m | `LeBrunSalamon.Construction.Lines.PublishedDirections.StandardInputs.general_selectedDirections_span` |
| OBL-082 | 3m | `LeBrunSalamon.Construction.Lines.PublishedDirections.StandardInputs.general_legendrianDirections` |
| OBL-083 | 3m | `LeBrunSalamon.PhaseThirtyTwo.primitiveContactFano_hasFreeContactLine` |
| OBL-084 | 3n | `LeBrunSalamon.ClassicalActions.StandardInputs.contactAutomorphismGroup_localOrbits` |
| OBL-085 | 3n | `LeBrunSalamon.ClassicalReduction.StandardInputs.nonprimitive_contactLine_embedding` |
| OBL-086 | 3n | `LeBrunSalamon.ClassicalReduction.StandardInputs.homogeneous_contact_adjointPresentation` |
| OBL-087 | 3n | `LeBrunSalamon.ClassicalReduction.StandardInputs.positiveQK_twistorReduction` |
| OBL-088 | 3n | `LeBrunSalamon.Skeleton.nilpotent_hasEulerLift` |
| OBL-089 | 3n | `LeBrunSalamon.Skeleton.adjointRank_even` |
| OBL-090 | 3n | `LeBrunSalamon.Skeleton.globalSymmetries_parallelCurvature` |
| OBL-091 | 3n | `LeBrunSalamon.Skeleton.homothety_parallelCurvature` |

## Definition validations: 8 pending units

The Step 2 record froze and compiled the theorem statement as a definition. It explicitly left these 8 identifications open. Copying that definition without alteration preserves the specification; it does not prove its agreement with the standard mathematical notions.

| ID | Validation | Status |
| --- | --- | --- |
| DEF-01 | smooth endomorphism fields versus smooth endomorphism-bundle sections | Pending |
| DEF-02 | parallel quaternionic rank-three bundle versus holonomy contained in Sp(n)Sp(1) for n >= 2 | Pending |
| DEF-03 | curvature commutator and sign convention | Pending |
| DEF-04 | extension of tangent vectors to smooth fields and uniqueness of curvature witness | Pending |
| DEF-05 | orthonormal-basis independence of scalar curvature | Pending |
| DEF-06 | parallel-curvature predicate versus nabla Rm = 0 | Pending |
| DEF-07 | point symmetries versus the standard globally symmetric-space condition | Pending |
| DEF-08 | Wolf classification of the intrinsic target class | Pending |

## Final gates: 4 pending units

| ID | Gate and acceptance requirement | Current boundary |
| --- | --- | --- |
| GATE-01 | **Exact frozen theorem endpoint.** A compiled unconditional theorem with the unchanged frozen hypotheses and both conclusions, including the actual positive metric Wolf homothety; no unproved PositiveQKSimpleConnectedness parameter. | Frozen specification preserved and importable statement compiled. Target assembly is conditional, and its full dependency graph is not yet accepted. |
| GATE-02 | **Dependency-complete current compilation.** All required current modules and reverse dependencies compile with exact source/dependency/runtime receipts, including the final target. | Four modules passed independent current-source CI; several larger candidates passed baseline-interface diagnostics. The full current graph remains open. |
| GATE-03 | **Exhaustive final transitive admission audit.** Native final-theorem dependencies and every source admission agree with the exact published-theorem allowlist; no novel proof, composite application, transport, or hidden extra assumption remains admitted. | Static inventories and selected exact-source comparisons exist. A topology transport has an axiom print containing no sorryAx. The final theorem trust audit remains open. |
| GATE-04 | **Reproducible locked milestone checkpoint.** One final source revision packages the frozen specification, source and runtime locks, accepted-unit evidence, whole-graph build receipts, and final trust-audit result in a reproducible checkpoint. | Runtime, source-preserving recovery, replay tooling, and targeted CI evidence exist. They are not a completed final milestone checkpoint. |

## Evidence and snapshot

Recorded UTC: `2026-11-03T17:18:39.770536+00:00`. Current source snapshot: `82f024f5ce739874efbbd23a99fea0b1f9bb99e04ba1432d65072477c44aad39` across 135 Lean modules. The companion JSON specifies the hashing convention and records the hashes of the input records.

Frozen target SHA-256: `9afe9c5b2e63db17e8f217b71c821eaca83fe26c5cfbc2956fc1b92832d09296`.

Historical records: recovered Step 3b archive `5cd10ccfa75b92566913e140ce53c437563a60f5864c6f1c8f56799fd913b03c`, members `lebrun_step3b_final/prior_step3a/STEP3A_STATUS.json` and `lebrun_step3b_final/STEP3B_STATUS.json`; Step 2 `final/audit/STATEMENT_AUDIT.json`. Record hashes and limitations are preserved in the JSON evidence table.

This ledger was produced by reading records and source. No Lean process was invoked and no proof source, plan, status, or README was changed. Only the two milestone-progress ledger files were written.
