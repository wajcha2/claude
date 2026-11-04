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

## Current targeted compatibility replay

The new VelocityAdditionFamily repair has an exact current native pass (30.362s) and no new admissions. A separate120-module smoothing replay is queued with116 strictly validated prior outputs. This run excludes Conic and does not establish the full reverse-cone gate. Accepted progress remains30/133. See [the scoped checkpoint](point1_checkpoint/TARGETED_SMOOTHING_SCOPE.json).

## New work with partial credit only — checkpoint — 2026-11-04T03:38:48.057058+00:00

**The proof and publication boundary is checked for all 43 original Steps 3c–3g obligations; the required current reverse-dependency compilation gate is still open.** The separately inherited affine-projection obligation OBL-069 is also checked. This checkpoint adds no accepted checklist units before the original plan's complete gate passes.

This immutable candidate contains **268 Lean modules and 99 direct `sorry` tokens**. The frozen target and pinned toolchain lock are unchanged. `SOURCE.sha256` and [the source freeze](point1_checkpoint/FREEZE.json) identify the exact candidate. Neither helper counts nor admission-token counts measure completion or establish publication eligibility.

### Current native and source evidence

The dedicated Point1 stage of [CI 41763014879](https://github.com/wajcha2/claude/actions/runs/41763014879) passed **190/190 modules**: the 19 distinct containing modules for the fixed 43 obligations and their complete project ancestry. All source files, dependency outputs, logs, compiler/runtime identities and final ancestry checks were independently validated. [The Point1 evidence](ci/41763014879/point1/README.md) records its exact scope.

The exhaustive declaration audit then checked **43 original roots plus OBL-069**, with **50 distinct actual admitted inputs**. Every actual leaf passed the independent primary-source/hypothesis/map review and is bound to its native type, source, output and ancestry hashes. No original project conclusion remains directly admitted in this audited boundary; no missing constant or unexpected project/global axiom was found. The old project-specific `TotalLine.projection_affine` admission is absent. Its actual theorem now reaches the precise generic affine section-representability input. See [the complete acceptance preparation](point1_acceptance_current_20261104T031351/README.md) and [the source-eligibility ledger](POINT1_PUBLISHED_LEAF_ELIGIBILITY.md).

The 29-root native tranche was carried forward only after all of its recorded ancestor source/output/import/dependency stamps and artifact bytes matched the same 190-module snapshot; the remaining 14 roots and OBL-069 were checked natively against that snapshot. All 44 original public headers match the certified baseline after comments and whitespace are removed, and the 15 changed-tranche native signatures are retained with their stated scope. These checks do not claim a new historical-baseline rebuild or completion of the separate definition-validation obligations. At this freeze, the entire 190-module source/output/ancestry binding was rechecked again in [POINT1_BOUNDARY_AT_FREEZE.json](point1_checkpoint/POINT1_BOUNDARY_AT_FREEZE.json).

| Batch | Original obligations | Native proof and publication boundary | Acceptance |
| --- | ---: | --- | --- |
| 3c | 6 | Passed | Required reverse cone pending |
| 3d | 11 | Passed | Required reverse cone pending |
| 3e | 7 | Passed | Required reverse cone pending |
| 3f | 11 | Passed | Required reverse cone pending |
| 3g | 8 | Passed | Required reverse cone pending |
| Separate OBL-069 | 1 | Passed | Required reverse cone pending |

### Remaining compilation gate

The latest full replay checked commit `3656bd1c17a200bf9d80edc86f289fb1861ff4d2` with all **268 modules** selected. It accepted **240**, with **2 failed and 26 blocked**. Across all stages of that run, 138 modules compiled natively and 102 came from the strictly validated prior cache. The final stage reports 40 fresh builds and 200 reuses because it also reused the earlier stages of the same run. Final source/runtime/ancestry validation found no invalidations. The failed modules were `LSConicJets`, `LSScaledVelocities`; [the full CI evidence](ci/41763014879/README.md) preserves their exact diagnostics and all successful receipts.

This is the remaining acceptance gate for Point1: compile the changed modules and their required current reverse-dependency cone. The original plan explicitly requires it, even though the selected 190-module proof boundary already passes. The recorded Conic failure includes an expensive kernel conversion at the identity-contact velocity, along with compatibility rewrites; the scaled-velocity failures are explicit map/carrier/rewriting mismatches. Later checked compatibility repairs in this candidate retain their own exact evidence and do not retroactively change the recorded CI result. Off-graph unverified drafts are excluded from the source graph.

The next stock-compiler replay selects all **268 modules**, with a 12000 MB memory cap, a 900-second per-module limit, and run **41763014879** as its sole cache source. Full source/import/lock/output/ancestry checks permit **240** previous outputs at this freeze. It first checks the LSSmoothingAssembly closure, including the repaired scaled-velocity branch, and uploads that separate diagnostic artifact. It then preserves separate Ext01, Geometry and fixed-Point1 artifacts before the full graph, and revalidates the entire selected graph at completion. No result from that future run is assumed.

### Current execution order and accounting

Finish the outstanding compatibility repairs, replay the complete required reverse cone, and bind its successful artifacts to the already completed 43+1 native/publication audit. Only then can the parent-controlled fixed ledger promote the original obligations. Continue the remaining batches and the frozen endpoint/definition-validation work under the existing plan after that gate; the stronger Wolf-homothety endpoint and the whole published-theorems-only milestone remain open.

The conservative accepted floor remains **30/133 = 22.56%, rounded to 23%**. This is a count of fully accepted checklist units, not mathematical effort, elapsed time or the proportion of compiled modules. The completed 43-root proof/publication work is recorded substantively without bypassing the original reverse-cone gate.

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

Recorded UTC: `2026-11-04T03:38:48.057058+00:00`. Frozen source snapshot: `61f610c63ac681cbb0e66cb369ed84dae03838cd472b2b0c4f9c92164f9bede5` across 268 Lean modules. The companion JSON specifies the hashing convention and records the hashes of the input records.

Frozen target SHA-256: `9afe9c5b2e63db17e8f217b71c821eaca83fe26c5cfbc2956fc1b92832d09296`.

Historical records: recovered Step 3b archive `5cd10ccfa75b92566913e140ce53c437563a60f5864c6f1c8f56799fd913b03c`, members `lebrun_step3b_final/prior_step3a/STEP3A_STATUS.json` and `lebrun_step3b_final/STEP3B_STATUS.json`; Step 2 `final/audit/STATEMENT_AUDIT.json`. Record hashes and limitations are preserved in the JSON evidence table.

This ledger was produced by reading records and source. No Lean process was invoked and no proof source, plan, status, or README was changed. Only the two milestone-progress ledger files were written.
