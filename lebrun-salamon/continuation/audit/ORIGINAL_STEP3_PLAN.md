# LeBrun–Salamon formalisation — Step 3 proof/deletion subdivision

## Binding conclusion

**None of the 122 current admitted declarations may retain `sorry` in its present form.**

- 35 have explicitly project-specific signatures.
- 87 look generic, but are still composites, specialisations, transports, or otherwise lack a one-to-one exact published statement audit.
- 24 are one-occurrence deletion candidates and must be tested in Step 3a; this has not yet been compiler-tested.
- 98 are not in the one-occurrence deletion-candidate set and must be treated as proof/refactoring obligations unless a later dependency check proves them dead.

The permitted end state is: newly isolated exact published leaves may contain `sorry`; every declaration below must be deleted or have a Lean proof from those leaves.

## Global acceptance rule

- No current admitted declaration is an exact published leaf in its present project interface.
- A current declaration must be deleted if unused, proved directly, or proved from newly isolated exact published leaves.
- Only the newly isolated exact published leaves may retain sorry, with one source, stable locator, exact hypothesis/conclusion audit, and no project-specific wrapper types.
- Every substep compiles its changed modules and reverse-dependency cone before acceptance.

## Step order

The order below is dependency-sensitive. A later batch may begin in parallel only when it does not import an unfinished earlier batch.

### 3a — Liveness triage and strict boundary infrastructure

**Depends on:** none

**Scope:** cross-cutting liveness triage on 24 candidates plus 1 direct declaration.

**Goal.** Test all 24 one-occurrence admissions for deletion; remove dead declarations; give `stageDescription` a complete definitional body; freeze exact-leaf metadata and checker rules.

**Method.** Use declaration-level reverse references, not grep alone. Delete one candidate at a time, compile its module and reverse-dependency cone, then update the manifest. No new `sorry` is allowed in this substep.

**Gate.** Every deletion candidate is classified as deleted or retained with a real consumer. `stageDescription` has no admission. The boundary checker and assignment manifest agree exactly.

**Assigned declarations:**
- `LeBrunSalamon.Project.stageDescription` *(delete-test in 3a)*

### 3b — Tensor, dual, exterior and symmetric sheaf functoriality

**Depends on:** 3a

**Scope:** 11 declarations; 3 are deletion candidates from 3a; expected retained count after successful liveness deletion: 8.

**Goal.** Replace the basic sheaf-construction admissions by proofs from universal properties and finite-locally-free algebra.

**Method.** Introduce only exact generic leaves for tensor pullback, dual base change, exterior/symmetric powers and Kähler differentials when mathlib lacks them; prove all project wrappers by universal-property extensionality and local finite-free calculations.

**Candidate exact published leaf families:**
- pullback of tensor products of module sheaves
- finite locally free dual base change
- exterior and symmetric power universal properties
- Kähler differential universal property

**Gate.** All declarations in this batch compile without direct admissions; surviving exact leaves are generic and individually cited.

**Assigned declarations:**
- `LeBrunSalamon.PhaseTwentyFive.tensorSheaf_pullback`
- `LeBrunSalamon.PhaseTwentyFive.dualSheaf_pullback`
- `LeBrunSalamon.PhaseTwentyFive.cotangentPresentation_exists`
- `cotangent_openRestriction` *(delete-test in 3a)*
- `LeBrunSalamon.PhaseTwentySix.exteriorPresentation_exists`
- `exteriorSheaf_locallyFree`
- `exteriorSheaf_pullback`
- `symmetricPresentation_exists`
- `symmetricSheaf_locallyFree` *(delete-test in 3a)*
- `symmetricSheaf_pullback` *(delete-test in 3a)*
- `pullback_locallyFree`

### 3c — External tensors, diagonal jets and descent of sections

**Depends on:** 3a, 3b

**Scope:** 6 declarations; 0 are deletion candidates from 3a; expected retained count after successful liveness deletion: 6.

**Goal.** Prove the external tensor/diagonal and section-descent wrappers that are currently composite corollaries.

**Method.** Separate exact diagonal associated-graded facts from project coordinates. Prove finite-sum and descent statements by affine/local trivialization and faithfully-flat or structure-sheaf descent. In particular, `smooth_diagonal_square_detected` must be derived, not admitted.

**Candidate exact published leaf families:**
- regular immersion diagonal and associated graded
- finite projective duality
- descent for quasi-coherent locally free sheaves

**Gate.** No `sorry` remains in the six wrappers; the diagonal detection theorem depends only on exact generic leaves.

**Assigned declarations:**
- `externalSection_finiteSum`
- `locallyFree_sections_descend`
- `LeBrunSalamon.PhaseTwentyEight.nonvanishingOpen_pullback`
- `LeBrunSalamon.Core.ExternalTensorCoordinates.globalTensorMap_injective`
- `LeBrunSalamon.Core.ExternalTensorCoordinates.diagonalRestriction_iff_quotientCoefficients`
- `LeBrunSalamon.Core.ExternalTensorCoordinates.smooth_diagonal_square_detected`

### 3d — Base change, fibers, pushouts and total spaces

**Depends on:** 3a, 3b

**Scope:** 11 declarations; 0 are deletion candidates from 3a; expected retained count after successful liveness deletion: 11.

**Goal.** Prove all project-specific base-change and fiber comparison declarations.

**Method.** Use flatness of locally free quotients, stalkwise exactness, the categorical affine pushout theorem, unit-locus pullback, and relative Spec. Exact literature leaves must not mention project wrappers such as `TotalBundle` or `DualThickening`.

**Candidate exact published leaf families:**
- base change for short exact sequences with flat quotient
- fiber of a locally free sheaf
- affine pushout along a surjective ring map
- relative Spec of a symmetric algebra
- unit loci of generated invertible sheaves

**Gate.** Every map in the conclusions is the actual canonical map from the project definitions, and all 11 wrappers compile without admission.

**Assigned declarations:**
- `LeBrunSalamon.StandardInputs.cotangentPullback_isIso`
- `LeBrunSalamon.Skeleton.dualBaseChange_isIso`
- `LeBrunSalamon.Construction.fiber_dimension`
- `LeBrunSalamon.Construction.fiber_finite`
- `LeBrunSalamon.Construction.vectorBundle_fiber_exact`
- `LeBrunSalamon.Construction.StandardInputs.BundleGeometry.vectorBundle_pullback_shortExact`
- `LeBrunSalamon.Construction.StandardInputs.BundleGeometry.homFiberEvaluation_injective_of_locallyFree`
- `LeBrunSalamon.Construction.StandardInputs.BundleGeometry.homBaseChange_isIso`
- `LeBrunSalamon.Construction.Smoothing.CoordinateCharts.StandardInputs.spec_pullback_isPushout`
- `LeBrunSalamon.Construction.Smoothing.CoordinateCharts.StandardInputs.generating_sections_unitOpen`
- `totalBundle_exists`

### 3e — Ampleness, determinants, first jets and principal parts

**Depends on:** 3a, 3b, 3c, 3d

**Scope:** 14 declarations; 7 are deletion candidates from 3a; expected retained count after successful liveness deletion: 7.

**Goal.** Prove the ample-line, determinant and principal-parts interface used later by the contact and Hom arguments.

**Method.** First delete any dead API declarations. For survivors, state exact Serre/ampleness and principal-parts filtration leaves, then prove the specific line-bundle and rank formulas. `polarizedEmbedding_firstJets` is a proof from the actual closed immersion and fat-point restriction, not a literature leaf.

**Candidate exact published leaf families:**
- ampleness under positive powers and closed pullback
- eventual global generation
- determinant of a short exact sequence
- principal-parts filtration for a smooth separated morphism

**Gate.** All retained declarations compile; no project-specific first-jet, determinant or contact statement remains admitted.

**Assigned declarations:**
- `LeBrunSalamon.ClassicalReduction.StandardInputs.polarizedEmbedding_firstJets`
- `smooth_cotangent_rank`
- `tangentDeterminant_anticanonical`
- `ample_positivePower_iff`
- `ample_tensor` *(delete-test in 3a)*
- `ample_closedPullback` *(delete-test in 3a)*
- `ample_affineBasis` *(delete-test in 3a)*
- `ample_eventualGlobalGeneration` *(delete-test in 3a)*
- `determinant_shortExact`
- `contact_distribution_determinant`
- `firstPrincipalParts_exact` *(delete-test in 3a)*
- `principalParts_locallyFree` *(delete-test in 3a)*
- `principalParts_higher_exact` *(delete-test in 3a)*
- `contactFano_hasProjectiveEmbedding`

### 3f — Affine algebra, square-zero thickenings and nodal local models

**Depends on:** 3a, 3b, 3d

**Scope:** 12 declarations; 1 are deletion candidates from 3a; expected retained count after successful liveness deletion: 11.

**Goal.** Eliminate the algebraic and infinitesimal wrappers around dual numbers, derivations, node algebras and the standard conic.

**Method.** Prove the dual-thickening normal form and vanishing statements directly. Derive first-order deformation/cotangent bijectivity from the Kähler differential universal property. For node normality and formal trait models, admit only an exact published normality/semistable local-form theorem and prove the specialization.

**Candidate exact published leaf families:**
- Kähler differentials versus derivations
- normality criterion for `R[u,v]/(uv-a)` over a DVR
- standard semistable node local form
- hypersurface conormal/fundamental class

**Gate.** The local algebra modules compile with no wrapper admissions; any surviving `sorry` is an exact generic theorem with no project types.

**Assigned declarations:**
- `LeBrunSalamon.StandardInputs.formalTrait_twoComponent_lineNormalForm`
- `formalTrait_smooth_lineNormalForm`
- `LeBrunSalamon.Construction.StandardInputs.InfinitesimalGeometry.dualThickening_zeroSection_surjective`
- `LeBrunSalamon.Construction.StandardInputs.InfinitesimalGeometry.dualThickening_normalForm_unique`
- `LeBrunSalamon.StandardInputs.affineLine_section_divisible`
- `LeBrunSalamon.StandardInputs.dualThickening_hom_vanishing`
- `LeBrunSalamon.Construction.StandardInputs.InfinitesimalGeometry.firstOrder_cotangentHom_bijective`
- `LeBrunSalamon.StandardInputs.standardConic_fundamentalClass_exists`
- `nodeAlgebra_integrallyClosed` *(delete-test in 3a)*
- `LeBrunSalamon.StandardInputs.affine_localDerivation_exists`
- `LeBrunSalamon.StandardInputs.affine_localDerivation_ext`
- `regular_of_heightOne`

### 3g — Projective-line geometry, splitting and source normalization

**Depends on:** 3a, 3b, 3e, 3f

**Scope:** 11 declarations; 3 are deletion candidates from 3a; expected retained count after successful liveness deletion: 8.

**Goal.** Build the complete P1 interface needed by lines, conics and source tensors.

**Method.** Use exact leaves for Pic(P1), Birkhoff–Grothendieck, T_P1=O(2), degree and ampleness. Prove the chosen-point/projectiveTwist transports, the normalized source bivector, projective coordinates and Laurent embedding explicitly.

**Candidate exact published leaf families:**
- Picard group of P1
- Birkhoff–Grothendieck theorem
- Euler sequence on P1
- degree/ampleness on proper curves
- Laurent expansion at a boundary DVR

**Gate.** All actual `ProjectiveLineOverC`, marked-point and normalized-coordinate wrappers compile without admission.

**Assigned declarations:**
- `LeBrunSalamon.StandardInputs.projectiveLineFamily_degree_constant`
- `LeBrunSalamon.CurveStandardInputs.exists_laurent_expansion_with_pole`
- `nonconstant_complexCurve_differential_ne_zero`
- `LeBrunSalamon.PhaseThirtyTwo.birkhoffGrothendieck`
- `LeBrunSalamon.PhaseThirtyTwo.splitting_unique_upToPermutation` *(delete-test in 3a)*
- `LeBrunSalamon.PhaseThirtyTwo.ample_positiveDegreeOnCurve` *(delete-test in 3a)*
- `sourceBivector_existsUnique`
- `projectiveCoordinates_exists`
- `LeBrunSalamon.PhaseThirtyTwo.projectiveLineBundle_classification`
- `LeBrunSalamon.PhaseThirtyTwo.projectiveTwist_ample_iff` *(delete-test in 3a)*
- `LeBrunSalamon.PhaseThirtyTwo.projectiveLine_tangent_twist`

### 3h — Cotangent sequences and smoothness criteria

**Depends on:** 3a, 3b, 3d

**Scope:** 8 declarations; 3 are deletion candidates from 3a; expected retained count after successful liveness deletion: 5.

**Goal.** Prove the cotangent transitivity, immersion/étale comparison and chart differential criteria.

**Method.** Admit only exact cotangent-complex or differential criteria from the literature. Prove that the project’s canonical maps are the maps in those sequences, and derive rank/surjectivity statements by exactness and local freeness.

**Candidate exact published leaf families:**
- transitivity exact sequence for Kähler differentials
- étale/open immersion cotangent vanishing
- closed immersion conormal sequence
- Jacobian/smoothness criterion

**Gate.** All eight declarations compile and use the actual canonical maps; no abstract isomorphism is substituted.

**Assigned declarations:**
- `smooth_cotangent_transitivity_shortExact` *(delete-test in 3a)*
- `openImmersion_cotangentMap_isIso`
- `etale_cotangentMap_isIso` *(delete-test in 3a)*
- `closedImmersion_cotangentMap_epi` *(delete-test in 3a)*
- `smoothClosedImmersion_conormal_rank`
- `Charts.smooth_differential_surjective`
- `Charts.differential_surjective_implies_smooth`
- `Charts.tangent_dimension_of_smooth`

### 3i — Hom representability, deformation smoothness and evaluation dominance

**Depends on:** 3a, 3g, 3h

**Scope:** 8 declarations; 1 are deletion candidates from 3a; expected retained count after successful liveness deletion: 7.

**Goal.** Prove the Hom-space and first-jet/evaluation wrappers used by the moving-line and conic arguments.

**Method.** Separate representability, local finite presentation and obstruction theory into exact leaves. Prove the supplied scheme represents the same functor, identify tangent maps, use H1-vanishing for smoothness, and derive dominance from smooth evaluation. Delete `homOpen_twoPointEvaluation_dominant` if it is genuinely unused.

**Candidate exact published leaf families:**
- representability of relative Hom/Mor
- deformation obstruction in H1
- openness of free/very free maps
- smooth evaluation and generic dominance
- degree locally constant/open on Hom components

**Gate.** All retained Hom wrappers compile without admission and their tangent maps are definitionally/canonically identified.

**Assigned declarations:**
- `LeBrunSalamon.StandardInputs.homOpen_sourceFirstJet_dominant`
- `LeBrunSalamon.Construction.Lines.HomDegree.StandardInputs.degree_open`
- `homSpacePresentation_exists`
- `_root_.LeBrunSalamon.StandardInputs.homOpen_twoPointEvaluation_dominant` *(delete-test in 3a)*
- `LeBrunSalamon.Construction.HomNeighborhood.StandardInputs.free_neighborhood`
- `LeBrunSalamon.Construction.Smoothing.HomDeformationInput.StandardInputs.presentation_exists_of_projectiveProduct`
- `LeBrunSalamon.Construction.Smoothing.HomDeformationInput.StandardInputs.locallyOfFinitePresentation`
- `LeBrunSalamon.Construction.Smoothing.HomDeformationInput.StandardInputs.smooth_of_firstCohomology_vanishes`

### 3j — Stable maps, nodal families and global functions

**Depends on:** 3a, 3f, 3g, 3i

**Scope:** 9 declarations; 1 are deletion candidates from 3a; expected retained count after successful liveness deletion: 8.

**Goal.** Prove the stable-map cover, nodal base change, normality and global-function statements.

**Method.** State exact stable-map existence/cover and nodal base-change leaves. Derive normality of the square and height-one regularity. Split each global-functions theorem into Stein factorization, geometric integrality and normal-base pieces, proving the project conclusion from them.

**Candidate exact published leaf families:**
- stable-map algebraic stack/coarse-space and finite scheme cover
- étale-local nodal curve structure and base change
- Serre R1+S2 normality
- Stein factorization/global functions for proper geometrically connected fibers

**Gate.** All nine wrappers compile; no conjunction or multi-source corollary remains as a direct `sorry`.

**Assigned declarations:**
- `LeBrunSalamon.StandardInputs.smooth_connected_complex_geometricallyIntegral`
- `proper_flat_connectedReduced_globalFunctions` *(delete-test in 3a)*
- `LeBrunSalamon.StandardInputs.proper_flat_normal_generic_globalFunctions`
- `LeBrunSalamon.Construction.Smoothing.DegreeSpecialization.StandardInputs.degree_near_twoComponent_fibre`
- `LeBrunSalamon.StandardInputs.isNodalCurve_pullback`
- `LeBrunSalamon.StandardInputs.stableMapSchemeCover_exists`
- `LeBrunSalamon.StandardInputs.nodalCurveSquare_normal`
- `LeBrunSalamon.StandardInputs.heightOne_regular_of_formalArcs`
- `LeBrunSalamon.SchemeStandardInputs.smooth_complex_reduced`

### 3k — Finite covers, normalization and numerical ramification data

**Depends on:** 3a, 3d, 3j

**Scope:** 11 declarations; 3 are deletion candidates from 3a; expected retained count after successful liveness deletion: 8.

**Goal.** Construct the generic finite-cover/descent API without project-specific admissions.

**Method.** Use exact leaves for generic étaleness, normalization and ramification theory. Prove existence/uniqueness/positivity of the project’s `GenericDegree` and `RamificationIndex` structures directly from those leaves and definitions. Prove the total-line and normalized-image wrappers by relative Spec/normalization.

**Candidate exact published leaf families:**
- finite dominant morphism generically étale in characteristic zero
- normalization of finite-type curves
- degree of a finite morphism
- ramification index and fundamental inequality
- spreading out finite presentation data

**Gate.** All retained descent-core declarations compile; definitional existence/uniqueness facts are proved, not admitted.

**Assigned declarations:**
- `LeBrunSalamon.StandardInputs.proper_automorphism_spreads_with_parameter`
- `LeBrunSalamon.StandardInputs.finite_generic_trivialization_spreads`
- `Descent.FiniteCoverStandardInputs.finite_dominant_genericEtale`
- `Descent.totalLine_exists`
- `Descent.TotalLine.projection_affine`
- `Descent.TotalLine.projection_lfp`
- `Descent.normalizedImage_exists`
- `Descent.genericDegree_existsUnique` *(delete-test in 3a)*
- `Descent.genericDegree_positive` *(delete-test in 3a)*
- `Descent.ramificationIndex_existsUnique` *(delete-test in 3a)*
- `Descent.ramification_le_degree`

### 3l — Purity, branch divisors and codimension-one extension

**Depends on:** 3a, 3k

**Scope:** 6 declarations; 0 are deletion candidates from 3a; expected retained count after successful liveness deletion: 6.

**Goal.** Prove the hard branch/ramification and normal-extension wrappers.

**Method.** This is a high-risk batch. Isolate exact leaves for purity, Laksov–Speiser transversality, tame/Kummer local form and Hartogs/reflexive extension. Then prove the actual project statements, including open-set avoidance and the normalization point, by explicit composition. No composite branch theorem may remain admitted.

**Candidate exact published leaf families:**
- purity of branch locus
- transversality theorem for a smooth dominant family
- tame/Kummer local model
- normalization unchanged over regular locus
- extension of sections on a normal scheme from codimension one

**Gate.** The six declarations compile with only exact generic literature leaves; all project-specific branch data are constructed in Lean.

**Assigned declarations:**
- `LeBrunSalamon.StandardInputs.finite_normal_branch_divisor_formalModel`
- `LeBrunSalamon.StandardInputs.smooth_projectiveLineFamily_transverse_divisor`
- `LeBrunSalamon.StandardInputs.finite_curvePullback_normalization_at_dvr`
- `Descent.purity_over_contactSquare`
- `Descent.finiteEtale_contactSquare_trivial`
- `NormalExtension.extend_from_heightOne`

### 3m — Contact lines, Legendrian directions and cone/product geometry

**Depends on:** 3a, 3g, 3i, 3j

**Scope:** 5 declarations; 0 are deletion candidates from 3a; expected retained count after successful liveness deletion: 5.

**Goal.** Prove the contact-line/direction wrappers and the generic dimension arguments used for cone addition.

**Method.** Admit exact statements of the corrected contact-line theorems and spanning theorem. Prove the chosen dense opens, affine-cone coordinates, tensor-product domain/dimension corollary, and positive-fiber conclusion in Lean.

**Candidate exact published leaf families:**
- existence and standardness of general contact lines
- corrected smooth Legendrian variety of directions
- spanning of contact directions
- dimension of fibers of a finite-type morphism
- geometric integrality/dimension of products over an algebraically closed field

**Gate.** All five project wrappers compile; the exact published contact results are quarantined and precisely cited.

**Assigned declarations:**
- `LeBrunSalamon.StandardInputs.finiteType_nondominant_positiveFiber`
- `LeBrunSalamon.StandardInputs.finiteType_tensorProduct_geometry`
- `LeBrunSalamon.Construction.Lines.PublishedDirections.StandardInputs.general_selectedDirections_span`
- `LeBrunSalamon.Construction.Lines.PublishedDirections.StandardInputs.general_legendrianDirections`
- `LeBrunSalamon.PhaseThirtyTwo.primitiveContactFano_hasFreeContactLine`

### 3n — Automorphism groups, adjoint varieties and twistor/Wolf recovery

**Depends on:** 3a, 3e, 3m

**Scope:** 9 declarations; 1 are deletion candidates from 3a; expected retained count after successful liveness deletion: 8.

**Goal.** Prove the final classical-reduction wrappers from exact published classification and Riemannian inputs.

**Method.** Use exact leaves for the neutral contact automorphism group, KPSW/Mori alternatives, homogeneous contact/Wolf classification, minimal nilpotent orbit facts, positive twistor construction and metric recovery. Prove all normalization, polarization, action, homothety and project-type translations in Lean.

**Candidate exact published leaf families:**
- contact automorphism group and Hamiltonian correspondence
- KPSW/Mori/Kobayashi–Ochiai classification inputs
- Wolf/Boothby/Beauville homogeneous contact classification
- minimal nilpotent orbit and Jacobson–Morozov facts
- LeBrun–Salamon twistor construction and metric recovery
- parallel curvature under global symmetries and homothety

**Gate.** All nine wrappers compile and the Step 2 theorem conclusion is reached without importing the conjecture itself.

**Assigned declarations:**
- `LeBrunSalamon.ClassicalActions.StandardInputs.contactAutomorphismGroup_localOrbits`
- `LeBrunSalamon.ClassicalReduction.StandardInputs.nonprimitive_contactLine_embedding`
- `LeBrunSalamon.ClassicalReduction.StandardInputs.homogeneous_contact_adjointPresentation`
- `LeBrunSalamon.ClassicalReduction.StandardInputs.positiveQK_twistorReduction`
- `minimalNilpotent_exists` *(delete-test in 3a)*
- `nilpotent_hasEulerLift`
- `adjointRank_even`
- `globalSymmetries_parallelCurvature`
- `homothety_parallelCurvature`

### 3o — Final Step 3 certification

**Depends on:** 3a, 3b, 3c, 3d, 3e, 3f, 3g, 3h, 3i, 3j, 3k, 3l, 3m, 3n

**Scope:** 0 declarations; 0 are deletion candidates from 3a; expected retained count after successful liveness deletion: 0.

**Goal.** Freeze the exact published-input boundary and certify the entire strict tree.

**Method.** Regenerate the allowlist from exact leaf records, scan source tokens, clean-build every module in topological order, run native transitive `sorryAx` dependency analysis, and compare the result with the allowlist. Recheck the frozen Step 2 statement hash.

**Gate.** Every source admission and every transitive `sorryAx` dependency belongs to a precisely cited exact published theorem; no wrapper, corollary, transport, project application, custom axiom, `admit` or `opaque` remains.

## Step 3a deletion candidates

These are candidates only; the previous checkpoint did **not** run the deletion compile test. Each must be removed separately and its module plus reverse-dependency cone rebuilt. If deletion fails, it returns to its primary proof batch above.

- `proper_flat_connectedReduced_globalFunctions` → proof batch 3j
- `cotangent_openRestriction` → proof batch 3b
- `symmetricSheaf_locallyFree` → proof batch 3b
- `symmetricSheaf_pullback` → proof batch 3b
- `ample_tensor` → proof batch 3e
- `ample_closedPullback` → proof batch 3e
- `ample_affineBasis` → proof batch 3e
- `ample_eventualGlobalGeneration` → proof batch 3e
- `firstPrincipalParts_exact` → proof batch 3e
- `principalParts_locallyFree` → proof batch 3e
- `principalParts_higher_exact` → proof batch 3e
- `nodeAlgebra_integrallyClosed` → proof batch 3f
- `smooth_cotangent_transitivity_shortExact` → proof batch 3h
- `etale_cotangentMap_isIso` → proof batch 3h
- `closedImmersion_cotangentMap_epi` → proof batch 3h
- `LeBrunSalamon.PhaseThirtyTwo.splitting_unique_upToPermutation` → proof batch 3g
- `LeBrunSalamon.PhaseThirtyTwo.ample_positiveDegreeOnCurve` → proof batch 3g
- `minimalNilpotent_exists` → proof batch 3n
- `_root_.LeBrunSalamon.StandardInputs.homOpen_twoPointEvaluation_dominant` → proof batch 3i
- `Descent.genericDegree_existsUnique` → proof batch 3k
- `Descent.genericDegree_positive` → proof batch 3k
- `Descent.ramificationIndex_existsUnique` → proof batch 3k
- `LeBrunSalamon.PhaseThirtyTwo.projectiveTwist_ample_iff` → proof batch 3g
- `LeBrunSalamon.Project.stageDescription` → proof batch 3a

## Agent-hour discipline

A substep is accepted only with a source diff, exact-leaf ledger changes, module build log, reverse-dependency build log, and boundary-check output. If a batch exposes a genuinely new missing theorem, the agent must isolate it as a new exact leaf or split the batch; it must not weaken hypotheses, strengthen assumptions, introduce a project-specific `sorry`, or silently delete an exported declaration.
