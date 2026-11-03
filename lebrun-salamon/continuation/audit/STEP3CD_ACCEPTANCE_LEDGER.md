# Step 3c–3d acceptance ledger

Seventeen original Step3c/3d obligations. Source and hypothesis audit is separate from kernel acceptance. No new false statement found in these seventeen; composite and citation mismatch statuses are not falsehood findings.

Three original obligations have native-checked proofs with no `sorryAx`: the smooth quadratic detector and the two fibre-rank conclusions. Three more have native-checked translations to exact generic published inputs: projection-formula descent and the two Künneth obligations. Their current containing modules and affected dependency cones still require fresh replay. The arbitrary chart-cover diagonal criterion also passed, but the full coefficient/quotient bridge is not complete. The nonvanishing candidate remains outside the live graph with two focused elaboration issues. Three other obligations have audited mathematical source matches (cotangent, dual base change and affine pushout), independently of the kernel gate.

| ID | Original theorem | Status | Primary source / proof | Remaining work |
|---|---|---|---|---|
| 3c-1 | `LeBrunSalamon.PhaseTwentyEight.externalSection_finiteSum` | native_proved_translation_to_audited_leaf_integrated_pending_public_replay | Stacks Lemma 33.29.1, Tag 0BED | Project specialization now has a proved body. The single generic canonical Kunneth leaf is exact Stacks0BED; current containing-module/reverse-cone replay and exhaustive native direct-leaf audit remain pending. |
| 3c-2 | `LeBrunSalamon.PhaseTwentyEight.locallyFree_sections_descend` | native_proved_translation_to_audited_leaf_integrated_pending_public_replay | Stacks Lemma 20.54.2, Tag 01E8 (01E6 is the section) | The helper passed native checking and its exhaustive dependency closure has exactly the audited generic01E8 leaf. The current Base05C transplantation and affected cone still require fresh replay. |
| 3c-3 | `LeBrunSalamon.PhaseTwentyEight.nonvanishingOpen_pullback` | source_match_with_definition_bridge_pending | Stacks Remark 17.25.11, Tag 0H78; nonvanishing locus defined in Lemma17.25.10, Tag01CY | The published equality is exactly the intended mathematical assertion. The current name is an alias and the source defines the locus by a stalk/residue nonvanishing condition; certify equivalence with the supremum definition, rather than relying only on the namespace. |
| 3c-4 | `LeBrunSalamon.Core.ExternalTensorCoordinates.globalTensorMap_injective` | native_proved_translation_to_audited_leaf_integrated_pending_public_replay | Stacks Lemma33.29.1, Tag0BED | Project specialization now has a proved body. The single generic canonical Kunneth leaf is exact Stacks0BED; current containing-module/reverse-cone replay and exhaustive native direct-leaf audit remain pending. |
| 3c-5 | `LeBrunSalamon.Core.ExternalTensorCoordinates.diagonalRestriction_iff_quotientCoefficients` | composite_admission | No single cited theorem has this conclusion; intended ingredients are affine closed immersions, sheaf restriction, and Spec tensor-product pullbacks. | Must construct U×U as the actual open in the fiber square, identify its ring and diagonal kernel with μ, transport the chosen line frame through both pullbacks and tensor pairing, and prove these opens cover the support of the thickened diagonal. k=0 is a separate empty-subscheme case. |
| 3c-6 | `LeBrunSalamon.Core.ExternalTensorCoordinates.smooth_diagonal_square_detected` | native_no_admission_proof_integrated_pending_public_replay | No new literature input needed: pinned Mathlib KaehlerDifferential=I.Cotangent, Module.Finite.exists_comp_eq_id_of_projective, Algebra.FormallySmooth.projective_kaehlerDifferential. | Generic helper and exact project signature passed the pinned native compiler; the main Ext01 transplant awaits fresh public-module replay. |
| 3d-1 | `LeBrunSalamon.StandardInputs.cotangentPullback_isIso` | mathematical_source_match | Stacks Lemma29.33.10, Tag01V0 | No mathematical mismatch found. The map normalization is explicitly proved. Final acceptance still requires the current-source dependency receipt and boundary-checker treatment of this generic cotangent leaf. |
| 3d-2 | `LeBrunSalamon.Skeleton.dualBaseChange_isIso` | mathematical_source_match | Grothendieck, EGA I (1960), chapitre 0, (5.4.5); canonical comparison defined in (4.4.6), finite-rank convention in (5.4.1). DOI10.1007/BF02684778. | The original French scan indexed paragraph0(5.4.5) explicitly states this dual-pullback map is bijective. The earlier0BVF citation was not exact and has been replaced. No mathematical mismatch remains; final acceptance still requires current-source replay and dependency boundary receipt. |
| 3d-3 | `LeBrunSalamon.Construction.fiber_dimension` | native_no_admission_proof_integrated_pending_public_replay | Cited Stacks17.14.4, Tag01C9, establishes local constancy of rank, not this fiber dimension identity. | Explicit free-frame/scalar-normalized fibre proof passed native checking with no sorryAx. Its Ext02 transplantation awaits fresh public-module replay. |
| 3d-4 | `LeBrunSalamon.Construction.fiber_finite` | native_no_admission_proof_integrated_pending_public_replay | Same issue as3d-3; no separate published result is required after the explicit fiber equivalence. | Explicit free-frame/scalar-normalized fibre proof passed native checking with no sorryAx. Its Ext02 transplantation awaits fresh public-module replay. |
| 3d-5 | `LeBrunSalamon.Construction.vectorBundle_fiber_exact` | composite_admission | Stacks10.39.12 Tag00HL is ring-module tensor exactness with flat quotient; Stacks18.39.4 Tag0G6R gives the sheaf pullback version. | Requires pullback short exactness, exact global sections on Specℂ, and translation from categorical exactness/mono/epi to range=kernel/injective/surjective. All are currently bundled. |
| 3d-6 | `LeBrunSalamon.Construction.StandardInputs.BundleGeometry.vectorBundle_pullback_shortExact` | source_found_specialization_pending | Stacks Lemma18.39.4, Tag0G6R (05VA is only the section); the exact generic statement uses a flat quotient. | The current leaf is a finite-vector-bundle specialization. Isolate generic flat-quotient pullback exactness and prove local freeness implies the required flatness, or prove locally split exactness directly. |
| 3d-7 | `LeBrunSalamon.Construction.StandardInputs.BundleGeometry.homFiberEvaluation_injective_of_locallyFree` | citation_mismatch_composite_admission | Stacks Lemma17.22.4, Tag01CP, is a comparison with Hom of stalks, not Hom of fibers. | Tensoring a stalk injection with a residue field need not preserve injectivity. Finite local freeness must be used to identify the fiber comparison, not merely finite presentation or finite type. |
| 3d-8 | `LeBrunSalamon.Construction.StandardInputs.BundleGeometry.homBaseChange_isIso` | ring_to_sheaf_bridge_pending | Stacks Lemma10.78.9, actual Tag0DVB (00NV is its section). | Need scalar-extension adjunction Hom_R(M,N⊗S)≃Hom_S(S⊗M,S⊗N), local finite-free reduction, and sheaf gluing for this specific comparison. The ring source alone is not the sheaf theorem. |
| 3d-9 | `LeBrunSalamon.Construction.Smoothing.CoordinateCharts.StandardInputs.spec_pullback_isPushout` | mathematical_source_match | Stacks Lemma37.14.1, Tag0ET0 | No mathematical mismatch found. The theorem explicitly states pushout in schemes, not only in affine schemes. Current code uses this exact category and map orientation. |
| 3d-10 | `LeBrunSalamon.Construction.Smoothing.CoordinateCharts.StandardInputs.generating_sections_unitOpen` | composite_admission | Stacks17.25.10 Tag01CY and17.25.11 Tag0H78 supply individual unit loci and pullback behavior. | The covering assertion from the Epi tuple and the universal image-in-open iff are project composites. The section-unit locus itself is already defined elsewhere. |
| 3d-11 | `LeBrunSalamon.Construction.Normalization.totalBundle_exists` | composite_admission | Stacks Lemma27.4.3 Tag01LU represents algebra maps out of a quasi-coherent algebra; Section27.6 Tag01M1 defines V(E)=Spec Sym(E). | Replacing TotalBundle by an existential does not remove its composite content. Must prove symmetric-algebra universal property, dual/bidual section identification, and pullback naturality of the tautological section. |

## Hypotheses, maps and next actions

### 3c-1 — LeBrunSalamon.PhaseTwentyEight.externalSection_finiteSum

**Hypotheses.** Generic leaf: any field, quasi-compact separated schemes, arbitrary quasi-coherent modules. The proof derives compactness from properness and quasi-coherence from actual finite local frames.

**Actual map.** The generic map is TensorProduct.lift of actual pullSection and tensorPresentation pairing. globalTensorMap_eq_kunneth is proved by rfl; finite pure-tensor expansion is proved using the spanning theorem.

**Next action.** Recompile current Base05C and ExtensionsPart01, then their affected cone. Verify the final transitive boundary contains the exact generic Kunneth input and no historical Kunneth composite.

Source: https://stacks.math.columbia.edu/tag/0BED

**Candidate/native status.** Native pass against frozen exact CI41685948946 ancestors. Source byte hashes match; current public modules and native transitive direct-leaf closure still need replay.

**Evidence.** audit/step3cd_kunneth_cover_build/

### 3c-2 — LeBrunSalamon.PhaseTwentyEight.locallyFree_sections_descend

**Hypotheses.** Arbitrary scheme morphism f and arbitrary F; E has local free generators indexed by finite sets. The section wrapper proves finite local freeness from the given constant-rank bundle and supplies IsIso(O→f_*O).

**Actual map.** projectionPair sends e⊗z to f*e⊗z on every inverse-image open; canonicalMap_pair proves this formula. unit_comparison identifies its unit specialization with the actual adjunction unit; sections_bijective proves the final pullSection map.

**Next action.** Recompile current Base05C and reverse cone; retain canonicalMap_isIso as the literal generic published input.

Source: https://stacks.math.columbia.edu/tag/01E8

**Evidence.** audit/step3cd_projection_build/

### 3c-3 — LeBrunSalamon.PhaseTwentyEight.nonvanishingOpen_pullback

**Hypotheses.** Morphism of locally ringed spaces and invertible sheaf. Scheme morphisms and the supplied line satisfy these assumptions.

**Actual map.** The project nonvanishingOpen is the supremum of opens where the actual pulled section is an isomorphism. pullSection uses the canonical unit pullback isomorphism.

**Next action.** Prove the locus definition matches the source and then specialize a generic locally-ringed-space nonvanishing pullback leaf, or prove directly by local rank-one coefficients.

Source: https://stacks.math.columbia.edu/tag/0H78

**Candidate/native status.** Zero-direct-admission candidate has only two remaining native elaboration issues: unit-coefficient composition normalization and an iff-composition timeout. Last failed source/logs preserved; candidate remains outside live source.

**Evidence.** audit/step3cd_kunneth_cover_build/pending_nonvanishing/

### 3c-4 — LeBrunSalamon.Core.ExternalTensorCoordinates.globalTensorMap_injective

**Hypotheses.** Generic leaf: any field, quasi-compact separated schemes, arbitrary quasi-coherent modules. The proof derives compactness from properness and quasi-coherence from actual finite local frames.

**Actual map.** The generic map is TensorProduct.lift of actual pullSection and tensorPresentation pairing. globalTensorMap_eq_kunneth is proved by rfl; finite pure-tensor expansion is proved using the spanning theorem.

**Next action.** Recompile current Base05C and ExtensionsPart01, then their affected cone. Verify the final transitive boundary contains the exact generic Kunneth input and no historical Kunneth composite.

Source: https://stacks.math.columbia.edu/tag/0BED

**Candidate/native status.** Native pass against frozen exact CI41685948946 ancestors. Source byte hashes match; current public modules and native transitive direct-leaf closure still need replay.

**Evidence.** audit/step3cd_kunneth_cover_build/

### 3c-5 — LeBrunSalamon.Core.ExternalTensorCoordinates.diagonalRestriction_iff_quotientCoefficients

**Hypotheses.** Separated structure map (essential), invertible sheaf, every affine line frame, every k including0.

**Actual map.** Left: actual restriction of sectionFromValue(globalTensorMap t) to V(ker Δ)^k. Right: coefficientTensorMap t in (Γ(U)⊗ℂΓ(U))/ker(μ)^k.

**Next action.** Prove the generic affine ideal-power quotient map and support lemmas, then the frame/coefficient naturality and local-to-global zero criterion. Do not admit this entire equivalence under a new name.

Source: https://stacks.math.columbia.edu/tag/01I9

**Partial proof.** Generic ideal-power quotient map previously checked. New SectionCoverProof.vanishes_iff_squareCover now passed native checking and is integrated: any supplied covering family suffices, including the two P1 charts. Actual affine product ring/frame-to-coefficient comparison remains open.

**Evidence.** audit/step3cd_kunneth_cover_build/

### 3c-6 — LeBrunSalamon.Core.ExternalTensorCoordinates.smooth_diagonal_square_detected

**Hypotheses.** CommRing A, complex algebra, smoothness; the proof actually only needs finite projectivity of Ω and invertible2.

**Actual map.** Live tensorSecond_eq_secondDiagonal proves equality with SecondDiagonalAlgebra.second by rfl; the project-signature detector was natively checked.

**Next action.** Run current Ext01 and its affected cone; preserve the no-sorry native axiom receipt.

Source: https://github.com/leanprover-community/mathlib4/blob/116662aa4c1e9106ab5c609b3214b02f6e11a65a/Mathlib/RingTheory/Kaehler/Basic.lean

**Evidence.** audit/step3cd_build/

### 3d-1 — LeBrunSalamon.StandardInputs.cotangentPullback_isIso

**Hypotheses.** Arbitrary scheme morphisms f:Y→S and g:T→S; no smoothness or flatness assumption.

**Actual map.** CotangentBaseChange.canonicalMap is cotangentMap, the pullback-square equality transport, then cotangentToRelative. canonicalMap_differential proves p*(da)↦d(p*a).

**Next action.** Retain as a source-eligible generic published input with the canonicalMap_differential mapping receipt; do not demand unnecessary smoothness.

Source: https://stacks.math.columbia.edu/tag/01V0

### 3d-2 — LeBrunSalamon.Skeleton.dualBaseChange_isIso

**Hypotheses.** Arbitrary morphism of ringed spaces; locally free sheaf of finite rank. The project restricts to schemes and constant finite rank, so no extra geometric premise is needed.

**Actual map.** dualBaseChange is curry of pulled evaluation followed by unitPullbackMap. The proved dualBaseChange_pullLocalSection gives f*(lambda)(f*e)=f*(lambda(e)) on every local pair, identifying the precise canonical map of EGA0(4.4.6).

**Next action.** Retain this existing generic theorem as the exact published EGA0(5.4.5) input; replay current Ext01 and audit its normalized-map declaration closure.

Source: https://numdam.org/item/PMIHES_1960__4__5_0/

### 3d-3 — LeBrunSalamon.Construction.fiber_dimension

**Hypotheses.** E has constant finite locally free rank r; x:Specℂ→X need not be assumed closed for this calculation.

**Actual map.** Fiber E x is global sections of actual pullback x*E, with ℂ action through ΓSpecIso and the identity structure map.

**Next action.** Run current Ext02 and affected cone. No pullback_locallyFree or old fibre-rank admission is used.

Source: https://stacks.math.columbia.edu/tag/01C9

**Evidence.** audit/step3cd_build/

### 3d-4 — LeBrunSalamon.Construction.fiber_finite

**Hypotheses.** Finite locally free rank r; arbitrary complex-valued point.

**Actual map.** Same actual Fiber as3d-3.

**Next action.** Run current Ext02 and affected cone. No pullback_locallyFree or old fibre-rank admission is used.

Source: https://stacks.math.columbia.edu/tag/01C9

**Evidence.** audit/step3cd_build/

### 3d-5 — LeBrunSalamon.Construction.vectorBundle_fiber_exact

**Hypotheses.** Actual short exact sequence; the quotient G is finite locally free hence flat. No flatness of the point map is needed.

**Actual map.** fiberMap i x and fiberMap q x are onCSections of the actual pullback functor maps.

**Next action.** Derive from3d-6 or its generic flat-quotient input and prove the one-point/global-section exactness conversion.

Source: https://stacks.math.columbia.edu/tag/0G6R

### 3d-6 — LeBrunSalamon.Construction.StandardInputs.BundleGeometry.vectorBundle_pullback_shortExact

**Hypotheses.** Any morphism of ringed topoi and short exact sequence with flat quotient. Locally free G is sufficient, but that implication belongs in the wrapper.

**Actual map.** ShortComplex.map (Scheme.Modules.pullback f), retaining i and q.

**Next action.** Use the exact0G6R input with a suitable generic flat sheaf predicate and a real finite-free local proof of its hypothesis.

Source: https://stacks.math.columbia.edu/tag/0G6R

### 3d-7 — LeBrunSalamon.Construction.StandardInputs.BundleGeometry.homFiberEvaluation_injective_of_locallyFree

**Hypotheses.** E finite locally free; F arbitrary. The stated project theorem is mathematically valid under these hypotheses.

**Actual map.** homFiberEvaluation is the fiber pairing of actual sheafEvaluationPair; homFiberEvaluation_curry proves its normalization.

**Next action.** Derive from the actual Hom base-change isomorphism3d-8 and the evaluation/section identification on Specℂ, then take injectivity.

Source: https://stacks.math.columbia.edu/tag/01CP

### 3d-8 — LeBrunSalamon.Construction.StandardInputs.BundleGeometry.homBaseChange_isIso

**Hypotheses.** Published ring statement: finite projective M, arbitrary R-modules N,L. Project: finite locally free E, arbitrary target F, arbitrary scheme map.

**Actual map.** homBaseChange is the curry of the pulled evaluation pairing; homBaseChange_curry is proved.

**Next action.** Prove locally using the actual finite-free sheaf trivializations and the normalization identity, or find an exact primary sheaf-level statement and prove the presentation transport.

Source: https://stacks.math.columbia.edu/tag/0DVB

### 3d-9 — LeBrunSalamon.Construction.Smoothing.CoordinateCharts.StandardInputs.spec_pullback_isPushout

**Hypotheses.** Ring maps A→C and B→C; A→C surjective. No surjectivity of the second map or field/Noetherian hypotheses are required.

**Actual map.** Spec.map f and g; cocone maps are Spec.map of the actual categorical pullback projections.

**Next action.** Retain as an exact generic published input; attach current Geometry replay and canonical pullback universal-property representation.

Source: https://stacks.math.columbia.edu/tag/0ET0

### 3d-10 — LeBrunSalamon.Construction.Smoothing.CoordinateCharts.StandardInputs.generating_sections_unitOpen

**Hypotheses.** Generating finite tuple in a line bundle, encoded as Epi of Sigma.desc.

**Actual map.** Every test morphism f:T→Y; actual pullSection f (a i) must be invertible exactly when the image lies in U i.

**Next action.** Choose U i=nonvanishingOpen L(a i), prove cover by local rank-one generation over local rings, and derive the image criterion from3c-3 and nonvanishingOpen_eq_top_iff.

Source: https://stacks.math.columbia.edu/tag/01CY

### 3d-11 — LeBrunSalamon.Construction.Normalization.totalBundle_exists

**Hypotheses.** Finite locally free E ensures quasi-coherence of its dual and finite biduality. The desired total space is Spec Sym(E∨), because it represents E-valued sections.

**Actual map.** Pull back τ along h and apply the actual compositionPullback h projection f equality E.sheaf.

**Next action.** Admit only relative-Spec representation of algebra maps; construct the symmetric-dual algebra and prove the natural equivalence with sections before packaging TotalBundle.

Source: https://stacks.math.columbia.edu/tag/01LU

