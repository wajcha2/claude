# Step 3c and Step 3d: theorem, source, hypothesis, and map ledger

Audit date: 3 November 2026. This ledger treats the original seventeen obligations as proof obligations. An alias in `PublishedInputs` does not discharge a composite. Source eligibility and kernel acceptance are separate. Two current leaves have a direct mathematical source match: arbitrary cotangent base change and the affine ring-pullback pushout theorem. Neither is counted as fully accepted here without its current source and dependency receipt. No new false statement was found among these seventeen.

The new second-diagonal helper is written without admissions in `lebrun_takeover/published_leaf_work/LSSecondDiagonalAlgebra.lean`. It is deliberately outside `continuation/source` until its pinned-compiler replay succeeds, because the build planner scans every source module. It is not yet accepted.

## Obligations

### 3c-1 — LeBrunSalamon.PhaseTwentyEight.externalSection_finiteSum

- **Current source:** `source/RecompileBasePart05C.lean`.
- **Current admitted boundary:** `LeBrunSalamon.PublishedInputs.ExternalTensorDiagonal.kunneth_degreeZero_surjective`.
- **Status:** `composite_admission`.
- **Primary source:** [Stacks Lemma 33.29.1, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED).
- **Hypotheses:** A field; quasi-compact schemes with affine diagonal; quasi-coherent sheaves. SmoothProperComplexVariety and line bundles meet stronger conditions, but the specialization must be supplied.
- **Actual map:** Finite sums of externalProductSection, which is the tensor pairing of actual pullSection maps.
- **Remaining gap:** The published theorem concerns the canonical tensor-product map. This leaf already concludes a Fin-indexed sum and does not construct the tensor-to-finite-sum conversion.
- **Next proof:** Isolate the canonical n=0 Künneth isomorphism for generic quasi-coherent sheaves. Derive surjectivity, extract a tensor, and prove a finite simple-tensor expansion; normalize with sectionValue and externalProductSection.

### 3c-2 — LeBrunSalamon.PhaseTwentyEight.locallyFree_sections_descend

- **Current source:** `source/RecompileBasePart05C.lean`.
- **Current admitted boundary:** `LeBrunSalamon.PublishedInputs.ExternalTensorDiagonal.projectionFormula_sections_bijective`.
- **Status:** `composite_admission`.
- **Primary source:** [Stacks Lemma 20.54.2, Tag 01E8 (01E6 is the section)](https://stacks.math.columbia.edu/tag/01E8).
- **Hypotheses:** Arbitrary morphism of ringed spaces; finite locally free E. The project additionally assumes the canonical O→f_*O is invertible.
- **Actual map:** pullSection f; its adjoint is normalized by the existing pullSection_adjoint proof.
- **Remaining gap:** The cited projection formula gives a sheaf isomorphism E⊗f_*F→f_*(f*E⊗F). Specialization F=O, tensor-unit transports, use of O≅f_*O, and global-section/adjunction bijectivity remain inside the admission.
- **Next proof:** Admit only the canonical projection-formula map's invertibility, then prove the unit and Hom/adjunction transports.

### 3c-3 — LeBrunSalamon.PhaseTwentyEight.nonvanishingOpen_pullback

- **Current source:** `source/RecompileBasePart07.lean`.
- **Current admitted boundary:** `LeBrunSalamon.PublishedInputs.ExternalTensorDiagonal.nonvanishingOpen_pullback`.
- **Status:** `source_match_with_definition_bridge_pending`.
- **Primary source:** [Stacks Remark 17.25.11, Tag 0H78; nonvanishing locus defined in Lemma17.25.10, Tag01CY](https://stacks.math.columbia.edu/tag/0H78).
- **Hypotheses:** Morphism of locally ringed spaces and invertible sheaf. Scheme morphisms and the supplied line satisfy these assumptions.
- **Actual map:** The project nonvanishingOpen is the supremum of opens where the actual pulled section is an isomorphism. pullSection uses the canonical unit pullback isomorphism.
- **Remaining gap:** The published equality is exactly the intended mathematical assertion. The current name is an alias and the source defines the locus by a stalk/residue nonvanishing condition; certify equivalence with the supremum definition, rather than relying only on the namespace.
- **Next proof:** Prove the locus definition matches the source and then specialize a generic locally-ringed-space nonvanishing pullback leaf, or prove directly by local rank-one coefficients.

### 3c-4 — LeBrunSalamon.Core.ExternalTensorCoordinates.globalTensorMap_injective

- **Current source:** `source/RecompileExtensionsPart01.lean`.
- **Current admitted boundary:** `LeBrunSalamon.PublishedInputs.ExternalTensorDiagonal.kunneth_degreeZero_injective`.
- **Status:** `specialization_admission`.
- **Primary source:** [Stacks Lemma33.29.1, Tag0BED](https://stacks.math.columbia.edu/tag/0BED).
- **Hypotheses:** Quasi-compactness, affine diagonal, quasi-coherence; current proper complex line-bundle input is stronger.
- **Actual map:** globalTensorMap is TensorProduct.lift of actual pullback and tensor pairing; globalTensorMap_tmul already proves the external-product normalization.
- **Remaining gap:** The map is well normalized. The current sorry isolates only injectivity at the project input type, rather than applying an independently stated generic Künneth isomorphism.
- **Next proof:** Use the same canonical generic Künneth input as3c-1 and prove its project specialization and injective projection.

### 3c-5 — LeBrunSalamon.Core.ExternalTensorCoordinates.diagonalRestriction_iff_quotientCoefficients

- **Current source:** `source/RecompileExtensionsPart01.lean`.
- **Current admitted boundary:** `LeBrunSalamon.PublishedInputs.ExternalTensorDiagonal.diagonalRestriction_iff_quotientCoefficients`.
- **Status:** `composite_admission`.
- **Primary source:** [No single cited theorem has this conclusion; intended ingredients are affine closed immersions, sheaf restriction, and Spec tensor-product pullbacks.](https://stacks.math.columbia.edu/tag/01I9).
- **Hypotheses:** Separated structure map (essential), invertible sheaf, every affine line frame, every k including0.
- **Actual map:** Left: actual restriction of sectionFromValue(globalTensorMap t) to V(ker Δ)^k. Right: coefficientTensorMap t in (Γ(U)⊗ℂΓ(U))/ker(μ)^k.
- **Remaining gap:** Must construct U×U as the actual open in the fiber square, identify its ring and diagonal kernel with μ, transport the chosen line frame through both pullbacks and tensor pairing, and prove these opens cover the support of the thickened diagonal. k=0 is a separate empty-subscheme case.
- **Next proof:** Prove the generic affine ideal-power quotient map and support lemmas, then the frame/coefficient naturality and local-to-global zero criterion. Do not admit this entire equivalence under a new name.

### 3c-6 — LeBrunSalamon.Core.ExternalTensorCoordinates.smooth_diagonal_square_detected

- **Current source:** `source/RecompileExtensionsPart01.lean`.
- **Current admitted boundary:** `LeBrunSalamon.PublishedInputs.ExternalTensorDiagonal.smooth_diagonal_secondDerivatives_detect`.
- **Status:** `proof_candidate_uncompiled`.
- **Primary source:** [No new literature input needed: pinned Mathlib KaehlerDifferential=I.Cotangent, Module.Finite.exists_comp_eq_id_of_projective, Algebra.FormallySmooth.projective_kaehlerDifferential.](https://github.com/leanprover-community/mathlib4/blob/116662aa4c1e9106ab5c609b3214b02f6e11a65a/Mathlib/RingTheory/Kaehler/Basic.lean).
- **Hypotheses:** CommRing A, complex algebra, smoothness; the proof actually only needs finite projectivity of Ω and invertible2.
- **Actual map:** second/rightDerivation in the new helper have the same tensor-generator formula a⊗b↦a·D(E(b)) as the project tensorSecond.
- **Remaining gap:** New helper code is written without sorry, but has not passed the pinned compiler and has not been imported into the live graph.
- **Next proof:** Compile LSSecondDiagonalAlgebra; prove the definitional/canonical map equality; replace the detector's direct sorry with the new theorem. Replay the affected cone.

### 3d-1 — LeBrunSalamon.StandardInputs.cotangentPullback_isIso

- **Current source:** `source/LSNodalFixedEnds.lean`.
- **Current admitted boundary:** `LeBrunSalamon.PublishedInputs.BaseChangeFibers.cotangentPullback_isIso`.
- **Status:** `mathematical_source_match`.
- **Primary source:** [Stacks Lemma29.33.10, Tag01V0](https://stacks.math.columbia.edu/tag/01V0).
- **Hypotheses:** Arbitrary scheme morphisms f:Y→S and g:T→S; no smoothness or flatness assumption.
- **Actual map:** CotangentBaseChange.canonicalMap is cotangentMap, the pullback-square equality transport, then cotangentToRelative. canonicalMap_differential proves p*(da)↦d(p*a).
- **Remaining gap:** No mathematical mismatch found. The map normalization is explicitly proved. Final acceptance still requires the current-source dependency receipt and boundary-checker treatment of this generic cotangent leaf.
- **Next proof:** Retain as a source-eligible generic published input with the canonicalMap_differential mapping receipt; do not demand unnecessary smoothness.

### 3d-2 — LeBrunSalamon.Skeleton.dualBaseChange_isIso

- **Current source:** `source/RecompileExtensionsPart01.lean`.
- **Current admitted boundary:** `LeBrunSalamon.PublishedInputs.BaseChangeFibers.dualBaseChange_isIso`.
- **Status:** `generic_fact_source_bridge_pending`.
- **Primary source:** [Stacks Example17.18.1, section0FNU; Lemma49.2.10 Tag0BVF only mentions module dual base change inside a proof.](https://stacks.math.columbia.edu/tag/0FNU).
- **Hypotheses:** Arbitrary scheme morphism, finite locally free source E. These are the correct hypotheses.
- **Actual map:** dualBaseChange is curry of the pulled evaluation pairing postcomposed with the canonical unitPullbackMap.
- **Remaining gap:** The cited0BVF theorem is about dualizing modules of quasi-finite flat ring maps, not this sheaf map. The mathematical dual-base-change fact is standard, but the one-to-one source and generic-to-project map translation are not yet supplied.
- **Next proof:** Prove from evaluation, finite-local-free duality, and tensor pullback, or derive as the F=O specialization of a proved canonical Hom base-change theorem.

### 3d-3 — LeBrunSalamon.Construction.fiber_dimension

- **Current source:** `source/RecompileExtensionsPart02.lean`.
- **Current admitted boundary:** `LeBrunSalamon.PublishedInputs.BaseChangeFibers.fiber_rank_and_finite`.
- **Status:** `composite_admission`.
- **Primary source:** [Cited Stacks17.14.4, Tag01C9, establishes local constancy of rank, not this fiber dimension identity.](https://stacks.math.columbia.edu/tag/01C9).
- **Hypotheses:** E has constant finite locally free rank r; x:Specℂ→X need not be assumed closed for this calculation.
- **Actual map:** Fiber E x is global sections of actual pullback x*E, with ℂ action through ΓSpecIso and the identity structure map.
- **Remaining gap:** Need a linear equivalence Fiber E x≃ℂ^r from a local frame and pullback of free modules, including the Γ(Specℂ) scalar normalization.
- **Next proof:** Construct that equivalence once and derive finrank and finite-dimensionality without any new admission.

### 3d-4 — LeBrunSalamon.Construction.fiber_finite

- **Current source:** `source/RecompileExtensionsPart02.lean`.
- **Current admitted boundary:** `LeBrunSalamon.PublishedInputs.BaseChangeFibers.fiber_rank_and_finite`.
- **Status:** `composite_admission`.
- **Primary source:** [Same issue as3d-3; no separate published result is required after the explicit fiber equivalence.](https://stacks.math.columbia.edu/tag/01C9).
- **Hypotheses:** Finite locally free rank r; arbitrary complex-valued point.
- **Actual map:** Same actual Fiber as3d-3.
- **Remaining gap:** Conjunction projection from the same directly admitted composite.
- **Next proof:** Derive Module.Finite from the explicit fiber linear equivalence to Fin r→ℂ.

### 3d-5 — LeBrunSalamon.Construction.vectorBundle_fiber_exact

- **Current source:** `source/RecompileExtensionsPart02.lean`.
- **Current admitted boundary:** `LeBrunSalamon.PublishedInputs.BaseChangeFibers.vectorBundle_fiber_exact`.
- **Status:** `composite_admission`.
- **Primary source:** [Stacks10.39.12 Tag00HL is ring-module tensor exactness with flat quotient; Stacks18.39.4 Tag0G6R gives the sheaf pullback version.](https://stacks.math.columbia.edu/tag/0G6R).
- **Hypotheses:** Actual short exact sequence; the quotient G is finite locally free hence flat. No flatness of the point map is needed.
- **Actual map:** fiberMap i x and fiberMap q x are onCSections of the actual pullback functor maps.
- **Remaining gap:** Requires pullback short exactness, exact global sections on Specℂ, and translation from categorical exactness/mono/epi to range=kernel/injective/surjective. All are currently bundled.
- **Next proof:** Derive from3d-6 or its generic flat-quotient input and prove the one-point/global-section exactness conversion.

### 3d-6 — LeBrunSalamon.Construction.StandardInputs.BundleGeometry.vectorBundle_pullback_shortExact

- **Current source:** `source/RecompileExtensionsPart03.lean`.
- **Current admitted boundary:** `LeBrunSalamon.PublishedInputs.BaseChangeFibers.vectorBundle_pullback_shortExact`.
- **Status:** `source_found_specialization_pending`.
- **Primary source:** [Stacks Lemma18.39.4, Tag0G6R (05VA is only the section); the exact generic statement uses a flat quotient.](https://stacks.math.columbia.edu/tag/0G6R).
- **Hypotheses:** Any morphism of ringed topoi and short exact sequence with flat quotient. Locally free G is sufficient, but that implication belongs in the wrapper.
- **Actual map:** ShortComplex.map (Scheme.Modules.pullback f), retaining i and q.
- **Remaining gap:** The current leaf is a finite-vector-bundle specialization. Isolate generic flat-quotient pullback exactness and prove local freeness implies the required flatness, or prove locally split exactness directly.
- **Next proof:** Use the exact0G6R input with a suitable generic flat sheaf predicate and a real finite-free local proof of its hypothesis.

### 3d-7 — LeBrunSalamon.Construction.StandardInputs.BundleGeometry.homFiberEvaluation_injective_of_locallyFree

- **Current source:** `source/RecompileExtensionsPart03.lean`.
- **Current admitted boundary:** `LeBrunSalamon.PublishedInputs.BaseChangeFibers.homFiberEvaluation_injective`.
- **Status:** `citation_mismatch_composite_admission`.
- **Primary source:** [Stacks Lemma17.22.4, Tag01CP, is a comparison with Hom of stalks, not Hom of fibers.](https://stacks.math.columbia.edu/tag/01CP).
- **Hypotheses:** E finite locally free; F arbitrary. The stated project theorem is mathematically valid under these hypotheses.
- **Actual map:** homFiberEvaluation is the fiber pairing of actual sheafEvaluationPair; homFiberEvaluation_curry proves its normalization.
- **Remaining gap:** Tensoring a stalk injection with a residue field need not preserve injectivity. Finite local freeness must be used to identify the fiber comparison, not merely finite presentation or finite type.
- **Next proof:** Derive from the actual Hom base-change isomorphism3d-8 and the evaluation/section identification on Specℂ, then take injectivity.

### 3d-8 — LeBrunSalamon.Construction.StandardInputs.BundleGeometry.homBaseChange_isIso

- **Current source:** `source/RecompileExtensionsPart03.lean`.
- **Current admitted boundary:** `LeBrunSalamon.PublishedInputs.BaseChangeFibers.homBaseChange_isIso`.
- **Status:** `ring_to_sheaf_bridge_pending`.
- **Primary source:** [Stacks Lemma10.78.9, actual Tag0DVB (00NV is its section).](https://stacks.math.columbia.edu/tag/0DVB).
- **Hypotheses:** Published ring statement: finite projective M, arbitrary R-modules N,L. Project: finite locally free E, arbitrary target F, arbitrary scheme map.
- **Actual map:** homBaseChange is the curry of the pulled evaluation pairing; homBaseChange_curry is proved.
- **Remaining gap:** Need scalar-extension adjunction Hom_R(M,N⊗S)≃Hom_S(S⊗M,S⊗N), local finite-free reduction, and sheaf gluing for this specific comparison. The ring source alone is not the sheaf theorem.
- **Next proof:** Prove locally using the actual finite-free sheaf trivializations and the normalization identity, or find an exact primary sheaf-level statement and prove the presentation transport.

### 3d-9 — LeBrunSalamon.Construction.Smoothing.CoordinateCharts.StandardInputs.spec_pullback_isPushout

- **Current source:** `source/RecompileExtensionsPart04Geometry.lean`.
- **Current admitted boundary:** `LeBrunSalamon.PublishedInputs.BaseChangeFibers.spec_pullback_isPushout`.
- **Status:** `mathematical_source_match`.
- **Primary source:** [Stacks Lemma37.14.1, Tag0ET0](https://stacks.math.columbia.edu/tag/0ET0).
- **Hypotheses:** Ring maps A→C and B→C; A→C surjective. No surjectivity of the second map or field/Noetherian hypotheses are required.
- **Actual map:** Spec.map f and g; cocone maps are Spec.map of the actual categorical pullback projections.
- **Remaining gap:** No mathematical mismatch found. The theorem explicitly states pushout in schemes, not only in affine schemes. Current code uses this exact category and map orientation.
- **Next proof:** Retain as an exact generic published input; attach current Geometry replay and canonical pullback universal-property representation.

### 3d-10 — LeBrunSalamon.Construction.Smoothing.CoordinateCharts.StandardInputs.generating_sections_unitOpen

- **Current source:** `source/RecompileExtensionsPart04Geometry.lean`.
- **Current admitted boundary:** `LeBrunSalamon.PublishedInputs.BaseChangeFibers.generating_sections_unitOpen`.
- **Status:** `composite_admission`.
- **Primary source:** [Stacks17.25.10 Tag01CY and17.25.11 Tag0H78 supply individual unit loci and pullback behavior.](https://stacks.math.columbia.edu/tag/01CY).
- **Hypotheses:** Generating finite tuple in a line bundle, encoded as Epi of Sigma.desc.
- **Actual map:** Every test morphism f:T→Y; actual pullSection f (a i) must be invertible exactly when the image lies in U i.
- **Remaining gap:** The covering assertion from the Epi tuple and the universal image-in-open iff are project composites. The section-unit locus itself is already defined elsewhere.
- **Next proof:** Choose U i=nonvanishingOpen L(a i), prove cover by local rank-one generation over local rings, and derive the image criterion from3c-3 and nonvanishingOpen_eq_top_iff.

### 3d-11 — LeBrunSalamon.Construction.Normalization.totalBundle_exists

- **Current source:** `source/RecompileExtensionsPart04Geometry.lean`.
- **Current admitted boundary:** `LeBrunSalamon.PublishedInputs.BaseChangeFibers.totalBundle_representation`.
- **Status:** `composite_admission`.
- **Primary source:** [Stacks Lemma27.4.3 Tag01LU represents algebra maps out of a quasi-coherent algebra; Section27.6 Tag01M1 defines V(E)=Spec Sym(E).](https://stacks.math.columbia.edu/tag/01LU).
- **Hypotheses:** Finite locally free E ensures quasi-coherence of its dual and finite biduality. The desired total space is Spec Sym(E∨), because it represents E-valued sections.
- **Actual map:** Pull back τ along h and apply the actual compositionPullback h projection f equality E.sheaf.
- **Remaining gap:** Replacing TotalBundle by an existential does not remove its composite content. Must prove symmetric-algebra universal property, dual/bidual section identification, and pullback naturality of the tautological section.
- **Next proof:** Admit only relative-Spec representation of algebra maps; construct the symmetric-dual algebra and prove the natural equivalence with sections before packaging TotalBundle.

## Acceptance rule

An obligation is accepted only after the source statement matches a single explicitly identified published theorem (or is proved without new admissions), all extra specialization/coordinate/adjunction steps are Lean proofs, the actual canonical maps are retained, and the changed declaration with its current ancestor graph has passed the pinned compiler. The direct-admission dependency closure must be recorded separately from the global presence of `sorryAx`.

