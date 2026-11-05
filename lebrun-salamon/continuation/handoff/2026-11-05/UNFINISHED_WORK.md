# Unfinished work: exact restart map

Prepared **5 November 2026** from accepted commit `11c18cdcb5e92e3975626a6a1276abfe419ad4f8`. This note records saved work; it adds no proof or acceptance credit.

## 1. The three states must stay separate

- **Accepted baseline:** 308 production modules, source manifest `e48fa8114d0a9eb29d6a8d67442af17a135f64e1160b5936792414b406551998`, compiled at `4d1aa547453f50736035a91f6fea81d340359143`. The ledger is **79/133**, with **42 original obligations +8 definition validations +4 final gates** pending. The unconditional frozen theorem is still open.
- **Completed isolated diagnostic proofs:** the source below has successful bounded local receipts and, where recorded, transitive admission audits. Some project imports came from the earlier verified Point1/local pool. These outputs are not current-308 native acceptance and do not remove an original admission.
- **Uncompiled integration proposal:** the proposed 311-module snapshot combines OBL-052, OBL-055 and OBL-057 changes. Its import graph and inverse guards were checked statically. It has not been compiled or selected as production.

The authoritative file list is [the deferred index](../../audit/deferred_next_steps_20261104/INDEX.json). In this note **D** means `audit/deferred_next_steps_20261104/`, relative to the continuation directory. All 126 indexed paths were matched against the pinned Git subtree; the index itself is the only additional file. Historical notes saying “74/133” or “audit pending” retain their earlier date and must be read with the later result/review groups.

## 2. Original obligations and the best next entry point

| Original ID | Saved progress and exact entry point | Still required |
|---|---|---|
| **049** `homOpen_sourceFirstJet_dominant`, `LSConicJets.lean` | The all-test Hom/deformation, marked-evaluation and section-interpolation infrastructure prepared for 052 is reusable. There is no saved complete 049 proof or integrated replacement. | Prove the actual first-jet evaluation/tangent comparison and its dominance statement with the original hypotheses. A two-point-evaluation proof is not a first-jet proof. |
| **050** `HomDegree.StandardInputs.degree_open` | D/`obl050051/design.md`; completed D/`fixed_degree_open_transport/source.lean` transfers a **supplied** degree stratum across the canonical presentation isomorphism. | Construct the canonical bounded stratum: an ample power of the **given** line, its actual hyperplane identification, the graph/twist Hilbert-polynomial comparison, and the required clopen, locally finite type and quasi-compact properties. Local constancy alone is insufficient. |
| **051** `Skeleton.homSpacePresentation_exists` | D/`early_hom_construction/` is the latest constructor organization; D/`hom_presentation_comparison/` proves uniqueness/comparison of supplied presentations. | Obtain a **scheme** representer with the actual evaluation on **all scheme tests**. The generic constructor consumes a representer; it does not establish its existence. Keep projectivity and early source-order prerequisites explicit. |
| **052** `homOpen_twoPointEvaluation_dominant` | D/`conditional_052_full/composition.lean` is the completed conditional composition; D/`criterion_specialization/source.lean` discharges its complex tangent criterion using the accepted 3h input. D/`obl052_integration_proposal/helper.lean` is the cleaned proposed `LSHomTwoPointDominance.lean`. | Review/register the proposed integrality inputs, apply the guarded seven-declaration relocation, and compile/audit the integrated actual statement and affected consumers. |
| **053** `HomNeighborhood.StandardInputs.free_neighborhood` | Latest D/`obl053_free_open_transport/source.lean` is the successful `LSHomFreeOpenTransport.lean`, 73.791 s; its exhaustive audit passed in 57.837 s. | Construct the first FreeOpen. The proof transports **all13 fields** (neighborhood plus12 further fields) of supplied data; it does not create existence. |
| **054** `presentation_exists_of_projectiveProduct` | The general relative-Hom comparisons, reverse constructor and early absolute constructor are support. | Prove scheme representability for the actual projective-product family, with the original all-test universal evaluation. No saved complete054 replacement is present. |
| **055** `HomDeformationInput.StandardInputs.locallyOfFinitePresentation` | D/`obl055_integration_proposal/generic_source.lean` and `geometry_source.lean`, with guard and independent review. Project functor/evaluation comparisons were checked separately. | Register the precise generic Stacks0D1C scheme-representer specialization, then run integrated native/type/dependency checks. It assumes a supplied representer; it does not prove051/054. |
| **056** `smooth_of_firstCohomology_vanishes` | The latest results are the seven-boundary progress note **plus its residue-point addendum**; detailed map below. | Actual flat-family ideal, obstruction coefficient and cohomology comparisons, then global small-extension lifting and the pointwise criterion. No complete056 wrapper exists. |
| **057** `smooth_connected_complex_geometricallyIntegral` (**3j**) | Completed conditional V4 in D/`obl057/source.lean`; proposed `LSGeometricIntegrality.lean` and single-body contact patch in D/`integrality_integration_proposal/`. | Register/review the three exact generic inputs and compile the integrated corollaries. Its use for052 does not make057 a3i obligation or grant credit. |

[050/051 mathematical design](../../audit/deferred_next_steps_20261104/obl050051/design.md) explains the actual existence and boundedness gaps. The generic all-test upgrade proposed there is SGA3 XI Remark3.4: Zariski gluing and filtered-colimit compatibility of the actual Hom functor must still be discharged. Stacks0D1C supplies an algebraic-space representer; a scheme-existence conclusion must not be inferred from that alone.

## 3. The ready source-integration proposal

Read [the combined static review](../../audit/deferred_next_steps_20261104/combined_future_static_review/review.txt) and [its manifest](../../audit/deferred_next_steps_20261104/combined_future_static_review/manifest.json). The proposal has **311 modules: 3 new and6 modified**, no detected import cycle, missing import or diagnostic import, and **220 affected current modules**. These are historical static results, not native passes.

| Intended production file | Exact saved candidate | SHA256 prefix |
|---|---|---|
| `LSGeometricIntegrality.lean` | D/`integrality_integration_proposal/generic_source.lean` | `97a08d7e6614` |
| `LSContactLineTests.lean` | D/`integrality_integration_proposal/contact_source.lean` | `a8672c168656` |
| `LSRelativeHomFunctor.lean` | D/`obl055_integration_proposal/generic_source.lean` | `43a0cd70213a` |
| `RecompileExtensionsPart04Geometry.lean` | D/`obl055_integration_proposal/geometry_source.lean` | `fa5d3ff62015` |
| `LSHomTwoPointDominance.lean` | D/`obl052_integration_proposal/helper.lean` | `ff2f9ee480fa` |
| `RecompileExtensionsPart02.lean` | D/`obl052_integration_proposal/ext02.lean` | `f547b9763365` |
| `LSConicJets.lean` | Inside D/`obl052_integration_proposal/bundle.json` | `e4e0f0a79da6` |
| `LSStableMapFamily.lean` | Same bundle | `c2cfbf1783b2` |
| `LSProjectAssembly.lean` | Same bundle | `cd6b5707d910` |

The bundle contains all five Pub candidate sources, exact diffs, builder, guards and original checked helper sources. Decode its declared gzip/base64 envelope and verify the decoded hash; no original scratch path is required.

The proposal removes exactly the original052,055 and057 `sorry` bodies and introduces **four separately named generic published inputs**: the three integrality criteria (Stacks0363;056T with the literal normality formulation033I;033O) and the general relative-Hom finite-presentation input (Stacks0D1C/01TO). It does not solve056. Original headers and all3h proof bodies were guarded; six relocated downstream proofs are byte-identical.

**Critical import cut:** do not import the late deformation chain directly into Ext02. `LSHomDegree` and the other required geometry already depend on Ext02. The prepared cut moves these seven declarations into `LSHomTwoPointDominance`:

1. `StandardInputs.homOpen_twoPointEvaluation_dominant`;
2. `Refinement.fullFamily_detects_bundle_section`;
3. `Refinement.fullFamily_detects_section`;
4. `Refinement.fullFamilyIdentity_symmetric`;
5. `Refinement.fullFamilyKernel_unique`;
6. `Refinement.FullFamilyDiagonalProof.detects_base_section`;
7. `Refinement.fullFamily_diagonalValue`.

The three external users listed in the table receive an import of the new module. Its imports are `LSNodalTangent`, `LSHomDegree`, `LSChartSmoothnessCriteria`, and `LSGeometricIntegrality`. The existing canonical obligation locations and acceptance/audit roots must be rebound to this relocation during a future integration. The later support proofs in sections4–5 below were **not** folded into this311 snapshot.

## 4. Module identities and diagnostic imports

The repository deliberately stores many sources as `source.lean`; that is an archive filename, not necessarily the original Lean module name. Restore the identity from the result/guard/evidence before replaying a diagnostic. Use cleaned modules and new exact guards for production; do not retain `Profile`/`Probe` imports merely to make a scratch build work.

| Latest source | Original module / useful API | Import or scope caveat |
|---|---|---|
| D/`early_hom_construction/core_source.lean` | `LSRelativeHomCoreComparisonProbe`; actual relative morphism functor, source maps, `homBaseChangeEquiv`, universal-element comparison | Mathlib-only; complete26.992 s control. |
| D/`early_hom_construction/absolute_source.lean` | `LSAbsoluteHomEarlyConstructionProbe`; `AbsoluteHomEarlyConstruction.ofRepresentation` | Ext01 plus the preceding core; complete11.249 s. This is the preferred early organization. |
| D/`hom_presentation_comparison/source.lean` | `LSHomPresentationComparison`; `HomPresentationComparison.canonicalIso`, evaluation and `mapAt` compatibility | Ext01-only;19 declarations,50.738 s. |
| D/`basechangeHom/source.lean` | `LSRelativeHomBaseChangeEquiv`; `homBaseChangeEquiv` and naturality | Imports original `LSRelativeHomFunctorTranslationProbe`;31.352 s. |
| D/`relative_hom_reverse_comparison/source.lean` | `LSRelativeHomRepresentationConstructionProbe`; `RelativeHomConstruction.ofRepresentation` | Requires the general/project functor comparison;32.219 s. |
| D/`fixed_degree_open_transport/source.lean` | `LSHomDegreeStratumTransport`; `transport`, `nonempty_transport` | Diagnostic imports `LSHomPresentationComparisonProfile`; replace through guarded integration with the actual clean comparison module. |
| D/`obl053_free_open_transport/source.lean` | `LSHomFreeOpenTransport`; `transport`, `nonempty_transport` | Same profile-import issue; uses Geometry and supplied FreeOpen, not the original053 theorem. |

The early core duplicates general functor names in the proposed `LSRelativeHomFunctor`. Do not import both unchanged into one environment: choose a shared early core or prove the exact extraction/rename guard. The older `absolute_representer_constructor/` is useful history but imports the later reverse comparison, so it is unsuitable as-is before051.

The [early-context addendum](../../audit/deferred_next_steps_20261104/early_hom_construction/context_scope_addendum.txt) is essential: the checked34-module early closure had33 unchanged source files, but Part06 was the older Point1 version. Current308 has accepted3h Part06. Equal descendant source bytes do not permit reuse of an old recursive native context.

For052 the cleaned candidate already inlines the nine checked sections: HomPointDeformations → HomMarkedEvaluation → TwoPointDeformations/TwoMarkedHomLifts → TwoPointProductLifts; FixedMarkings; SmoothRestrictionDensity; TwoPointDominance; ComplexCriterionSpecialization. The actual argument applies3h smoothness to the **fixed-pair map from the smooth open U**, proves density in the irreducible target, and transfers density to the full evaluation through the fixed-markings section. It does not require a newly assumed smoothness of the entire HomTwoPointEvaluation source. The earlier complete conditional052 audit had four explicit criteria; the later specialization discharges the tangent criterion, and the proposed integrality module supplies the other three only after its own review/integration.

## 5. Last unfinished part: OBL-056

Start with [the original seven-boundary plan](../../audit/deferred_next_steps_20261104/obl056_finite_yoneda_h1/plan_markdown.md), then [the progress note](../../audit/deferred_next_steps_20261104/obl056_progress_note/markdown.md), then **[the later residue addendum](../../audit/deferred_next_steps_20261104/obl056_residue_point_lifting/progress_markdown.md)**. The last of these supersedes the note's statement that test-centre construction is still open.

### Latest successful supporting sources

| Saved source | Actual module / completed result | Recorded local pass |
|---|---|---:|
| D/`obl056_finite_yoneda_h1/actual.lean` | `LSFiniteYonedaFirstCohomologyV2`: finite coproduct preservation/reflection of actual Yoneda extension splitting, including the empty family |33.165 s |
| D/`parameter_family_lifting/source.lean` | `LSRelativeHomLiftingCorrespondenceProbe`: `RelativeHomLifting.lift_iff_family` for the actual all-test morphism functor |32.584 s |
| D/`obl056_ordinary_lifting/source.lean` | `LSRelativeHomPresentationLifting`: `lift_iff_evaluation`, `point_lift_iff_evaluation` for supplied project `Presentation` and literal evaluation maps |36.494 s |
| D/`obl056_residue_field_boundary/source.lean` | `LSRationalPointResidueCompatibilityV3`: actual rational-point/base residue isomorphisms and their compatibility;12 declarations |35.545 s |
| D/`small_extension_kernel_algebra/source.lean` | `LSSmallExtensionKernelProbeV2`: length-one module/residue equivalence, maximal-ideal annihilation, literal kernel properness and square-zero equality;7 declarations |27.819 s |
| D/`obl056_central_coefficient/source.lean` | `LSRelativeHomCentralCoefficient`: actual family restriction, pullback-composition coefficient iso, and central tangent H1 transport;10 declarations |37.876 s |
| D/`smooth_locus_neighborhood/source.lean` | `LSSmoothLocusPointNeighborhoodProbe`: smooth locus gives a smooth open containing the actual field-valued point's whole image |47.894 s |
| **D/`obl056_residue_point_lifting/source.lean`** | **`LSResiduePointLiftingV2`: actual compatible test centre;7 declarations, Mathlib-only** |**29.762 s** |

The final residue construction takes `f : T → X`, `t : T`, `p : Spec K → X`, the **actual** residue-map isomorphism at `t`, and `p(closedPoint K)=f(t)`. It constructs `q : Spec K → T` with `q≫f=p` and the correct centre. It also proves the base equation. `ResiduePointLifting.exists_localTestCentre` gives the exact specialization needed for `T=Spec B`. No Artinianity, smoothness, flatness or residue-isomorphism assumption on `p` was added.

The ordinary lifting/residue sources import `LSRelativeHomLiftingCorrespondenceProbe`, which imports `LSRelativeHomFunctorTranslationProbe`. Both original parent sources are preserved inside D/`obl056_ordinary_lifting/evidence.json` and the residue-field evidence. Decode those envelopes when reconstructing the original diagnostic chain.

### The exact remaining mathematics

The original056 is unchanged in `RecompileExtensionsPart04Geometry.lean`. It assumes a locally Noetherian base, proper flat locally finitely presented source family, smooth proper complex target, supplied all-test `Presentation`, local finite presentation of `H.toBase`, and the original rational point/base equations. Its H1 assumption is the actual pullback of `tangentSheaf X.structureMap` along the central evaluation. Its conclusion is a smooth open restriction of the **actual** `H.toBase` containing the range of that point. No extra integrality, projectivity or source smoothness should be added.

For every permitted small extension `B′ → B` and test `α : Spec B → H`, the remaining proof must perform these concrete steps:

1. **Centre and restriction:** instantiate the completed residue-point V2 to obtain the compatible `i : Spec ℂ → Spec B`; use the proved family-change and evaluation equations. These ordinary pieces are now available, although the universal test argument is not assembled.
2. **Actual family ideal:** from flatness of the original source family identify the sheaf ideal of `Y_B → Y_B′` with the base-changed **literal kernel** `I=ker(B′→B)`, including quotient, module/scalar action and square-zero data. The small-kernel algebra result does not identify this sheaf.
3. **Actual obstruction coefficient:** identify the literal internal-Hom sheaf
   `Hom(g_B* Ω_(X/ℂ), J)`
   with the closed-central-fibre pushforward of the actual central tangent coefficient tensored with `I`. This needs locally free cotangent duality, tensor/pushforward compatibility and the compatible residue scalar structures. No such combined comparison has yet been proved or admitted.
4. **Cohomology:** transport the original Yoneda-H1 vanishing through the support/scalar-restriction and coefficient comparisons, using the existing derived-H1 bridge and finite coefficient-sum proof as appropriate. The completed central result is only `j*(g*E) ≅ g₀*E` and vanishing on the central fibre; it is not vanishing of the whole obstruction sheaf on `Y_B`.
5. **Lifting and smoothness:** apply the exact generic obstruction theorem to obtain the global extending family, use `PresentationLifting` to obtain the parameter lift, quantify over all small tests, apply the pointwise criterion, and finish with the proved smooth-locus wrapper.

Only **two proposed generic published boundaries** remain in the plan; neither has been installed:

- **SGA1 ExposéIII Proposition5.1/Corollary5.2**, printed pp.59–61 (arXiv PDF indices74–76): for one actual square-zero closed immersion and its actual ideal, a smooth target and an actual map, vanishing of the literal internal-Hom obstruction H1 supplies a global extending morphism. The leaf must not mention project Hom presentations or conclude a smooth neighborhood. [Archived precise source/type plan](../../audit/deferred_next_steps_20261104/obl056_finite_yoneda_h1/plan_markdown.md).
- **Stacks02HX, Lemma37.12.1(4)⇒(1)**, with the literal **02HS** small extensions: local Artinian rings, a surjection, kernel of module length one, and the actual centre/residue conditions. Dual-number lifting alone does not suffice.

OBL055 is not a logical prerequisite for this056 proof:056 already assumes local finite presentation. Using the3h differential converse on an unknown smooth Hom source would be circular. Likewise, neither SGA1's later ideal-adic corollaries nor the cotangent-complex obstruction in08U8 removes the actual coefficient comparisons above.

**Inherited admission scope:** the central coefficient module's first nine declarations use standard axioms only; `centralTangent_h1` inherits exactly the accepted generic `PublishedInputs.SheafFunctoriality.cotangentPresentation`. Its complete audit passed36.715 s (31,783 constants;179 project; no original056). The coefficient/result records explicitly retain the older local import context. Do not advertise the tangent specialization as having no `sorryAx` at all.

## 6. Recommended next integration order

1. Preserve accepted308 and extract the saved sources/guards into a separate candidate worktree. Do not run historical builders against missing absolute scratch paths without adapting and recording those paths.
2. Review/register the four exact generic inputs needed by the prepared052/055/057 proposal. Integrate its three new modules, guarded original-body replacements and seven-declaration/import cut as one coherent source graph. The proposed manifest is `c6c4eb7be981426b7db7796fcc0525b3e3ac8484f91bc57299e5f0fce7039c85`.
3. Compile that integrated graph using current accepted parents and audit changed original roots/affected descendants before any ledger change. The earlier conditional052 audit cannot certify its newly instantiated production theorem, and the static220-module impact calculation is not a native receipt.
4. Separately organize the later early-Hom core and transport helpers into clean common modules. Reuse them for051/054 scheme representability and050/053 existence; the supplied-data transport proofs do not close these obligations. Keep049's first-jet comparison explicit.
5. Continue056 at the actual flat ideal/coefficient comparison above. This work can be logically independent of the scheme-existence obligations because its presentation and finite-presentation hypotheses are supplied. Keep the two prospective generic inputs as explicit parameters until their final type/source eligibility is reviewed.

The rest of the pending ledger remains authoritative:3i049–056;3j057–064;3k065–068 and070–072;3l073–078;3m079–083;3n084–091. This handoff does not claim prepared solutions for every later ID. Fu's coarse-family route is separately reviewed and has caused no retirements.

## 7. Failed or superseded variants to avoid

- Use integrality **V4** (`d2892be4…`), not failed V1–V3; its three criteria are still explicit in that checked source.
- Use finite-Yoneda-H1 **V2**, rational-residue compatibility **V3**, small-kernel **V2**, FreeOpen **V3**, and residue-point lifting **V2**. Their successful filenames above are authoritative even when the archived basename is simply `source.lean`.
- FreeOpen V1/V2 failed at function/coercion presentations of dense range. The passing source uses an explicit generic density lemma and literal scheme-function equality. Do not reintroduce the earlier broad rewrite.
- Residue-point V1 had ordinary diagnostic placement, missing included hypotheses and `Spec.map_comp` rewrite errors. V2 keeps `hp` and the residue-isomorphism premise in the actual existential declarations. Do not delete those premises because a section variable looks unused in the visible conclusion.
- Avoid the old late absolute-constructor import chain when implementing051 before Geometry. Use the early Mathlib core/Ext01 organization, then recheck current dependency contexts.
- Do not turn a tactic EXIT marker, an inferred-type print, a failed module's later marker or a local diagnostic pass into full native acceptance. Earlier failed receipts are retained for scope and diagnosis, not reusable outputs.
- Do not substitute an algebraic-space representer for the required scheme, local degree constancy for boundedness, a two-point map for first jets, or a conditional supplied-data transport for existence.

## 8. Preservation and evidence recovery

The pinned deferred subtree contains all126 indexed files (125 distinct Git blobs; one review is intentionally referenced twice), plus INDEX.json. The latest source/result packages remembered by the source owner are attached: residue V2 with its19-file evidence and dated addendum, central coefficient with its21-file proof/audit evidence, finiteH1, ordinary lifting, rational-residue V3, small-kernel V2, early Hom constructors, and FreeOpen V3. The final acceptance output review is separately attached at `audit/step3h_acceptance_41912044307/GENERATED_OUTPUT_INDEPENDENT_REVIEW.json`, blob `ab772c0ad061a566b9eb345b2fa85b4867f52cad`.

One later **independent review**, not a missing proof, was detached from accepted11c18: Pub's residue-point review blob `e1b00b7aa0c2ca00887696c0adec5389d9d886e8`, SHA256 `a23a808cf10f87e4e337054b508587ea047234fa2c0f3685824ce9050f6e3541`. It is recovered as [a handoff supplement](RESIDUE_POINT_LIFTING_INDEPENDENT_REVIEW.json). The actual source/profile/evidence and root's review were already in the accepted deferred tree. No latest substantive proof result is known to be missing.

Evidence envelopes are data: read their declared encoding and decoder, verify compressed/decoded hashes and each file hash, then recover the named files. Formats include gzip+base64, XZ+base64 and per-file base64/UTF-8 records. A package may deliberately omit binary `.olean` output while retaining its hash, source, runtime configuration, receipt and raw logs; that is stated in its metadata. Do not invent missing binaries or treat a historical local `.olean` as a current308 parent. Source preservation and current native cache availability are different questions; the [build note](BUILD_AND_RESUME.md) handles the official runtime/cache restoration.
