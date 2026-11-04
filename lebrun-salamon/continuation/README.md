# LeBrun–Salamon formalisation: continuation

**Point 1 and Step 3h are accepted. The full published-theorems-only milestone remains open.**

The accepted checklist total is **79/133 = 59.40%**: 22 retired original admissions, eight historically accepted Step 3b wrappers, 43 Point 1 obligations, the separately accepted OBL-069, and five Step 3h obligations. There remain **42 original obligations, eight definition validations and four final gates: 54 units**. The denominator remains 121 original admissions plus eight definition validations and four final gates. This measures accepted checklist units; it does not estimate mathematical effort, time remaining or the fraction of source lines. Helpers, publication reviews and build receipts add no units.

## Accepted scope

| Step | Accepted original obligations |
|---|---:|
| 3c | 6/6 |
| 3d | 11/11 |
| 3e | 7/7 |
| 3f | 11/11 |
| 3g | 8/8 |
| 3h | 5/5 |
| Separate inherited OBL-069 | 1/1 |

## Step 3h proofs

| Original obligation | Completed project proof |
|---|---|
| OBL-044 | Identify the actual cotangent map with the canonical restriction map by universal derivations and adjunction; transfer the restriction isomorphism. |
| OBL-045 | Identify the actual differential with the immersion epimorphism and prove the rank of its literal kernel from smooth cotangent ranks. |
| OBL-046 | Lift the actual dual-number thickening through the supplied smooth open, then prove compatibility with the project tangent differential. |
| OBL-047 | Convert surjectivity of that differential into the canonical tangent-lift criterion, retaining both original structural smoothness assumptions. |
| OBL-048 | Construct a linear equivalence between project derivations and the dual of the actual cotangent fiber; deduce its dimension using existing rank results. No new published input is needed. |

## Native verification

[Native run 41912044307](https://github.com/wajcha2/claude/actions/runs/41912044307) verifies **308/308 current source modules** at `4d1aa547453f50736035a91f6fea81d340359143`. Exactly 50 accepted-baseline native contexts are preserved; 257 existing contexts have been revalidated, and one new module is verified. All source, output, log, receipt, recursive dependency and runtime bindings were checked. The final full-stage reuse count includes work already compiled in earlier stages of the same workflow. It is not the number of unchanged modules relative to Point 1.

The historical Point 1 audit used 190 ancestor modules. In the current source graph, 40 of those contexts are preserved and 150 have been revalidated. The historical all-190-unchanged event remains intact in its original record. The frozen theorem statement, toolchain lock and historical native drivers are unchanged.

See [the complete verification](audit/step3h_acceptance_41912044307/FULL_CONTINUATION_VERIFICATION.json) and [the acceptance record](audit/step3h_acceptance_41912044307/STEP3H_ACCEPTANCE.json).

## Published-input boundary

The current boundary covers **49 original roots** and **54 actual distinct eligible published inputs**. There are 39 fresh current native dependency walks and 10 historical boundaries reused only because their complete native contexts match exactly. Fresh baseline/current native type and universe comparisons preserve all 49 original statements. No original conclusion in this boundary is directly admitted; no missing constant, custom project axiom or unexpected axiom was found.

The five new published inputs state canonical restriction of differentials, the immersion differential epimorphism, the kernel rank of an epimorphism between locally free sheaves, square-zero lifting for smooth morphisms, and the rational-point tangent criterion for smoothness. Their exact native types were independently compared with the reviewed primary statements. The former direct admission of OBL-044 has been retired from the boundary. The original Point 1 evidence remains historical evidence; its distinction between 15 explicit native signature comparisons and 29 written-header comparisons is not retrospectively changed.

## Remaining proof and the Fu comparison

The first architecture comparison with Baohua Fu's [*The classification of Fano contact manifolds revisited*, arXiv:2611.01423v1](https://arxiv.org/html/2611.01423v1) is complete; see [the source-bound review](audit/continuation_3h/FU_ROUTE_REVIEW.md). The relative-conic and quadratic-term arguments may replace much of the remaining branch-geometry work, particularly OBL-073–077. The actual coarse-family comparison, arbitrary reduced-base chart construction and contact compatibility must be proved before any old obligation is retired. The finite-cover input still needs the correct single-target Picard-one scope. No obligation has been retired on the strength of this review, and the whole classification theorem has not been admitted.

Continue Step 3i with one coherent relative-Hom construction. The project presentation is now compared with the genuine functor on arbitrary test schemes in both directions, including the actual universal evaluation and target base-change naturality. The isolated OBL-055 composition and exact generic finite-presentation boundary have a reviewed proposed integration. Representing-scheme existence remains separate: the classical Hom/Hilbert reference has a locally-Noetherian-test restriction, and the SGA 3 XI, Remark 3.4 upgrade still requires its Zariski gluing and limit-preservation hypotheses to be proved.

For OBL-050 and OBL-051, the canonical isomorphism between supplied Hom presentations and its evaluation compatibility are proved. A supplied fixed-degree stratum now transfers to the original HomDegree.Open contract, preserving closedness, local finite type, quasi-compactness and the degree condition for every complex point. Its exhaustive local boundary contains exactly two already accepted published inputs and neither original OBL-050 nor OBL-051. Constructing the initial bounded stratum remains: preserve the given ample line through a very ample power and compute the actual graph Hilbert polynomial.

An end-to-end conditional OBL-052 prototype proves density of the actual universal two-point evaluation with the original geometric hypotheses. It fixes the two source markings, realizes their prescribed infinitesimal motions through the Hom universal property, and applies the smoothness criterion on the supplied smooth Hom open. The complete local dependency walk found four previously eligible published inputs and no pending original dominance or integrality admission. Four generic criteria remain explicit in that prototype; a separate checked specialization supplies its tangent criterion from the exact native Step 3h input.

For OBL-056, the parameter-lift equivalence is proved with the actual familyChange and evaluation equations. Finite coproducts preserve the original Yoneda first-cohomology vanishing predicate, including the empty family, and formal smoothness of the actual stalk map gives a smooth open containing the whole field-valued point. The main remaining comparison identifies the actual square-zero kernel and differential-Hom obstruction sheaf with the original fibre tangent-sheaf coefficient. The proposed published boundaries are SGA 1 III, Proposition 5.1/Corollary 5.2 for a specified thickening, and Stacks 02HX for all residue-compatible small Artinian extensions. These are a precise plan, not newly accepted admissions.

The target-product irreducibility prerequisite has a separate conditional composition for OBL-057 in Step 3j, using three generic field/normality criteria. The reviewed static integration proposal moves seven dominance/detection declarations to a later module and changes three consumer imports. Its complete native validation remains pending. All these isolated preparations add zero accepted units; their proposed source changes remain outside the accepted production snapshot until source, publication and native checks pass.

The full milestone remains **open**. The compiled assembly still takes the explicit `LeBrunSalamon.Milestone.PositiveQKSimpleConnectedness` bridge. The unconditional frozen theorem, including the actual positive-metric Wolf homothety, is not yet proved. All eight semantic definition validations and all four final-theorem gates remain pending. Current conditional compilation does not close those gates.

Continue with [the plan](TAKEOVER_PLAN.md), [the progress ledger](audit/MILESTONE_PROGRESS.md),
and [the machine-readable status](TAKEOVER_STATUS.json).

## Reproduction and history

`SOURCE.sha256` binds the checked production sources, `target/MainStatement.lean` the frozen
specification, and `TOOLCHAIN.lock.json` the runtime. The acceptance documentation commit
has identical production sources to the compiled commit; it is not a new compiler event.
The earlier current documents are preserved under [audit/history/pre_step3h_20261104](audit/history/pre_step3h_20261104).
Run 41900703071 stopped in the static checker before any compiler invocation; its sole
missing-section-end repair and complete failure evidence are retained under
`audit/continuation_3h/attempts/41900703071`.
