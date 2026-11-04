# LeBrun–Salamon formalisation: continuation

**Status on 4 November 2026: working candidate; the published-theorems-only milestone is not met.**

The conservative acceptance-checklist completion floor is **30/133 = 22.56%, rounded to 23%**. This counts fully accepted items from the agreed plan and records newer proof work separately; it does not estimate mathematical effort or time remaining. See [the fixed ledger](audit/MILESTONE_PROGRESS.md).

This directory contains the actual source recovered from the cumulative Step 3g V2 checkpoint, the frozen Step 2 target, and the takeover audit. The original recovery commit is `d8749550ace47a9186fcc1d8c2a38fa81d8b3ba0`; it preserves all 129 recovered source modules byte for byte. Subsequent changes are explicit descendants of that commit.

Start with **[TAKEOVER_PLAN.md](TAKEOVER_PLAN.md)**. Machine-readable current status is in [TAKEOVER_STATUS.json](TAKEOVER_STATUS.json).

Steps **3c, 3d, 3e and 3f were reported complete** in the earlier conversation. Their current handover status is **reported complete; recovered source awaiting verification and identified repairs**. The historical evidence boundary at Step 3b must not be confused with the latest development position. The plan records the completion announcements and the distinction between missing certificates and concrete source defects.

## Point 1 checkpoint — 2026-11-04T01:05:53.044287+00:00

This immutable candidate contains **213 Lean modules and 97 direct `sorry` tokens**. The frozen target and pinned toolchain lock are unchanged. Exact candidate bytes are identified by `SOURCE.sha256` and [audit/point1_checkpoint/FREEZE.json](audit/point1_checkpoint/FREEZE.json). Source admission counts do not establish eligibility as published theorem inputs.

The latest completed full replay, [41745746489](https://github.com/wajcha2/claude/actions/runs/41745746489), checked commit `6b976918d73e771813e661711f0395137b94c4f5` with all 172 modules selected. It accepted **139 modules: 30 strictly reused and 109 freshly compiled**. 3 modules failed and 30 were blocked. The failed modules were `LSConicJets`, `LSStandardConicDifferential`, `LSProductGeometry`; their exact diagnostics are retained in [audit/ci/41745746489/](audit/ci/41745746489/).

That run freshly checked `RecompileSections`, Extensions Parts 01–04Geometry, `LSHomVelocity`, `LSNodalTangent`, `LSNodalFixedEnds`, and the integrated epsilon/Hom and family-degree helpers at its committed source. Every accepted source, import, dependency output, native artifact, log, and compiler/runtime identity was validated; final validation found no changed inputs or runtime files. Later edits change the dependency ancestry, so these 139 passes retain their exact-commit scope.

All **17 original Step 3c/3d obligations** now have native proof/source evidence: 14 project composites have proved translations and three are exact generic published inputs. Step 3d includes actual pullback and fibre exactness, canonical Hom base change and fibre injectivity, the generating-unit-open cover, and both total-line and total-bundle representations. Native public-type adapters and exhaustive dependency inventories are retained. The changed containing modules and live reverse dependency graph still require replay. See [audit/STEP3CD_ACCEPTANCE_LEDGER.md](audit/STEP3CD_ACCEPTANCE_LEDGER.md) and [audit/STEP3D_INTEGRATION_READY.json](audit/STEP3D_INTEGRATION_READY.json).

The original normalized-source-bivector signature is also now implemented by construction, symmetry, uniqueness, affine-frame normalization, and the second-diagonal argument. Its ten proof modules and exhaustive 82,298-constant diagnostic passed, with the old normalized-source admission absent. That diagnostic used historical project interfaces; its old diagonal and affine-derivation leaves have proved replacements in this candidate, which the fresh full replay must connect. Exact scope is recorded in [audit/p1_source_bivector_work/SCOPE.json](audit/p1_source_bivector_work/SCOPE.json).

The exact `LSRelativeDifferential` and `LSStandardConicDifferential` compatibility repairs passed focused native checks over the frozen cdf ancestors. The latter still retains its historical fundamental-class composite input until its constructive replacement is completed. The full `LSProductGeometry` module passed after factoring finite-type transitivity through abstract algebras and making the principal affine-open type explicit. Its original generic product-geometry admission is unchanged and belongs to the later Step 3m work. `LSConicJets` has a checked exact 1,142-line initial segment; its remaining tail and full containing-module replay are still pending. These diagnostic passes retain their recorded ancestor scope.

The current source also contains the normalized projective-coordinate constructor and marked tautological-line accessors, together with individually checked trait-embedding and cohomological lifting helpers. Their exact source/receipt evidence is preserved in the corresponding audit directories. The original formal-trait normal-form conclusions still require their final assembly and source-boundary audit. Added helpers and fewer composite admissions do not themselves complete an original checklist obligation.

The next stock-compiler replay selects all **213 modules**, with a 12000 MB cap and run **41745746489** as its sole cache source. Source, import, lock, output, and full project ancestry checks permit **46** cache outputs at this freeze. It first checks the actual current `RecompileExtensionsPart01` dependency closure and uploads a separate early artifact, then continues the full graph in the same build directory with strictly validated reuse. This makes the current normalized-coordinate interface available for downstream proof work without treating that partial artifact as a full replay. All other selected modules must compile against the candidate's actual dependencies. The replay revalidates the complete selected graph at completion; no result from that run is assumed.

**Point 1 remains open.** Its 43 obligations across Steps 3c–3g still require the stage acceptance gates: exact published statements, proofs of the nondefinitional project translations, and successful replay of the affected current sources and dependencies. The remaining proof work and compatibility candidates are recorded with their individual evidence. Off-graph unfinished drafts are excluded from the source graph.

The conservative accepted floor remains **30/133 = 22.56%, rounded to 23%**. This checkpoint adds no accepted checklist unit before the current source and proof-boundary gates pass. The published-theorem-only milestone and the frozen endpoint bridge remain open.

## Findings at the takeover audit

- The recovered archive has SHA-256 `722c44bc3e21211634732fc92fb0d598b429f886ac85dec3d3699318d4a3fe32`.
- The last recorded passing incremental stage is Step 3b: eight wrappers discharged to its recorded published-input boundary, with 91 further proof/refactoring obligations. This was not a complete clean build of the final theorem.
- The recovered V2 has 129 source modules and 98 direct admissions. Fifty are in `PublishedInputs` namespaces; this is a namespace count, not certification of fifty published theorems.
- The initial continuation found that the determinant input omitted alternation. Its replacement now isolates the alternating discriminant theorem on smooth proper complex bases, cites Auel's 2009 thesis, Proposition 1.10 and Definition 1.7, and proves the determinant conversion and contact specialization. The native diagnostic pass is recorded separately from cumulative acceptance.
- The legacy exported theorem concludes local Riemannian symmetry. The new conditional assembly makes the additional Wolf-homothety obligation explicit, as described above.

## Files and evidence

- [source/](source/): current Lean candidate, with current hashes in [SOURCE.sha256](SOURCE.sha256).
- [target/MainStatement.lean](target/MainStatement.lean): immutable Step 2 specification, SHA-256 `9afe9c5b2e63db17e8f217b71c821eaca83fe26c5cfbc2956fc1b92832d09296`.
- [TOOLCHAIN.lock.json](TOOLCHAIN.lock.json): exact Lean/mathlib environment.
- [audit/RECOVERED_V2_SOURCE_AUDIT.md](audit/RECOVERED_V2_SOURCE_AUDIT.md): source, dependency, admission and endpoint findings before the repair.
- [audit/PUBLISHED_BOUNDARY_AUDIT.md](audit/PUBLISHED_BOUNDARY_AUDIT.md): mathematical checks and examples of unproved project-specific translations.
- [audit/COMPREHENSIVE_STATIC_AUDIT_V2.json](audit/COMPREHENSIVE_STATIC_AUDIT_V2.json): recovered-source hashes, graph, inventories and original obligation mapping.
- [audit/ORIGINAL_STEP3_PLAN.md](audit/ORIGINAL_STEP3_PLAN.md): the agreed original plan, preserved unchanged.
- [audit/proof_batch_build/](audit/proof_batch_build/): source-matched native diagnostic receipts and axiom output for the current proof batch.
- [audit/current_determinant_build/README.md](audit/current_determinant_build/README.md): determinant trust audit against freshly compiled current ancestors, with no baseline project artifacts.
- [audit/ci/41680976758/README.md](audit/ci/41680976758/README.md): independent clean four-module CI result and its exact scope.
- [audit/MILESTONE_PROGRESS.md](audit/MILESTONE_PROGRESS.md): fixed milestone acceptance checklist and percentage accounting.

The portable checker in `scripts/check_checkpoint.py` is a static integrity and rebuild-planning tool. It is not a Lean compiler or a mathematical certificate. The full milestone remains open; see the current status and compiler receipts for the precise tested scope.
