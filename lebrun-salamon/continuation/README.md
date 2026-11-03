# LeBrun–Salamon formalisation: continuation

**Status on 3 November 2026: working candidate; the published-theorems-only milestone is not met.**

The conservative acceptance-checklist completion floor is **30/133 = 22.56%, rounded to 23%**. This counts fully accepted items from the agreed plan and records newer proof work separately; it does not estimate mathematical effort or time remaining. See [the fixed ledger](audit/MILESTONE_PROGRESS.md).

This directory contains the actual source recovered from the cumulative Step 3g V2 checkpoint, the frozen Step 2 target, and the takeover audit. The original recovery commit is `d8749550ace47a9186fcc1d8c2a38fa81d8b3ba0`; it preserves all 129 recovered source modules byte for byte. Subsequent changes are explicit descendants of that commit.

Start with **[TAKEOVER_PLAN.md](TAKEOVER_PLAN.md)**. Machine-readable current status is in [TAKEOVER_STATUS.json](TAKEOVER_STATUS.json).

Steps **3c, 3d, 3e and 3f were reported complete** in the earlier conversation. Their current handover status is **reported complete; recovered source awaiting verification and identified repairs**. The historical evidence boundary at Step 3b must not be confused with the latest development position. The plan records the completion announcements and the distinction between missing certificates and concrete source defects.

## Point 1 checkpoint — 2026-11-03T22:34:09.806987+00:00

This immutable candidate contains **155 Lean modules and 92 direct `sorry` tokens**. Counts of source admissions do not certify their published-theorem eligibility. The frozen target and toolchain lock are unchanged. `SOURCE.sha256` and [audit/point1_checkpoint/FREEZE.json](audit/point1_checkpoint/FREEZE.json) identify the exact candidate.

The latest full replay, [41728791345](https://github.com/wajcha2/claude/actions/runs/41728791345), checked commit `6fa6ee1a25735be73e73be455aed94ad88eae8e1` with all 149 modules selected. It accepted **29 modules (12 strictly reused and 17 freshly compiled), failed 1, and blocked 119**. Its sole source diagnostic was the unqualified `structureModule` name in `LSPublishedPicard.lean`. This candidate qualifies that name as `PhaseTwentyFive.structureModule`; the next replay checks the repair. No accepted Sections or Ext01 output was produced by that run.

Every accepted source, import, dependency output, compiler/runtime fingerprint, output artifact, diagnostic log, and cache provenance was validated against the committed source. Fresh passes include Base04, Base05A/B/C, Base06 and Base07, so their integrated proof translations now have evidence in that source ancestry. The final validation reported no invalidation. Detailed receipts and exact failure evidence are in [audit/ci/41728791345/](audit/ci/41728791345/).

This checkpoint additionally includes the completed native diagnostic proofs for the epsilon/Hom-vanishing sequence, the arbitrary-affine relative derivation wrappers, and the projective-line family-degree translation. Their exact tested sources and inherited assumptions are recorded in `audit/STEP3F_HOM_VANISHING.json`, `audit/STEP3F_AFFINE_RELATIVE.json`, and `audit/p1_family_degree_build/`. These integrations still require their actual containing modules and current dependency graph to pass. Unchecked off-graph drafts are excluded.

The next full stock-compiler replay selects all 155 modules with a 12000 MB cap. Its sole cache source is run **41728791345**. The source/runtime/dependency validator permits only **28** ancestry-safe outputs at this freeze; the subsequently edited affine-derivation module is excluded. The replay revalidates the entire selected graph at completion. No result from this next run is assumed.

**Point 1 remains open:** all 43 original obligations across Steps 3c–3g still require the stage acceptance gates, including exact primary statements, proofs of nondefinitional project specializations, and the affected source/dependency replay. Actual pullback/fiber exactness, Hom/base-change and total-space transports, diagonal calculations and normalized source work continue outside this frozen candidate where unfinished. Historical run 41714131927 accepted 97 modules at its own older head; those outputs are not current-source acceptance.

The conservative accepted floor remains **30/133 = 22.56%, rounded to 23%**, with no additional full acceptance unit credited in this checkpoint. The published-theorem-only milestone and the frozen endpoint bridge remain open.

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
