# LeBrun–Salamon formalisation: continuation

**Status on 3 November 2026: working candidate; the published-theorems-only milestone is not met.**

The conservative acceptance-checklist completion floor is **30/133 = 22.56%, rounded to 23%**. This counts fully accepted items from the agreed plan and records newer proof work separately; it does not estimate mathematical effort or time remaining. See [the fixed ledger](audit/MILESTONE_PROGRESS.md).

This directory contains the actual source recovered from the cumulative Step 3g V2 checkpoint, the frozen Step 2 target, and the takeover audit. The original recovery commit is `d8749550ace47a9186fcc1d8c2a38fa81d8b3ba0`; it preserves all 129 recovered source modules byte for byte. Subsequent changes are explicit descendants of that commit.

Start with **[TAKEOVER_PLAN.md](TAKEOVER_PLAN.md)**. Machine-readable current status is in [TAKEOVER_STATUS.json](TAKEOVER_STATUS.json).

Steps **3c, 3d, 3e and 3f were reported complete** in the earlier conversation. Their current handover status is **reported complete; recovered source awaiting verification and identified repairs**. The historical evidence boundary at Step 3b must not be confused with the latest development position. The plan records the completion announcements and the distinction between missing certificates and concrete source defects.

## Point 1 checkpoint — 2026-11-03T22:08:02.671367+00:00

This frozen candidate contains **149 Lean source modules and 92 direct `sorry` tokens**. Source token counts are inventories, not counts of accepted published theorems. The immutable target remains byte-identical. The source manifest is `SOURCE.sha256`; the freeze receipt and exact source hashes are in [audit/point1_checkpoint/FREEZE.json](audit/point1_checkpoint/FREEZE.json).

The latest completed full run, [41714131927](https://github.com/wajcha2/claude/actions/runs/41714131927), checked commit `0e7a654645d92fe82473e358a925b47101305e97`: **97 of 135 modules were accepted for that commit (32 reused with exact receipts and 65 freshly compiled), 5 failed and 33 were blocked**. The final receipt validation invalidated no accepted output. The failures were `LSBranchRamification`, `LSNodalFixedEnds`, `LSConicJets`, `LSClassicalActions` and `LSProductGeometry`; their exact diagnostics are preserved in [audit/ci/41714131927/](audit/ci/41714131927/). The earlier 12000 MB run 41685948946 completed with 32 passes, a Geometry parser failure and 102 blocked modules. That Geometry compatibility repair subsequently passed.

This candidate includes new proofs and explicit translations for the Step 3c diagonal/projection-formula work, Step 3d fiber-rank work, Step 3e determinant/smooth-cotangent/ampleness work, Step 3f cotangent deformations and dual-thickening normal forms, and Step 3g projective, Laurent and Picard work. Their native helper checks are recorded with their exact tested interfaces. They are **diagnostic proof-development evidence**, not acceptance of the whole current source graph. Compatibility repairs are recorded separately in [audit/ci_compatibility_repairs/](audit/ci_compatibility_repairs/).

The marked projective-line tangent-to-`O(2)` translation also passed a 14.972 s native diagnostic and an 8.175 s transitive audit excluding the former tangent admission. It is integrated into `RecompileSections`, which now contains no direct `sorry`. The audit retains the five inherited inputs of its tested historical interface; it does not certify the newly edited ancestor graph. See [audit/p1_tangent_build/](audit/p1_tangent_build/).

The next full CI run attempts every module in this frozen candidate using the stock pinned compiler with a 12000 MB cap. Its only cache source is run **41714131927**. The cache validator checks source bytes, imports, compiler/runtime identity, output hashes and the entire dependency ancestry; it does not reuse the other 85 old-head outputs merely because they once passed. Twelve outputs still match the current full ancestry at this freeze. The driver revalidates the entire selected batch at the end. No result from this new run is assumed in this checkpoint.

**Point 1 (43 obligations across Steps 3c–3g) remains open.** The remaining work includes the actual vector-bundle exactness translations, internal-Hom/fiber maps, diagonal and normalized source calculations, Hom vanishing, and the required native transitive-boundary and affected-graph checks. An exact primary theorem and a proof of each nondefinitional project specialization are required. A newly renamed admission is not a completed obligation.

The conservative accepted floor remains **30/133 = 22.56%, rounded to 23%**. No additional full acceptance unit is claimed for this candidate. The publication-only milestone, frozen endpoint bridge and eight definition validations remain open.

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
