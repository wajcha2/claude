# LeBrun–Salamon formalisation: continuation

**Status on 3 November 2026: working candidate; the published-theorems-only milestone is not met.**

The conservative acceptance-checklist completion floor is **30/133 = 22.56%, rounded to 23%**. This counts fully accepted items from the agreed plan and records newer proof work separately; it does not estimate mathematical effort or time remaining. See [the fixed ledger](audit/MILESTONE_PROGRESS.md).

This directory contains the actual source recovered from the cumulative Step 3g V2 checkpoint, the frozen Step 2 target, and the takeover audit. The original recovery commit is `d8749550ace47a9186fcc1d8c2a38fa81d8b3ba0`; it preserves all 129 recovered source modules byte for byte. Subsequent changes are explicit descendants of that commit.

Start with **[TAKEOVER_PLAN.md](TAKEOVER_PLAN.md)**. Machine-readable current status is in [TAKEOVER_STATUS.json](TAKEOVER_STATUS.json).

Steps **3c, 3d, 3e and 3f were reported complete** in the earlier conversation. Their current handover status is **reported complete; recovered source awaiting verification and identified repairs**. The historical evidence boundary at Step 3b must not be confused with the latest development position. The plan records the completion announcements and the distinction between missing certificates and concrete source defects.

## Current proof batch

- The first-jet claim now has an explicit closed-immersion proof through actual dual-number maps and projective coordinates. Both helper modules and the public wrapper compile against the recovered dependency interfaces.
- The dual-thickening point-surjectivity claim is proved from its nilpotent residue kernel and the actual pullback. Its actual project specialization compiles; native axiom inspection finds no `sorryAx` dependency.
- The determinant argument uses a restricted alternating-discriminant leaf and an explicit tensor-cancellation proof. The corrected module and all its current ancestors passed fresh CI; an independent native audit of those exact current artifacts confirms the five remaining admitted inputs and excludes the defective old input.
- Three new target modules import the frozen statement through shared definitions and assemble its full conclusion conditionally on the explicit simple-connectedness bridge. They do not assert an unconditional final theorem.
- Direct source admissions have decreased from 98 to 96, with no new admissions. The five changed proof modules have native diagnostic passes; these do not certify the full current dependency graph.
- Stock-compiler GitHub Actions run [41680976758](https://github.com/wajcha2/claude/actions/runs/41680976758) freshly compiled the nilpotent topology helper, the shared foundation, the frozen-statement formulation and its topology module. All four passed.
- A dependency-aware replay driver checks source, output, runtime and dependency hashes, including a final validation at the end of the batch. The CI workflow now attempts every project module.

The first full replay, [41682674689](https://github.com/wajcha2/claude/actions/runs/41682674689), freshly passed **19 modules**, including the repaired determinant module and all its current ancestors. It then reached Lean's 7200 MB memory cap in `RecompileBasePart07`; 115 dependent modules were blocked. The subsequent run [41685948946](https://github.com/wajcha2/claude/actions/runs/41685948946) uses a 12000 MB cap on the same 135 Lean source blobs. Its result is pending. The later missing-name/type diagnostics from the first attempt are not treated as independent source defects before this resource-sufficient replay.

The preserved evidence distinguishes **a fresh current dependency build** from **a candidate checked against recovered historical interfaces**. The latter is useful proof-development evidence, but is not acceptance of the cumulative project or of a whole Step 3 stage.

A native recursive audit of the first-jet theorem traversed 78,870 constants, including 583 project constants, and found exactly one direct inherited admission: the generic preservation of local freeness and rank under pullback. It found no dependence on the historical first-jet claim or the defective determinant input. [The dependency report](audit/proof_batch_build/README.md) records the exact path and type; [the reference clarification](audit/PULLBACK_RANK_REFERENCE.md) supplies explicit fixed-rank primary sources, including Vakil's rank-one case used here.

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
