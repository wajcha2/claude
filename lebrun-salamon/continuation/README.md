# LeBrun–Salamon formalisation: continuation

**Status on 3 November 2026: working candidate; the published-theorems-only milestone is not met.**

This directory contains the actual source recovered from the cumulative Step 3g V2 checkpoint, the frozen Step 2 target, and the takeover audit. The original recovery commit is `d8749550ace47a9186fcc1d8c2a38fa81d8b3ba0`; it preserves all 129 recovered source modules byte for byte. Subsequent changes are explicit descendants of that commit.

Start with **[TAKEOVER_PLAN.md](TAKEOVER_PLAN.md)**. Machine-readable current status is in [TAKEOVER_STATUS.json](TAKEOVER_STATUS.json).

## What is established

- The recovered archive has SHA-256 `722c44bc3e21211634732fc92fb0d598b429f886ac85dec3d3699318d4a3fe32`.
- The last recorded passing incremental stage is Step 3b: eight wrappers discharged to its recorded published-input boundary, with 91 further proof/refactoring obligations. This was not a complete clean build of the final theorem.
- The recovered V2 has 129 source modules and 98 direct admissions. Fifty are in `PublishedInputs` namespaces; this is a namespace count, not certification of fifty published theorems.
- The current continuation adds an explicit alternating-form hypothesis to the determinant input and supplies the Levi alternation proof at its contact application. This source repair is **not yet kernel checked**. Its broad literature match is still pending.
- The current exported theorem concludes local Riemannian symmetry. It has not yet been connected to the separately frozen Wolf-homothety target.

## Files and evidence

- [source/](source/): current Lean candidate, with current hashes in [SOURCE.sha256](SOURCE.sha256).
- [target/MainStatement.lean](target/MainStatement.lean): immutable Step 2 specification, SHA-256 `9afe9c5b2e63db17e8f217b71c821eaca83fe26c5cfbc2956fc1b92832d09296`.
- [TOOLCHAIN.lock.json](TOOLCHAIN.lock.json): exact Lean/mathlib environment.
- [audit/RECOVERED_V2_SOURCE_AUDIT.md](audit/RECOVERED_V2_SOURCE_AUDIT.md): source, dependency, admission and endpoint findings before the repair.
- [audit/PUBLISHED_BOUNDARY_AUDIT.md](audit/PUBLISHED_BOUNDARY_AUDIT.md): mathematical checks and examples of unproved project-specific translations.
- [audit/COMPREHENSIVE_STATIC_AUDIT_V2.json](audit/COMPREHENSIVE_STATIC_AUDIT_V2.json): recovered-source hashes, graph, inventories and original obligation mapping.
- [audit/ORIGINAL_STEP3_PLAN.md](audit/ORIGINAL_STEP3_PLAN.md): the agreed original plan, preserved unchanged.

The portable checker in `scripts/check_checkpoint.py` is a static integrity and rebuild-planning tool. It is not a Lean compiler or a mathematical certificate. No successful cumulative kernel build is claimed by this handover.
