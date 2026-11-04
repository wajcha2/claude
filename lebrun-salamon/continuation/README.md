# LeBrun–Salamon formalisation: continuation

**Status on 4 November 2026: working candidate; the published-theorems-only milestone is not met.**

The conservative acceptance-checklist completion floor is **30/133 = 22.56%, rounded to 23%**. This counts fully accepted items from the agreed plan and records newer proof work separately; it does not estimate mathematical effort or time remaining. See [the fixed ledger](audit/MILESTONE_PROGRESS.md).

This directory contains the actual source recovered from the cumulative Step 3g V2 checkpoint, the frozen Step 2 target, and the takeover audit. The original recovery commit is `d8749550ace47a9186fcc1d8c2a38fa81d8b3ba0`; it preserves all 129 recovered source modules byte for byte. Subsequent changes are explicit descendants of that commit.

Start with **[TAKEOVER_PLAN.md](TAKEOVER_PLAN.md)**. Machine-readable current status is in [TAKEOVER_STATUS.json](TAKEOVER_STATUS.json).

The earlier completion announcements for Steps **3c, 3d, 3e and 3f** are preserved in the plan. The current native and publication boundary has now passed for all **43 Steps 3c–3g obligations**, plus the inherited affine-projection theorem. The original required reverse-dependency compilation gate remains open; it is distinct from the historical recovery certificate questions.

## Current targeted smoothing replay

Frozen `2026-11-04T04:04:55.242417+00:00`: this narrow checkpoint preserves the checked `LSVelocityAdditionFamily` repair (`c04edfdb2d6936c0cada7ab90e8aa8e296be0bb85ef491fee50a643fe158cbb7`) and its complete native30.362-second receipt. It changes one source from d660456c; all268 source files match the working graph at this freeze, and the target is unchanged. The next remote run selects only the120-module ancestry of `LSSmoothingAssembly`, reusing116 independently validated outputs from the preceding early smoothing artifact. It uses the same stock pinned compiler,12000 MB cap and900-second per-module limit. It deliberately leaves the unchanged Conic failure to its separate ongoing repair and full replay.

The remaining fresh modules are VelocityAdditionFamily and its three downstream smoothing modules. The first is locally checked; the next hit a30-second local wall cap without diagnostics. No future cloud result is assumed. The43+1 native/publication boundary remains preserved; the required reverse-cone gate is open and accepted progress remains30/133. The earlier full-checkpoint record below remains historical evidence, not a claim that this targeted run selects the entire graph.

## Point 1 checkpoint — 2026-11-04T03:38:48.057058+00:00

**The proof and publication boundary is checked for all 43 original Steps 3c–3g obligations; the required current reverse-dependency compilation gate is still open.** The separately inherited affine-projection obligation OBL-069 is also checked. This checkpoint adds no accepted checklist units before the original plan's complete gate passes.

This immutable candidate contains **268 Lean modules and 99 direct `sorry` tokens**. The frozen target and pinned toolchain lock are unchanged. `SOURCE.sha256` and [the source freeze](audit/point1_checkpoint/FREEZE.json) identify the exact candidate. Neither helper counts nor admission-token counts measure completion or establish publication eligibility.

### Current native and source evidence

The dedicated Point1 stage of [CI 41763014879](https://github.com/wajcha2/claude/actions/runs/41763014879) passed **190/190 modules**: the 19 distinct containing modules for the fixed 43 obligations and their complete project ancestry. All source files, dependency outputs, logs, compiler/runtime identities and final ancestry checks were independently validated. [The Point1 evidence](audit/ci/41763014879/point1/README.md) records its exact scope.

The exhaustive declaration audit then checked **43 original roots plus OBL-069**, with **50 distinct actual admitted inputs**. Every actual leaf passed the independent primary-source/hypothesis/map review and is bound to its native type, source, output and ancestry hashes. No original project conclusion remains directly admitted in this audited boundary; no missing constant or unexpected project/global axiom was found. The old project-specific `TotalLine.projection_affine` admission is absent. Its actual theorem now reaches the precise generic affine section-representability input. See [the complete acceptance preparation](audit/point1_acceptance_current_20261104T031351/README.md) and [the source-eligibility ledger](audit/POINT1_PUBLISHED_LEAF_ELIGIBILITY.md).

The 29-root native tranche was carried forward only after all of its recorded ancestor source/output/import/dependency stamps and artifact bytes matched the same 190-module snapshot; the remaining 14 roots and OBL-069 were checked natively against that snapshot. All 44 original public headers match the certified baseline after comments and whitespace are removed, and the 15 changed-tranche native signatures are retained with their stated scope. These checks do not claim a new historical-baseline rebuild or completion of the separate definition-validation obligations. At this freeze, the entire 190-module source/output/ancestry binding was rechecked again in [POINT1_BOUNDARY_AT_FREEZE.json](audit/point1_checkpoint/POINT1_BOUNDARY_AT_FREEZE.json).

| Batch | Original obligations | Native proof and publication boundary | Acceptance |
| --- | ---: | --- | --- |
| 3c | 6 | Passed | Required reverse cone pending |
| 3d | 11 | Passed | Required reverse cone pending |
| 3e | 7 | Passed | Required reverse cone pending |
| 3f | 11 | Passed | Required reverse cone pending |
| 3g | 8 | Passed | Required reverse cone pending |
| Separate OBL-069 | 1 | Passed | Required reverse cone pending |

### Remaining compilation gate

The latest full replay checked commit `3656bd1c17a200bf9d80edc86f289fb1861ff4d2` with all **268 modules** selected. It accepted **240**, with **2 failed and 26 blocked**. Across all stages of that run, 138 modules compiled natively and 102 came from the strictly validated prior cache. The final stage reports 40 fresh builds and 200 reuses because it also reused the earlier stages of the same run. Final source/runtime/ancestry validation found no invalidations. The failed modules were `LSConicJets`, `LSScaledVelocities`; [the full CI evidence](audit/ci/41763014879/README.md) preserves their exact diagnostics and all successful receipts.

This is the remaining acceptance gate for Point1: compile the changed modules and their required current reverse-dependency cone. The original plan explicitly requires it, even though the selected 190-module proof boundary already passes. The recorded Conic failure includes an expensive kernel conversion at the identity-contact velocity, along with compatibility rewrites; the scaled-velocity failures are explicit map/carrier/rewriting mismatches. Later checked compatibility repairs in this candidate retain their own exact evidence and do not retroactively change the recorded CI result. Off-graph unverified drafts are excluded from the source graph.

The next stock-compiler replay selects all **268 modules**, with a 12000 MB memory cap, a 900-second per-module limit, and run **41763014879** as its sole cache source. Full source/import/lock/output/ancestry checks permit **240** previous outputs at this freeze. It first checks the LSSmoothingAssembly closure, including the repaired scaled-velocity branch, and uploads that separate diagnostic artifact. It then preserves separate Ext01, Geometry and fixed-Point1 artifacts before the full graph, and revalidates the entire selected graph at completion. No result from that future run is assumed.

### Current execution order and accounting

Finish the outstanding compatibility repairs, replay the complete required reverse cone, and bind its successful artifacts to the already completed 43+1 native/publication audit. Only then can the parent-controlled fixed ledger promote the original obligations. Continue the remaining batches and the frozen endpoint/definition-validation work under the existing plan after that gate; the stronger Wolf-homothety endpoint and the whole published-theorems-only milestone remain open.

The conservative accepted floor remains **30/133 = 22.56%, rounded to 23%**. This is a count of fully accepted checklist units, not mathematical effort, elapsed time or the proportion of compiled modules. The completed 43-root proof/publication work is recorded substantively without bypassing the original reverse-cone gate.

## Findings at the takeover audit

- The recovered archive has SHA-256 `722c44bc3e21211634732fc92fb0d598b429f886ac85dec3d3699318d4a3fe32`.
- At the initial takeover, the last recorded passing incremental stage was Step 3b: eight wrappers discharged to its recorded published-input boundary, with 91 further proof/refactoring obligations. This was not a complete clean build of the final theorem.
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
