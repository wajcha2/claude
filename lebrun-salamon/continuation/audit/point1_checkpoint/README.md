# Immutable point 1 follow-up checkpoint

## Point 1 checkpoint — 2026-11-03T22:34:09.806987+00:00

This immutable candidate contains **155 Lean modules and 92 direct `sorry` tokens**. Counts of source admissions do not certify their published-theorem eligibility. The frozen target and toolchain lock are unchanged. `SOURCE.sha256` and [audit/point1_checkpoint/FREEZE.json](../point1_checkpoint/FREEZE.json) identify the exact candidate.

The latest full replay, [41728791345](https://github.com/wajcha2/claude/actions/runs/41728791345), checked commit `6fa6ee1a25735be73e73be455aed94ad88eae8e1` with all 149 modules selected. It accepted **29 modules (12 strictly reused and 17 freshly compiled), failed 1, and blocked 119**. Its sole source diagnostic was the unqualified `structureModule` name in `LSPublishedPicard.lean`. This candidate qualifies that name as `PhaseTwentyFive.structureModule`; the next replay checks the repair. No accepted Sections or Ext01 output was produced by that run.

Every accepted source, import, dependency output, compiler/runtime fingerprint, output artifact, diagnostic log, and cache provenance was validated against the committed source. Fresh passes include Base04, Base05A/B/C, Base06 and Base07, so their integrated proof translations now have evidence in that source ancestry. The final validation reported no invalidation. Detailed receipts and exact failure evidence are in [audit/ci/41728791345/](../ci/41728791345/).

This checkpoint additionally includes the completed native diagnostic proofs for the epsilon/Hom-vanishing sequence, the arbitrary-affine relative derivation wrappers, and the projective-line family-degree translation. Their exact tested sources and inherited assumptions are recorded in `audit/STEP3F_HOM_VANISHING.json`, `audit/STEP3F_AFFINE_RELATIVE.json`, and `audit/p1_family_degree_build/`. These integrations still require their actual containing modules and current dependency graph to pass. Unchecked off-graph drafts are excluded.

The next full stock-compiler replay selects all 155 modules with a 12000 MB cap. Its sole cache source is run **41728791345**. The source/runtime/dependency validator permits only **28** ancestry-safe outputs at this freeze; the subsequently edited affine-derivation module is excluded. The replay revalidates the entire selected graph at completion. No result from this next run is assumed.

**Point 1 remains open:** all 43 original obligations across Steps 3c–3g still require the stage acceptance gates, including exact primary statements, proofs of nondefinitional project specializations, and the affected source/dependency replay. Actual pullback/fiber exactness, Hom/base-change and total-space transports, diagonal calculations and normalized source work continue outside this frozen candidate where unfinished. Historical run 41714131927 accepted 97 modules at its own older head; those outputs are not current-source acceptance.

The conservative accepted floor remains **30/133 = 22.56%, rounded to 23%**, with no additional full acceptance unit credited in this checkpoint. The published-theorem-only milestone and the frozen endpoint bridge remain open.

