# Immutable point 1 proof checkpoint

## Point 1 checkpoint — 2026-11-03T22:08:02.671367+00:00

This frozen candidate contains **149 Lean source modules and 92 direct `sorry` tokens**. Source token counts are inventories, not counts of accepted published theorems. The immutable target remains byte-identical. The source manifest is `SOURCE.sha256`; the freeze receipt and exact source hashes are in [audit/point1_checkpoint/FREEZE.json](../point1_checkpoint/FREEZE.json).

The latest completed full run, [41714131927](https://github.com/wajcha2/claude/actions/runs/41714131927), checked commit `0e7a654645d92fe82473e358a925b47101305e97`: **97 of 135 modules were accepted for that commit (32 reused with exact receipts and 65 freshly compiled), 5 failed and 33 were blocked**. The final receipt validation invalidated no accepted output. The failures were `LSBranchRamification`, `LSNodalFixedEnds`, `LSConicJets`, `LSClassicalActions` and `LSProductGeometry`; their exact diagnostics are preserved in [audit/ci/41714131927/](../ci/41714131927/). The earlier 12000 MB run 41685948946 completed with 32 passes, a Geometry parser failure and 102 blocked modules. That Geometry compatibility repair subsequently passed.

This candidate includes new proofs and explicit translations for the Step 3c diagonal/projection-formula work, Step 3d fiber-rank work, Step 3e determinant/smooth-cotangent/ampleness work, Step 3f cotangent deformations and dual-thickening normal forms, and Step 3g projective, Laurent and Picard work. Their native helper checks are recorded with their exact tested interfaces. They are **diagnostic proof-development evidence**, not acceptance of the whole current source graph. Compatibility repairs are recorded separately in [audit/ci_compatibility_repairs/](../ci_compatibility_repairs/).

The marked projective-line tangent-to-`O(2)` translation also passed a 14.972 s native diagnostic and an 8.175 s transitive audit excluding the former tangent admission. It is integrated into `RecompileSections`, which now contains no direct `sorry`. The audit retains the five inherited inputs of its tested historical interface; it does not certify the newly edited ancestor graph. See [audit/p1_tangent_build/](../p1_tangent_build/).

The next full CI run attempts every module in this frozen candidate using the stock pinned compiler with a 12000 MB cap. Its only cache source is run **41714131927**. The cache validator checks source bytes, imports, compiler/runtime identity, output hashes and the entire dependency ancestry; it does not reuse the other 85 old-head outputs merely because they once passed. Twelve outputs still match the current full ancestry at this freeze. The driver revalidates the entire selected batch at the end. No result from this new run is assumed in this checkpoint.

**Point 1 (43 obligations across Steps 3c–3g) remains open.** The remaining work includes the actual vector-bundle exactness translations, internal-Hom/fiber maps, diagonal and normalized source calculations, Hom vanishing, and the required native transitive-boundary and affected-graph checks. An exact primary theorem and a proof of each nondefinitional project specialization are required. A newly renamed admission is not a completed obligation.

The conservative accepted floor remains **30/133 = 22.56%, rounded to 23%**. No additional full acceptance unit is claimed for this candidate. The publication-only milestone, frozen endpoint bridge and eight definition validations remain open.

