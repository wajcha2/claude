# Full current replay: 240 accepted, two failed

Run: https://github.com/wajcha2/claude/actions/runs/41763014879

The completed run checked immutable commit `3656bd1c17a200bf9d80edc86f289fb1861ff4d2`, with 268 project source modules and the unchanged frozen theorem target. Independent validation accepted **240 modules**, with **two failed and 26 blocked**. Final validation found no changed source, artifact, dependency ancestry, or runtime inputs. All 240 accepted outputs matched the live source ancestry when collected.

Across all stages of this run, 138 modules compiled natively and 102 were restored from the prior run with strict complete-ancestry checks. The final stage alone records 40 fresh compilations and 200 reuses because it also reused the successful earlier stages in this same run.

The two failed modules are `LSConicJets` (eight diagnostics, including kernel memory consumption at the identity-contact velocity specialization) and `LSScaledVelocities` (four API/transport diagnostics). `ERRORS.json` contains the exact native errors and `CI_RECEIPT.json` identifies every source/output hash and receipt. Later Conic repairs have separate scoped evidence and do not retroactively change this result.

The dedicated Point1 stage passed all **190 modules** in the complete ancestry of the fixed 43 Step3c–3g obligations (19 distinct containing modules). Its manifest was independently bound to the Git tree and its evidence is retained in `point1/`. The earlier Ext01 and changed Geometry closures are retained under `early_ext01/` and `early_geometry/`. The failed Conic/Scaled modules and their blocked descendants are outside the selected Point1 closure; the original plan's additional reverse-dependency acceptance gate remains open. The declaration-level boundary and publication-eligibility audits are separate evidence.

The compiler was the pinned stock Lean frontend with the recorded mathlib revision, a 12000 MB cap and a 900-second per-module wall limit. The full artifact is `lebrun-takeover-kernel-41763014879-1`, id `13292737548`, 60,193,992 bytes, SHA256 `9d6811b8c7d07e3d1c2469e97752dba4a623136ad549da46535f4eb759ea1035`. Its digest, runtime identity, exact Git source set, native logs, output bytes, dependency keys and recursive ancestry stamps were independently checked.

The full graph and the published-theorem-only milestone are not accepted by this receipt.
