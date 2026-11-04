# Full source replay 41732181431: completed

The stock pinned Lean compiler checked immutable commit `cdf4d8a5ae81407900431d905634c97bae4c9996` with a 12000 MB memory cap. The run completed on 2026-11-03 at 23:10 UTC with **121 accepted modules, 4 failed, and 30 blocked**, out of all 155 selected source modules. The accepted count comprises 28 strictly validated cache reuses and 93 fresh native compilations. The full graph did not pass.

The completed artifact was downloaded and its SHA256 verified as `c131a87581f0ba183a6ed5c6464ffe9ca506d0ce871c6380d19976d02fa3bc48` (49,384,148 bytes). Every accepted receipt was rechecked against the immutable source, exact imports, dependency output hashes, pinned compiler/library files, diagnostic logs, and final source/ancestry validation. No input or runtime invalidation was reported.

Fresh passes include RecompileSections, Ext01–Ext04Geometry, LSHomVelocity, LSNodalTangent, LSNodalFixedEnds, and the completed epsilon/Hom/family helpers included in this commit. The four failed modules are:

- `LSConicJets`: 32 diagnostics, including the reducibility-attribute issue subsequently repaired in the live source, dependent coercion/rewrite failures, one memory diagnostic, and one heartbeat diagnostic.
- `LSRelativeDifferential`: 4 proof/transport diagnostics.
- `LSStandardConicDifferential`: 22 diagnostics, beginning with the reserved `section` identifier and unqualified tensor-pullback comparison.
- `LSProductGeometry`: a doc-comment/option placement parser error and a 6,000,000-heartbeat limit.

`ERRORS.json` preserves all 60 original compiler diagnostics. The precise source, per-module status and cache provenance are recorded in `CI_RECEIPT.json`, `RUN_STATUS.json`, the receipts and logs.

The live working tree has later nonvanishing and exactness changes that are absent from this immutable commit. At validation time, only **30** outputs retained both identical live source and fully unchanged live ancestry; these alone appear in `VALIDATED_SEEDS.json`. The larger 121-module frozen-head artifact is useful for isolated compatibility diagnostics and does not certify those later live changes. Full Point 1 and milestone acceptance remain pending.

[GitHub Actions run](https://github.com/wajcha2/claude/actions/runs/41732181431)
