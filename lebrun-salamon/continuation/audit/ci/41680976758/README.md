# Successful stock compiler CI replay — 2026-11-03

[GitHub Actions run 41680976758](https://github.com/wajcha2/claude/actions/runs/41680976758) completed successfully at 17:08:35 UTC for commit `194d98fd9e8bfcd014a9578dd10bfabe74f05cf1` on `codex/lebrun-takeover-audit-20261103`.

The runtime was restored from pinned archives. This runner used stock Lean 4.36.0-rc1 without the local executable-path adapter. Mathlib revision: `116662aa4c1e9106ab5c609b3214b02f6e11a65a`. The selected targets were `LSNilpotentTopology` and `LSMilestoneTopology`.

| Freshly compiled module | Return code | Compiler elapsed time |
| --- | ---: | ---: |
| LSNilpotentTopology | 0 | 1.518 s |
| RecompileBasePart01 | 0 | 40.160 s |
| LSMilestoneStatement | 0 | 5.032 s |
| LSMilestoneTopology | 0 | 3.274 s |

All four output hashes were independently checked after downloading the artifact, and all four source hashes matched the current local continuation sources when this receipt was created. Final replay validation found no changed source/dependency/runtime files and no invalidated modules. `full_selected_graph_passed` is true for this four-module selection. `milestone_met` remains false. This run does not compile the remainder of the cumulative proof, the first-jet integration modules, or `LSMilestoneTarget`.

The downloaded artifact ZIP has SHA-256 `cb8c64b98b891e8e9a46afae0b68946e8adb35d708a42bc35844a5ed56dec134`, matching GitHub's artifact digest. Artifact ID: `13251659826`; artifact size: 2,195,392 bytes. The actual `.olean` files remain in the local extracted artifact directory recorded by `CI_RECEIPT.json`; this checked-in evidence directory preserves the small metadata, receipts and logs.

There were no compiler failures in this run. The job log contains a nonblocking GitHub Actions warning that the v4 checkout/upload actions target Node.js 20 and were run under Node.js 24. No workflow or runtime change is required by this successful result.
