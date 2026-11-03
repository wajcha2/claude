# Full 135-module replay: 19 passed, Part07 failed, 115 blocked

[GitHub Actions run 41682674689](https://github.com/wajcha2/claude/actions/runs/41682674689) checked commit `7b624261fff0a5eda25b14a035d637e238e3454a`, tree `7b38e09c0b00482522b1f83c483650b3f1542608`, and finished with failure at 17:32:51 UTC on 2026-11-03. The exact tree contains 135 project Lean source modules. The workflow selected all modules, used stock Lean 4.36.0-rc1 and the pinned mathlib runtime, and supplied no historical artifact seeds.

## Result and scope

Nineteen modules compiled freshly and produced verified outputs. `RecompileBasePart07` failed with return code 1 after 227.492 seconds. The remaining 115 modules were blocked through their dependencies. They were not individually compiled by this run. The full graph and the mathematical milestone remain unverified.

The passing source hashes match the current continuation source when this receipt was created. All 19 output hashes were independently checked after downloading the artifact, and final replay validation reported no invalidated accepted module or changed runtime fingerprint. This is a compilation result for a subset of the graph; the ratio 19/135 is not a mathematical milestone-completion percentage.

| Freshly passed module | Compiler seconds |
| --- | ---: |
| FieldDifferentials | 1.819 |
| LSConeDiagonal | 4.876 |
| LSConePole | 4.024 |
| LSCurveLaurentStandardInputs | 1.317 |
| LSNilpotentTopology | 1.418 |
| RecompileBasePart01 | 29.283 |
| LSConeArcs | 3.172 |
| LSLaurentRescaling | 3.322 |
| LSMilestoneStatement | 4.529 |
| RecompileBasePart02 | 16.005 |
| LSConeLocalization | 3.322 |
| LSMilestoneTopology | 3.072 |
| RecompileBasePart03 | 109.447 |
| RecompileBasePart04 | 132.694 |
| RecompileBasePart05A | 31.84 |
| RecompileBasePart05B | 47.921 |
| RecompileBasePart05C | 87.816 |
| RecompileBasePart05 | 2.923 |
| RecompileBasePart06 | 38.507 |

## First failure

The first diagnostic is `(kernel) excessive memory consumption detected` at `RecompileBasePart07.lean:264:8`, in `affineStructureKernelIso_hom_ι`. Subsequent memory errors occur at lines 289, 348, 379, 387, 395 and later. The compiler configuration used `-M7200`.

The module reports 54 errors: 27 memory-cap diagnostics and 27 other diagnostics. These later errors include unknown declarations (`infinityNormalizedFrames`, `pointIdealOverlapOneFrame`, `homLine`), missing instances, universe/type mismatches and an unsolved goal. They occur after earlier declarations failed. Their independence from the memory failure has not been established. `ERRORS.json` preserves every exact diagnostic, and the original JSONL log is retained under `kernel-evidence/logs/`.

The compiler exited normally with return code 1 and empty stderr; this was not an observed operating-system kill. A resource-sufficient replay is needed before diagnosing the later messages as separate proof defects. No proof source or workflow was changed during this CI audit.

## Reusing the successful ancestry

`VALIDATED_SEEDS.json` contains all 19 passing modules, with no excluded candidates. Each seed verifies current source/import hashes, its output hash, the full project ancestor chain, the toolchain lock, and direct external artifact hashes against the current local runtime. Provenance identifies this exact stock-compiler CI run and archive. The replay driver accepts it through `--seed-receipts`; selecting `--module RecompileBasePart07` then reuses the validated successful ancestors.

The seed file references downloaded `.olean` files under the local extracted directory recorded in `CI_RECEIPT.json`. Large binaries are not copied into this evidence directory. They remain available in GitHub artifact `13254717942` (12,618,690 bytes), whose verified ZIP SHA-256 is `17277e26c74e56214945c3afbd35c7b7a85026d26b3c0393c48a0fdc9033a1dd`.
