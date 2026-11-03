# Current-source contact determinant boundary

The existing determinant dependency walker passed against the freshly compiled current-source CI artifacts, with exit code zero in 32.825 seconds. No theorem source was edited. No historical baseline project artifacts were on the search path.

## Scope upgrade and dependency validation

The determinant cone is now checked against its actual current ancestors, compiled by pinned stock Lean in CI run **41682674689**, source commit `7b624261fff0a5eda25b14a035d637e238e3454a`. The five project modules on this cone are Part01 through Part05A; the other imported dependencies come from the pinned Mathlib/Lean runtime. This strengthens the earlier baseline-interface diagnostic. It does **not** establish that the full LeBrun–Salamon graph passes or that its published-theorem-only milestone has been met.

For every project ancestor, this audit independently checked current source hashes, exact import lists, CI output hashes, original receipt hashes, direct dependency hashes, and the current toolchain lock against `VALIDATED_SEEDS.json`. External direct artifacts were checked against the pinned local runtime. The audit's direct Part05A import hash equals the newly compiled CI Part05A artifact hash. All five project artifact files were fingerprinted by the runner before and after the audit. A second source/artifact hash check after success found no changes.

The runtime configuration uses only the fresh CI olean directory plus the pinned Mathlib/Lean roots; the runner overwrites inherited `LEAN_PATH`. `CURRENT_ANCESTOR_VALIDATION.json` records the evidence.

| Current project module | Source SHA-256 | CI olean SHA-256 |
| --- | --- | --- |
| `RecompileBasePart01` | `46d783aa22de8543b21fe79accb874576a18c8fe68ffbf717a7e86f5dbce61bf` | `a9f3c384ac4831b59f8d005fd2b08345219ca0c0e832eec50f90e806f07dab74` |
| `RecompileBasePart02` | `2948effe75d3a6933119fe5e5b6e432f7bc273d020ce1056017313acc72c06f7` | `8f050b44735d9d4b4afe537a976aabf2364d9eb2f34c39e8c738299f7922ec21` |
| `RecompileBasePart03` | `44e6f996c575e9de863f2cad7063eea49b03f7aebb4d7b57b30e11d52f8ae228` | `37d2f48e206753e3efd299b660f9ee142662f0ba4139b938d4ced946966e72e3` |
| `RecompileBasePart04` | `fef347742972b6c8bd206648e25de31e98d980006400923e79782883d1ab5308` | `b2949fdabd3adb19db69cc8070275978908397e5209c7f20cffa8fbb249d2cd3` |
| `RecompileBasePart05A` | `7e6497b17a33f6b700418f118b45624833c7f8407a989e685813cb648fe9cf05` | `5ecc5bae10083aa752ab572247acf972b85c878f35407f38dd2ec26f261a9818` |

## Native closure result

The unchanged walker body traverses every imported constant's type, definition/theorem/opaque value, and inductive constructors. It includes nonproject recursion and records shortest paths with a breadth-first queue.

| Item | Result |
| --- | ---: |
| All constants visited | 41996 |
| Project constants visited | 632 |
| Direct uses of `sorryAx` | 5 |
| Missing constants | 0 |
| Custom project axioms | 0 |

## Exact current admitted leaves

- `LeBrunSalamon.PublishedInputs.Step3e.alternatingDiscriminantTrivial`
- `LeBrunSalamon.PublishedInputs.SheafFunctoriality.exterior_locallyFree`
- `LeBrunSalamon.PublishedInputs.SheafFunctoriality.exteriorPresentation`
- `LeBrunSalamon.PublishedInputs.Step3e.smooth_cotangent_rank`
- `LeBrunSalamon.PublishedInputs.SheafFunctoriality.cotangentPresentation`

The smooth-cotangent-rank obligation now appears under the current `PublishedInputs.Step3e.smooth_cotangent_rank` name, reached through the proved project API alias. The full native types and shortest paths of all five leaves are retained in `DETERMINANT_DEPENDENCY_NATIVE_OUTPUT.txt` and `DETERMINANT_DEPENDENCY_SUMMARY.json`. Naming a leaf here does not independently certify its publication translation.

## The false original input remains absent

```text
OLD_FALSE_PUBLISHED_INPUT name=LeBrunSalamon.PublishedInputs.Step3e.symplecticDeterminant present_in_environment=false present_in_closure=false
```

The new proved `PhaseTwentySeven.symplecticDeterminant` wrapper explicitly includes alternation in its native printed type. The repaired contact determinant reaches the new alternating-discriminant leaf through this wrapper.

## Preserved evidence

- `receipt.json`: successful native audit receipt.
- `RUN_STATUS.json`: successful run and unchanged final fingerprints.
- `CURRENT_ANCESTOR_VALIDATION.json`: independent pre/post source, artifact, receipt and dependency checks.
- `CI_VALIDATED_SEEDS.json`: the supplied CI provenance manifest, preserved unchanged.
- `RecompileBasePart*.ci.receipt.json`: the five original CI ancestor receipts.
- `runtime-config.json`: exact isolated runtime/search-path configuration.
- `LSSymplecticDeterminantDependencyAudit.lean`: executed audit; only the scope comment differs from the validated diagnostic.
- `DETERMINANT_DEPENDENCY_SUMMARY.json`: structured current boundary.
- `DETERMINANT_DEPENDENCY_NATIVE_OUTPUT.txt`: complete native printed output.
- `DETERMINANT_PROJECT_CLOSURE.txt`: all 632 project declaration names.

Earlier baseline-interface diagnostics and all first-jet evidence were preserved separately in `audit/proof_batch_build/`.
