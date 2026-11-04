# Validated unselected cache reuse

This change retains selected-module-only restoration by default. An explicit `include_validated_unselected_cache` input permits revalidation of a native receipt omitted from the latest selected run only when the same official artifact contains a completed strict cache-union binding for it.

The additional path requires the completed union's exact runtime fingerprint and final validation flag, source/output/recursive-stamp bindings, and matching native receipt provenance. Every existing native receipt, current source/import/dependency/runtime, artifact/log hash and recursive ancestry check still applies. Explicit failed or blocked run entries never fall back to the cache. The union performs the unchanged final source, runtime, output, receipt and dependency rehashes.

The 20-case fixture includes the prior ten integrity checks and ten focused eligibility cases. The real official archive restored 101 modules under the unchanged default and 274 under the explicit mode. All 274 original native receipt bytes matched the official ZIP, and all native keys/output/log/recursive stamps matched the preserved union, including all 190 audited Point1 ancestors. No compiler was invoked by this validation, no local diagnostic runtime key was accepted, and the acceptance ledger remains unchanged.

`VALIDATION.json` binds the exact archive digest, current source manifest, complete comparison and test results. `WORKSPACE.json` records the read-only byte mirror used to validate the original stock runtime paths. The first production use remains subject to the ordinary stock CI cache and native-stage checks.
