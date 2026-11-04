# Validated current Point1 dependency closure

The dedicated Point1 stage of [run 41763014879](https://github.com/wajcha2/claude/actions/runs/41763014879) passed all **190 selected project modules** at commit `3656bd1c17a200bf9d80edc86f289fb1861ff4d2`: 96 fresh native compilations and 94 strictly validated reuses. There were no failed or blocked modules. Final validation found no changed source, dependency, artifact, or runtime inputs.

The selected closure is derived from the fixed 43 original Step3c–3g obligations, which occur in 19 distinct containing modules. The collector independently bound that manifest and every source file to the committed Git blobs, recomputed the exact selected ancestry, checked the pinned stock compiler/mathlib identity and all direct external artifact hashes, and verified each native receipt, output and diagnostic log. All 190 outputs matched the live source ancestry when collected.

The downloaded artifact is `lebrun-takeover-point1-41763014879-1`, id `13292536046`, 53,505,871 bytes, SHA256 `0854b0be78df30062097584d1e7502ca137008fdb087fb072908321b343469f5`. The exact verification timestamp, per-module source hashes and outputs are in `CI_RECEIPT.json`; current-safe replay entries are in `VALIDATED_SEEDS.json`.

This receipt certifies compilation of the complete selected closure. It does not certify source eligibility of admitted published inputs, the declaration-level 43-root acceptance ledger, or the complete 268-module graph. The workflow continues with that larger graph in a separate stage. In particular, the remaining ConicJets compatibility repairs lie outside this Point1 closure.
