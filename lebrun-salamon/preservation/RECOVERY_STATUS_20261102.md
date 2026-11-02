# LeBrun–Salamon preservation checkpoint — 2 November 2026

This catalogue entry records the exact evidence available before Step 3g begins.

## Complete checkpoints

- Step 1: canonical baseline and toolchain evidence.
- Step 2: audited main statement and compiled certificate.
- Step 3a: certified liveness/deletion checkpoint.
- Step 3b: certified source tree, build evidence, and published-input ledger.

## Recoverable later layers

- Step 3c: exactly three modified source files are preserved: `RecompileBasePart05C.lean`, `RecompileBasePart07.lean`, and `RecompileExtensionsPart01.lean`.
- Step 3d: report/status/ledger and an autosave discovery bundle are preserved, but no complete cumulative source overlay was present in the working filesystem.
- Step 3e: the preserved finalizer says `passed = false`; its packaged 129-module tree is byte-for-byte the Step 3b tree because its overlay failed.
- Step 3f: README/status/delivery records are preserved, but the previously claimed cumulative source ZIP was not present.

## Step 3g lineage

Step 3g therefore starts from the certified Step 3b source tree plus the three actual Step 3c source overlays. Missing Step 3d–3f source changes are not silently invented or represented as certified.

## Persistent copies

The complete preservation archive and checksum are stored in the ChatGPT Library at:

- `/Lean formalization checkpoints/LeBrunSalamon_Preservation_Steps1_2_3a_3f_20261102.zip`
- `/Lean formalization checkpoints/LeBrunSalamon_Preservation_Steps1_2_3a_3f_20261102.zip.sha256`

Archive SHA-256: `REPLACE_FROM_MANIFEST`.
