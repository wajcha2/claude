# Build and resume the accepted LeBrun–Salamon checkpoint

Recovered on **5 November 2026** from immutable Git files and current Actions metadata. **No compiler was run, no Git ref was changed, and no CI was triggered during this handoff audit.** The commands below are recovered instructions, not a new verification result.

## 1. Which snapshot to use

Use accepted commit `11c18cdcb5e92e3975626a6a1276abfe419ad4f8` for the current documentation, **79/133** ledger, 308 production modules and all saved unfinished work. Both canonical and review branches still pointed there at this audit. Its source manifest SHA-256 is:

```text
e48fa8114d0a9eb29d6a8d67442af17a135f64e1160b5936792414b406551998
```

The repository's default branch is `claude/wonderful-fermat-1v76ux`; select the handoff/canonical branch or exact commit explicitly.

The **compiled parent** is `4d1aa547453f50736035a91f6fea81d340359143`. Its production sources are byte-identical to the accepted checkpoint. Reproduce the historical staged Step3h gate in a **separate worktree at that parent**: its baseline guards intentionally require the then-current 74-unit ledger. Running those historical guards directly against the accepted 79-unit ledger fails correctly. Do not downgrade the current ledger or relax the guards.

From an existing clone, including a shallow handoff clone:

```bash
git fetch --no-tags origin 4d1aa547453f50736035a91f6fea81d340359143
git fetch --no-tags origin 80bbb1ce6343260cdba2de6a1d067a3a4e65fd91
git worktree add --detach ../lebrun-native-4d1 4d1aa547453f50736035a91f6fea81d340359143
```

For an integrity check of the accepted checkout:

```bash
cd lebrun-salamon/continuation
sha256sum -c SOURCE.sha256
sha256sum -c CONTINUATION_FILES.sha256
python3 scripts/check_checkpoint.py --root . --verify-manifest --output-dir /tmp/lebrun-static-check
```

The accepted inventory excludes itself and does not list later handoff additions; the handoff has its own inventory. A source ZIP contains the files but not Git history. The staged historical reproduction uses `git show` for the pinned older baseline, so obtain the two commits above in a Git clone for that route.

## 2. Exact runtime and machine requirements

The successful workflow used **Ubuntu 24.04, Linux x86-64, a 16 GiB runner, and one Lean process at a time**. Its tools are Python 3, Git, GitHub CLI (`gh` with authorized Actions-read access), curl, GNU tar and zstd/`unzstd`. Runtime archives require several GiB of download and expanded disk space. The published build is driven by Python scripts; there is no continuation `lakefile` to replace them with a plain `lake build`.

| Item | Exact binding |
| --- | --- |
| Lean | `leanprover/lean4:v4.36.0-rc1` |
| Lean commit | `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e` |
| Official Linux release SHA-256 | `26b3cea1a006ad419215520b8668dcd3f6a9eeba1a123756563a739f9c6274b2` |
| Mathlib revision | `116662aa4c1e9106ab5c609b3214b02f6e11a65a` |
| Mathlib root .olean SHA-256 | `cf4e1b9c97a496d1a653ac6ebe1abfac5b62e8f6a3e442041b5d8845789e09bf` |
| Accepted native runtime fingerprint | `9387025ac24e8fbfc8c41c101ebb879f2345074bbb8683f5b65951d1f5cb8004` |

`scripts/restore_ci_runtime.py` restores the official compiler, mathlib cache, full IR and eight package dynamic libraries, checks their pinned hashes and writes the runtime configuration. Its **effective native flags** are:

```text
--json -j1 -DElab.async=false -M12000 -DmaxErrors=1000 -DmaxHeartbeats=2000000
```

The unchanged historical `TOOLCHAIN.lock.json` records `-M5400`; the older restricted local diagnostic runtime used `-M7200` and an executable-path adapter. These are distinct contexts. Follow the reviewed runtime recipe and receipts; do not overwrite the lock, relabel adapter results as native, or rewrite cache keys. Normal Linux/CI reproduction uses the stock frontend without the local adapter. Its older recipe is retained under `audit/runtime/` and `audit/local_recovery_20261104/` only if needed for that restricted environment.

## 3. Reproduce the historical native stages

The exact authoritative recipe is repository file `.github/workflows/lebrun-3h-continuation-native.yml`. The accompanying [REPRODUCE_COMPILED_4d1.sh](REPRODUCE_COMPILED_4d1.sh) transcribes its shell steps with task-specific `LEBRUN_NATIVE_TEMP` / `LEBRUN_NATIVE_WORKSPACE` variables and substitutes `gh run download` for the two Actions download steps; it performs **no artifact upload or GitHub dispatch**. It is a reference script, not newly executed build evidence.

After entering the fresh `../lebrun-native-4d1` worktree, run that script by its absolute path. It:

1. Materializes the pinned 307-module Point1 source baseline from commit `80bbb1ce...` and checks the combined source plan.
2. Restores the stock runtime at its native path `/home/runner/work/_temp/lebrun-runtime`.
3. Downloads and verifies the baseline and exact historical resume artifacts, including the original native type capture.
4. Restores the 105 eligible current contexts and excludes the failed Geometry result.
5. Runs the nine stages: `part07_parents`, `part07`, `core`, `geometry_parents`, `geometry`, `accepted_boundaries`, `smooth_descent_parents`, `smooth_descent`, `full`, with the current-root audit between the boundary and SmoothDescent stages.
6. Writes the complete report to `continuation-evidence/FULL_CONTINUATION_VERIFICATION.json`.

The only 600-second exceptions are the isolated `RecompileBasePart07`, `RecompileExtensionsPart04Geometry` and `LSFamilySmoothDescent` checks, after their parents have passed. All other module limits are 300 seconds. The workflow's job limit is 120 minutes. It preserves early core/boundary artifacts on CI. Do not grant a longer allowance to an entire import closure or change heartbeat flags to conceal a proof error.

For a new local source attempt, the reusable driver interface is:

```bash
python3 "$CONTINUATION/scripts/replay_checkpoint.py" \
  --root "$CONTINUATION" --runtime-config /absolute/path/runtime-config.json \
  --build-dir /absolute/path/new-build --module ActualModuleName --timeout 300
```

It automatically includes project ancestors and validates source/import/output/runtime/recursive-dependency hashes. A fresh runtime at different absolute paths has a different identity: native cache reuse can correctly be rejected. Use the existing strict validators, not manual receipt edits. Adapt the reviewed staging/acceptance plan for a new candidate; the historical Step3h plan and reports are evidence, not authorization to credit later work.

## 4. Available official artifacts

Read-only GitHub metadata checked on 5 November 2026 reports every artifact below unexpired. Full IDs, names, sizes, ZIP digests and retention dates are in [ARTIFACT_AVAILABILITY.json](ARTIFACT_AVAILABILITY.json). This audit did not redownload the binary ZIPs.

| Purpose | Run / artifact | Retention shown by GitHub |
| --- | --- | --- |
| Current 308-module native outputs and complete audit | run `41912044307`, artifact `13366173425`, `lebrun-3h-current-native-41912044307-1` | 2 February 2027 |
| Point1 baseline required by historical reproduction | run `41888465259`, artifact `13353190843` | 2 February 2027 |
| Historical 105-context resume packet | run `41902480321`, artifact `13360788893` | 2 February 2027 |
| Mathlib cache: 12 parts + manifest | run `41234129669`, pattern `mathlib-cache-*` | 29 January 2027 |
| Full IR: payload + manifest | run `41309680327`, pattern `mathlib-full-ir-*` | 30 January 2027 |
| Package native libraries | run `41440059394`, artifact `13141100538` | 31 January 2027 |
| Optional exact official Lean split archive | run `41234129521`, pattern `lean-toolchain-*` | 29 January 2027 |

Retrieve the current output tree without starting CI:

```bash
gh run download 41912044307 --repo wajcha2/claude \
  --name lebrun-3h-current-native-41912044307-1 --dir native-artifact
```

The **original ZIP** is 179,280,815 bytes, SHA-256 `aa96014256646d209d710f8b32e98ab61991c0a9c5d1020b38a66876b3e60f3d`. Preserve that raw ZIP when using the archived independent verifier: `gh run download` extracts it, so the ZIP checksum is not a checksum of the extracted directory. A GitHub artifact-download client can retain the original ZIP by ID. The original Lean release URL and every runtime archive checksum are in `restore_ci_runtime.py`; the optional split-Lean artifacts contain the same official archive bytes.

## 5. What survived, and reconstruction limits

The Git checkpoint contains the complete 35-group /126-file unfinished index, all its exact referenced blobs, the final publication reviews, scripts and previous failures. All 126 unfinished-file Git identities and inventory hashes were checked again for this handoff. The latest known work from this audit agent requires **no additional detached proof blob** to be saved.

`audit/step3h_acceptance_41912044307/FULL_NATIVE_TEXT_AND_AUDIT_EVIDENCE.json` is a lossless gzip/base64 JSON envelope containing **964 files**: receipts, raw streams, reports and both generated audit sources/outputs. Its decoded payload SHA-256 is `38e1789c4428a52e264bf284030b0b80d9770dac6a345879df83e5af74571d08`. It does not contain the production-module binary cache or the large runtime; retrieve those Actions artifacts separately. Evidence envelopes in the unfinished groups may use gzip or XZ; their individual encoding and per-file hashes are explicit.

The original post-publication scratch-only `FINAL_PUBLICATION_READBACK.json` (SHA-256 `9bc39cc5dc54a80ffe9194c5ba7251bde0c04dd045277aa3c06bf2a3a9e08fb9`) was not an attached Git file. Its role was administrative ref/tree readback, not a proof result. The new [CHECKPOINT_VERIFICATION.json](CHECKPOINT_VERIFICATION.json) reproduces the current checks without claiming to recover those old bytes.

The archived `official/VALIDATION_INPUT_FINAL.json` inside the native text envelope contains old absolute scratch paths. Its two standalone metadata inputs (`IMMUTABLE_GIT_BINDING_4d1aa547.json` and `PINNED_AUDIT_EXTERNAL.json`) are not present under those standalone names in the committed tree. A successor can regenerate the former from the immutable compiled Git tree and the latter from the official Lean archive; the unchanged V3 verifier checks those Git identities and the pinned `Lean.Util.CollectAxioms` hash `60556ab5263a908aa74a5e65620b5e957cac3846aa6e4f05414434b8c12ea7de`. Rebind filesystem paths to a fresh extraction directory, retaining all source/runtime/evidence hashes. The completed historical independent report itself is attached and remains available.

The accepted ledger is unchanged by any of these recovery steps. Helpers, local compilations and source proposals earn no units until their exact current-source/native/publication gates pass.
