# LeBrun–Salamon formalisation — Step 1 canonical baseline

Frozen and verified on **1 November 2026**.

## Result

**STEP 1: PASSED**

The **strict published-input candidate v7** is the sole forward source tree. The **Stage 3 integrated master v20** is preserved separately as an immutable compilation reference and regression oracle. No source file is overlaid between these trees.

## Frozen environment

- Lean `v4.36.0-rc1`, commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`
- Lean Linux release SHA-256 `26b3cea1a006ad419215520b8668dcd3f6a9eeba1a123756563a739f9c6274b2`
- mathlib `116662aa4c1e9106ab5c609b3214b02f6e11a65a`
- `Mathlib.olean` SHA-256 `cf4e1b9c97a496d1a653ac6ebe1abfac5b62e8f6a3e442041b5d8845789e09bf`
- Strict flags: `--json -j1 -DElab.async=false -M7200 -DmaxErrors=1000 -DmaxHeartbeats=2000000`

GitHub Actions run `41296866387` independently checked out the exact mathlib revision, checksum-verified the exact Lean release and root olean, completed `lake build` with 18,167 jobs, and passed direct and Lake-based `Mathlib` import checks.

## Canonical source provenance

- Strict v7: 129 modules; 207 project import edges; acyclic graph.
- Strict source hashes differing from the archived build plan: 0.
- Independently parsed import lists differing from the archived plan: 0.
- Strict archive manifest entries verified: 2,411.
- Compiling-reference archive manifest entries verified: 50.
- Forward-source policy: no silent cross-tree copying; any later transfer from v20 must be an explicit patch with before/after hashes.

## Clean compilation reference

The unchanged v20 integrated source, SHA-256 `5169c1ddea312c0bb9628b309bcd45f5afe7526b5118e6a1ea32eb1d416318ba`, was compiled directly in the frozen environment from a fresh output directory.

- Return code: **0**
- Started: `2026-11-01T10:50:17Z`
- Finished: `2026-11-01T11:03:57Z`
- Output olean SHA-256: `03bb807e6f655b5a817b682fdec7c10c7d1582ac8f97e2c85079b4b28ae6fdf7`
- Output bytes: `24311320`

This independently confirms the earlier archived clean `lake build` success.

## Strict v7 failure frontier

The unchanged five root snapshots were recompiled against 73 dependency artifacts, each hash-matched to the archived receipts. Exactly the documented five roots failed; no native-runtime failure occurred:

- `LSBranchRamification`: rc 1; errors 7 (archived 7); exact diagnostics: **true**
- `LSNodalFixedEnds`: rc 1; errors 84 (archived 84); exact diagnostics: **true**
- `LSConicJets`: rc 1; errors 52 (archived 52); exact diagnostics: **true**
- `LSClassicalActions`: rc 1; errors 4 (archived 4); exact diagnostics: **true**
- `LSProductGeometry`: rc 1; errors 1 (archived 1); exact diagnostics: **true**

All five diagnostic streams match the archived JSON diagnostics exactly.

The 32 blocked modules are exactly the reverse-dependency closure of these five failed roots, excluding the roots themselves.

## Admission boundary at this freeze

Strict v7 has 121 direct admissions; all 121 match approved exact source records. The source reconciliation reports zero unapproved direct admissions and zero unassociated private `sorry` tokens. The native transitive dependency audit is **not** yet complete; this remains a later milestone and is not claimed by Step 1.

## Files

- `CANONICAL_SELECTION.json`: canonical-source decision and non-mixing policy.
- `TOOLCHAIN.lock.json`: exact toolchain, dependency, and flag lock.
- `SOURCE_MANIFEST.json`: per-source hashes, imports, status, and admission metadata.
- `DEPENDENCY_GRAPH.json` / `.dot`: full 129-node dependency graph and build order.
- `REPRODUCTION_STATUS.json`: machine-readable gate result.
- `logs/`: live clean-build and strict-root diagnostics.
- `evidence/`: archived build evidence, admission reconciliation, integrity checks, and dependency-artifact provenance.

## Boundary of Step 1

Step 1 establishes a canonical, reproducible baseline. It does **not** assert that strict v7 already compiles completely, that the frozen main theorem has been audited, or that the final transitive `sorryAx` audit has passed. Those are the gates of later steps.
