# LeBrun–Salamon formalisation: recovered continuation source

**Status: RECOVERED, UNCHECKED — 3 November 2026.**

This directory preserves the 129 Lean source modules from
`LeBrunSalamon_Cumulative_Precompile_Step3g_V2_20261103.zip` byte for byte.
The archive SHA-256 is
`722c44bc3e21211634732fc92fb0d598b429f886ac85dec3d3699318d4a3fe32`.
This source recovery is not a compilation certificate or a proof-completion claim.

## What is preserved

- `source/`: exactly the 129 recovered `.lean` modules; no source edits were made.
- `SOURCE.sha256`: SHA-256 hashes of those modules, relative to this directory.
- `target/MainStatement.lean`: the separately frozen Step 2 target statement.
- `TOOLCHAIN.lock.json`: the unchanged Step 3b toolchain lock.

The target statement SHA-256 is
`9afe9c5b2e63db17e8f217b71c821eaca83fe26c5cfbc2956fc1b92832d09296`.

## Evidence boundary

The recovered source has 98 direct `sorry` admissions. The takeover inventory
records 43 rewritten wrapper declarations; their cumulative compilation and
their published-input boundary remain to be audited. These rewrites must not
be counted as certified completed proof obligations.

Step 3b remains the latest historical accepted incremental batch. Its report
records 99 direct admissions, eight identified published-input leaves, and
91 remaining non-published proof/refactoring obligations. Later partial
reports and this recovered cumulative source do not by themselves advance
that certified boundary.

The current source theorem's stated conclusion is only the local-symmetry form.
It has not yet been connected to the stronger frozen target, whose conclusion
also requires an actual Wolf-space homothety. The target file is preserved
separately to make this outstanding obligation explicit.

No claim is made that all remaining admitted declarations are exact published
theorems. Source-specific specialisations, construction steps, definition
bridges, and novel arguments must receive complete Lean proofs. The first
milestone permits `sorry` only for exact published theorems, with their
hypotheses and source citations checked.

## Continuation discipline

Keep this checkpoint and the older stage catalogues as historical evidence.
Preserve the frozen target and the pinned Lean/mathlib environment. Record
each subsequent source change and its affected dependency closure. Reuse only
hash-matched verified artifacts; compile unchecked or changed parts at the
appropriate validation gate. Report compilation and admission classification
separately, including transitive dependencies and semantic definition bridges.

The inherited GitHub workflows are restricted to historical branch names;
this archival commit does not start a project build.

To verify the archived source bytes from this directory:

```bash
sha256sum --check SOURCE.sha256
```
