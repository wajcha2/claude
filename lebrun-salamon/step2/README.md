# LeBrun–Salamon formalisation — Step 2

This directory freezes and mechanically checks the exact main theorem statement.

## Result

`MainStatement.lean` compiles unchanged under Lean `v4.36.0-rc1` and mathlib revision `116662aa4c1e9106ab5c609b3214b02f6e11a65a`. It contains no `sorry`, `admit`, custom `axiom`, or `opaque` declaration.

The audit found that the previous public theorem was incomplete at the interface level: it exposed only parallel curvature. The frozen proposition contains both the parallel-curvature conclusion and a positive metric homothety to an actual intrinsic Wolf-space model.

## Files

- `MainStatement.lean` — admission-free frozen definitions and proposition.
- `STATEMENT_AUDIT.md` — critical clause-by-clause mathematical audit.
- `STATEMENT_AUDIT.json` — machine-readable audit.
- `STATEMENT_FREEZE.json` — exact source and proposition freeze record.
- `FINAL_RECHECK.trigger` — records the final CI recheck of the normalized source.

## Mechanical certificate

GitHub Actions run `41305229872` compiled the checked-in source without transformation. The source SHA-256 is `9afe9c5b2e63db17e8f217b71c821eaca83fe26c5cfbc2956fc1b92832d09296`; the compiled olean SHA-256 is `48c594a66e4e43de69190cf35994405172f04cfa479242cbdb965f129f12080b`.

This certifies the statement layer only. It does not claim that the entire strict proof tree compiles or that the frozen proposition has already been proved.
