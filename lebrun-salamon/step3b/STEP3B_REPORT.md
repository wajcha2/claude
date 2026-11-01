# LeBrun–Salamon formalisation — Step 3b final report

**Status: PASSED**

Step 3b replaces the surviving tensor/dual/exterior/symmetric sheaf wrapper admissions by complete Lean proofs from a quarantined family of generic published inputs.

## Scope

The Step 3a tree contains 99 direct admissions. Step 3b changes only:

- `RecompileBasePart03.lean`
- `RecompileBasePart04.lean`

The other 127 source modules are byte-identical to the certified Step 3a tree.

## Project wrappers discharged

1. `LeBrunSalamon.PhaseTwentyFive.tensorSheaf_pullback`
2. `LeBrunSalamon.PhaseTwentyFive.dualSheaf_pullback`
3. `LeBrunSalamon.PhaseTwentyFive.cotangentPresentation_exists`
4. `LeBrunSalamon.PhaseTwentySix.exteriorPresentation_exists`
5. `LeBrunSalamon.PhaseTwentySix.exteriorSheaf_locallyFree`
6. `LeBrunSalamon.PhaseTwentySix.exteriorSheaf_pullback`
7. `LeBrunSalamon.PhaseTwentySix.symmetricPresentation_exists`
8. `LeBrunSalamon.PhaseTwentySix.pullback_locallyFree`

Each now has a complete proof body and no direct `sorry`.

## Quarantined exact published inputs

The eight admissions have been moved to the namespace
`LeBrunSalamon.PublishedInputs.SheafFunctoriality`. They are generic statements about ringed-space module sheaves and do not mention contact geometry, the LeBrun–Salamon manuscript, its project structures, or its final theorem.

The exact declarations and source locators are recorded in `PUBLISHED_INPUTS_3B.csv`.

## Admission accounting

- Before Step 3b: 99 direct admissions, all requiring proof/refactoring after Step 3a.
- After Step 3b: 99 direct admissions total.
- Admissions in project wrappers discharged by Step 3b: 0.
- Exact published-input admissions introduced: 8.
- Remaining non-published proof/refactoring obligations: 91.
- `admit`: 0.
- custom `axiom`: 0.
- project `opaque`: 0.

The count remains 99 because each of eight wrapper admissions was replaced one-for-one by one exact generic published leaf.

## Kernel checks

- `RecompileBasePart03`: return code 0; output SHA-256 `516cdc807c154cd78fb8e4afd5e858329953f8fffeb5192dd87a6f469c246dfb`; 21 warnings, 0 errors.
- `RecompileBasePart04`: return code 0; output SHA-256 `1765de71fde4b7b2a35ec3035e01569a599995eae9ee7828ee24e6ed80e4a18f`; 44 warnings, 0 errors.
- Full compatibility module: imported the 73 previously compiled strict project artifacts with the new Part03/Part04 artifacts shadowing their predecessors; return code 0; output SHA-256 `36acc46d65455772d5b7b3a45968a6f8e2d4ae954b6e4bff30a84b0a156587cf`.
- Final strict checker: `passed = true`, zero violations.
- All eight wrapper theorem headers are byte-normalized-identical to their Step 3a interfaces.

## Statement integrity

The frozen Step 2 main-statement SHA-256 remains:

`9afe9c5b2e63db17e8f217b71c821eaca83fe26c5cfbc2956fc1b92832d09296`.

## Boundary of the result

Step 3b does not complete Step 3. It establishes the published-input boundary for the basic sheaf-functoriality layer. The remaining 91 non-published obligations are assigned to Steps 3c–3n.
