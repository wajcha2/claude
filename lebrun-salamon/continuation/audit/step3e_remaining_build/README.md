# Remaining Step 3e translations: native diagnostic pass

The three translation proofs and an exhaustive dependency-closure audit passed the pinned native Lean frontend in **8.494 seconds** on 2026-11-03. The source is `Step3eRemainingTranslations.lean`; the exact hash, compiler invocation, dependency artifact hashes and logs are recorded in `receipt.json` and `RUN_STATUS.json`.

## Proofs and source scope

- **Smooth cotangent rank:** [Stacks Project Lemma 29.35.12, Tag 02G1](https://stacks.math.columbia.edu/tag/02G1) gives local freeness of relative differentials; [Definition 29.35.13, Tag 02G2](https://stacks.math.columbia.edu/tag/02G2) fixes relative dimension. The new generic leaf produces a universal cotangent presentation of the required rank. The project proof uses the already proved uniqueness of that universal presentation and transports an actual local free cover to the chosen project sheaf.
- **Positive-power ampleness:** [Stacks Project Lemma 28.27.2, Tag 01PT](https://stacks.math.columbia.edu/tag/01PT), with the quasi-compact convention of [Definition 28.27.1, Tag 01PR](https://stacks.math.columbia.edu/tag/01PR), is stated on actual invertible module sheaves and recursive tensor powers. The proof explicitly transports every existential section and nonvanishing-open predicate using `linePower_sheaf_eq_tensorPower`. It does not assume the project's line-power construction is definitionally the ordinary tensor power.
- **Determinants of short exact sequences:** no new admission is added. The generic exterior map from [Stacks Project Lemma 48.29.1, Tag 0E9Y](https://stacks.math.columbia.edu/tag/0E9Y), already audited in `../tangent_determinant_build`, gives the dual-determinant tensor relation. The new proof uses proved determinant duality and explicit tensor cancellation to obtain the exact public conclusion.

The closure audit traverses both declaration types and values, including inductive constructors. It rejects any use of the three old `PublishedInputs.Step3e` admissions and requires the relevant generic published input. All three checks passed. The remaining direct admitted dependencies are printed in the log; this audit does not certify every other generic input in the wider library.

## Integration status

All three old declaration names retain their original theorem types and now have proved bodies in `source/RecompileBasePart04.lean`. The two generic published inputs replace three old project admissions, reducing the direct `sorry` count by one. The exact integration diff and before/after hashes are preserved.

The diagnostic imported the frozen published-head Base04 plus the previously checked standalone determinant translation. The integrated Base04 module and its changed reverse dependency graph have **not yet been replayed**. The current source graph cannot reuse downstream CI artifacts whose Base04 ancestor changed.
