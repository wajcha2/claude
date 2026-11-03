# Native proof-batch evidence — 3 November 2026

## Scope

All five candidate modules below passed the unchanged pinned stock Lean compiler. The actual candidate source, diagnostic input copy and receipt source hash were checked for equality. These checks use recovered baseline dependency interfaces. They **do not certify the current cumulative dependency graph or attainment of the published-theorem-only milestone**. Each receipt records the exact imported artifact hashes, command, runtime fingerprint, exit code and output hash.

| Module | Seconds | Candidate SHA-256 |
| --- | ---: | --- |
| `RecompileBasePart05A` | 62.856 | `7e6497b17a33f6b700418f118b45624833c7f8407a989e685813cb648fe9cf05` |
| `LSFirstJetEmbedding` | 30.984 | `165b776ccb8c20d18aed5ac3c4ed2058dc921a7f326509aaa131c25dc14dbd58` |
| `LSFirstJetEmbeddingGeometry` | 30.661 | `1354e7f1649edd2b8e2a501766b01d2790711b6fb62986333251615bbe89cb04` |
| `LSClassicalReduction` | 27.870 | `5f553b7cea8d929432e7b267a7c7e5fde6889b326ae96bf3e57d3d67cd55a3dc` |
| `LSHomVelocity` | 109.267 | `10aa675e010a4320f167867effd07c7e1b088264851f34c906b7ba448276b0b5` |

The first-jet helper and geometry modules contain no direct admissions and emitted no `declaration uses sorry` warnings. The old direct admission in `PublishedInputs.Step3e.polarizedEmbedding_firstJets` is replaced by the actual closed-embedding proof. The determinant module retains one explicit published discriminant leaf and supplies proved tensor conversion and alternation wrappers.

## Native axiom inspection

`AXIOMS.txt` is the actual compiler output. `origin_surjective` and both root/public forms of `dualThickening_zeroSection_surjective` depend only on `propext`, `Classical.choice`, and `Quot.sound`. The final first-jet theorem also reports `sorryAx`; the dependency traversal below identifies its exact origin.

## Full first-jet dependency traversal

`LSFirstJetDependencyAudit.lean` is the actual executed audit source. It uses the checked kernel environment and traverses **all constants**, including Lean and Mathlib constants. It reads each constant's type and, when available, its definition, theorem or opaque value; inductive constructors are also traversed. A breadth-first queue records shortest dependency paths. The audit passed with exit code zero.

- All constants visited: **78870**.
- Project constants visited: **583**.
- Direct uses of `sorryAx`: **1**.
- Missing constants: **0**.
- Custom project axioms: **0**.

The complete project-name closure is in `FIRST_JET_PROJECT_CLOSURE.txt`; raw native output is in `FIRST_JET_DEPENDENCY_NATIVE_OUTPUT.txt`. The sole direct admission and its shortest path are printed exactly below:

```text
DIRECT_SORRY LeBrunSalamon.PublishedInputs.SheafFunctoriality.pullback_locallyFree
MODULE RecompileBasePart04
SHORTEST_PATH LeBrunSalamon.PublishedInputs.Step3e.polarizedEmbedding_firstJets -> LeBrunSalamon.ClassicalReduction.FirstJetProof.projectiveEmbedding_firstJets -> LeBrunSalamon.ClassicalReduction.FirstJetProof.Embedding.tupleJet_projectivelyImmersive -> LeBrunSalamon.ClassicalReduction.FirstJetProof.DualCoordinateProof.projectiveMaps_eq_of_scaled_frames -> LeBrunSalamon.ClassicalReduction.FirstJetProof.projectiveMaps_eq_of_coordinateIso -> LeBrunSalamon.PhaseTwentySix.pullbackLine -> LeBrunSalamon.PhaseTwentySix.pullbackLine._proof_1 -> LeBrunSalamon.PhaseTwentySix.pullback_locallyFree -> LeBrunSalamon.PublishedInputs.SheafFunctoriality.pullback_locallyFree
TYPE ∀ {X Y : AlgebraicGeometry.Scheme.{0}} (f : Quiver.Hom.{0, 1} X Y) {E : LeBrunSalamon.PhaseOne.OModule.{0} Y}
  {r : ℕ},
  LeBrunSalamon.PhaseOne.IsLocallyFreeOfRank E r →
    LeBrunSalamon.PhaseOne.IsLocallyFreeOfRank (LeBrunSalamon.PhaseTwo.pullbackModule.{0} f E) r
```

Neither `symplecticDeterminant` nor `alternatingDiscriminantTrivial` occurs in that closure. The only name ending `polarizedEmbedding_firstJets` is the newly proved root theorem; no older alias or branch claim is used.

## Baseline signature comparison and publication scope

`PULLBACK_RANK_SIGNATURE_COMPARISON.json` records a byte-for-byte comparison of the sole admitted declaration in the current Part04 source and certified Step3b source. The declarations, including their complete signatures, are identical. The native printed type above agrees with that source statement.

The source cites Stacks Lemma 17.14.3. Its precise lemma tag is [01C8](https://stacks.math.columbia.edu/tag/01C8); [01C5](https://stacks.math.columbia.edu/tag/01C5) is the section. The lemma explicitly states preservation of local freeness; its statement does not display the constant-rank clause. The follow-up [reference comparison](../PULLBACK_RANK_REFERENCE.md) supplies explicit primary formulations: Vakil, *The Rising Sea*, Exercise 14.1.B(b)–(c), p.402, for positive rank (including rank one used in this first-jet proof); and Griffith, *Maps to Projective Space Defined by Global Sections of Invertible Sheaves*, Proposition 2.12, p.4, for the same constant rank without a positivity restriction. The latter is accurately identified as author-hosted expository notes. This clarifies the one historically accepted Step3b generic input; no contact or first-jet assertion is hidden in it, and no additional admission was introduced.

## Determinant boundary

The repaired Part05A's sole admission is the underlying-line conclusion of Auel's 2009 Penn dissertation, *Cohomological invariants of line bundle-valued symmetric bilinear forms*, Proposition 1.10 (p.15), with discriminant line defined in Definition 1.7 (p.13). The Lean leaf is restricted to smooth proper connected schemes over the actual complex base and explicitly requires alternation and a perfect adjoint map. Its source is [Auel's dissertation](https://math.dartmouth.edu/~auel/papers/docs/AUEL_thesisSS.pdf). The conversion from trivial discriminant line to determinant identity and the contact caller's alternation proof both compiled in this batch. This receipt remains scoped to the baseline interfaces pending the current cumulative build.
