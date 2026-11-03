# Step 3f: four elementary publication checks

**Decision:** three leaves are eligible as direct published theorem statements/directions; one remains pending a generic specialization bridge. This is a source-and-literature judgment, **not kernel acceptance**. The JSON companion records exact signatures, hashes, source locations, and remaining checks.

| Lean leaf | Primary source | Eligibility | Hypothesis and type comparison |
|---|---|---|---|
| `regular_of_heightOne` | [Stacks 031T, Lemma 10.157.6(2)](https://stacks.math.columbia.edu/tag/031T) | Eligible | Same Noetherian normal domain and fraction field. `RegularAtPrime` expands to `∃ a b, b ∉ p ∧ z*b=a`, literally membership in the localization at `p`; `RegularScalar` expands to membership in the image of `R`. This is the nontrivial direction of the published height-one intersection equality. |
| `affine_localDerivation_exists` | [Stacks 01UO, Lemma 29.33.4](https://stacks.math.columbia.edu/tag/01UO) | Eligible | Specialize the affine scheme to `U`, base to `Spec ℂ`, and coefficient sheaf to `O_U`. The unbundled additive/Leibniz/constant-annihilation laws describe the actual relative derivation. Conclusion is the surjective direction of the global-sections bijection. |
| `affine_localDerivation_ext` | [Stacks 01UO, Lemma 29.33.4](https://stacks.math.columbia.edu/tag/01UO) | Eligible | The same bijection's injective direction. `LocalDerivation` explicitly includes all subopen actions, restriction naturality, Leibniz, and annihilation of base sections. Equality of actions on every global function determines the whole derivation. |
| `firstOrder_cotangentHom_bijective` | [Stacks 02H5](https://stacks.math.columbia.edu/tag/02H5), [04FJ](https://stacks.math.columbia.edu/tag/04FJ), [04FK](https://stacks.math.columbia.edu/tag/04FK) | Pending generic bridge | The published cotangent-Hom torsor uses the first-order thickening's conormal sheaf. The source instead uses the actual dual-number product and its specified epsilon-normalized map into `O_Y`. The expected specialization is mathematically correct, but it needs the conormal identification and canonical-map comparison below. |

The first three judgments do not impose extra formal work for mere presentations of definitions. `RegularAtPrime`, `RegularScalar`, and the fields of `LocalDerivation` are concrete expanded forms of the concepts in the cited statements, not contact-geometric hypotheses. In 01UO the coefficient sheaf may be arbitrary; no quasi-coherence, finite-type, or smoothness assumption is missing. The `h0` premise in the existence leaf is redundant with additivity and does not strengthen its conclusion.

## Remaining first-order comparison

`Lines.FamilyVariation.Deformation` is genuine geometric data: a map from `Y ×_ℂ Spec(ℂ[ε]/ε²)` to `X`, over `ℂ`, whose zero-section restriction is `f`. It contains no conclusion or positivity field. `Deformation.cotangentHom` is built from the actual epsilon coefficient, the universal derivation, and pullback/pushforward adjunction. `LSHomVelocity.lean` already proves its normalization on local differentials, its uniqueness under that normalization, and its vanishing for the constructed constant lift.

The cited source gives a simply transitive action by `Hom(f* Ω, C)` for a first-order thickening, with `C` its conormal module. Remark 04FK covers the fixed target used here. To apply this exact generic result, the remaining wrapper must identify the source's actual zero-section thickening as first order, identify `C` with `O_Y` through its actual epsilon, and compare the difference/action map with `Deformation.cotangentHom`. Existing reconstruction and multiplication identities provide much of the algebra; the current code does not yet expose this complete generic application. Its `dualThickening_normalForm_unique` admission also needs its own separate leaf audit.

This is a standard generic deformation-theory specialization, not a new contact-Fano theorem. It should remain pending until that comparison is explicit, or an exact primary statement using this canonical dual-number construction is located. The label alone is insufficient.

## Bookkeeping

The current `regular_of_heightOne` publication declaration lacks `_root_` inside `LeBrunSalamon.Refinement.Boundary`. Its lexically scoped name is therefore `LeBrunSalamon.Refinement.Boundary.LeBrunSalamon.PublishedInputs.Step3f.regular_of_heightOne`. This does not change the published mathematical statement; the native audit must record the actual elaborated name.

`04BU` is the stable tag for Section 37.9, not Lemma 37.9.2. The precise lemma tag is `02H5`. A comment/citation correction is appropriate independently of the mathematical proof.

For a fixed acceptance checklist, these results supply **three completed publication-eligibility judgments** out of the audited four. They supply no new compiled-obligation closures and no whole-project gate pass.
