# OBL-056: exact deformation boundary and remaining translations

Status: source and primary-literature review only. No original proof has been replaced, no new published input has been introduced, and no native or ledger credit is claimed. The separate finite-sum helper proposed below is an ordinary proof task, not an obstruction theorem.

## 1. The original obligation

The original declaration is `Construction.Smoothing.HomDeformationInput.StandardInputs.smooth_of_firstCohomology_vanishes` in `RecompileExtensionsPart04Geometry.lean`. It has an arbitrary locally Noetherian base `S`, a proper, flat, locally finitely presented source family `pi : Y ⟶ S`, the original smooth proper complex target, and a supplied all-test-scheme `Presentation`. Local finite presentation of `H.toBase` is already an explicit hypothesis.

Its point is the actual morphism `p : ComplexBase ⟶ H.parameter`. The equations `hp` and `hb` imply `b ≫ sS = 𝟙 ComplexBase`. The coefficient sheaf in the hypothesis is exactly

```
pullbackModule (familyChange pi b H.toBase p hb ≫ H.evaluation)
  (tangentSheaf X.structureMap).
```

The conclusion is a smooth open restriction of the actual map `H.toBase`, containing the whole range of `p`. It is not a tangent-dimension assertion, generic smoothness, or smoothness of a different representative.

I found no missing geometric hypothesis in this original statement. Flatness of `pi`, smoothness of the target, local Noetherianity of the base, the all-test universal property, and the displayed finite-presentation hypothesis each have a concrete role. No source smoothness, projective embedding, integrality, or reducedness of the Artinian tests should be added.

## 2. Exact published inputs that would be eligible

### A. One square-zero thickening, with its actual obstruction sheaf

Use SGA 1, Exposé III, Proposition 5.1 and Corollary 5.2: printed pages 59–61, especially pages 60–61; arXiv `math/0206203v2`, PDF indices 74–76. For a square-zero closed immersion `i : T₀ → T` over `B`, its actual ideal `J` regarded as an `O(T₀)`-module, a smooth `Z → B`, and `f₀ : T₀ → Z` over `B`, the obstruction lies in

\[
H^1\bigl(T_0,\mathcal{H}om(f_0^*\Omega_{Z/B},J)\bigr).
\]

If that group is zero, a global `B`-morphism `T → Z` extending `f₀` exists. This is the proposed leaf's entire conclusion. The input must retain the actual thickening, quotient/kernel identification, structural maps and extension equation.

Source: [SGA 1, Exposé III §5](https://arxiv.org/pdf/math/0206203). The same lift sheaf and action are stated in [Stacks 04FH](https://stacks.math.columbia.edu/tag/04FH), [04FJ](https://stacks.math.columbia.edu/tag/04FJ) and the fixed-target specialization [04FK](https://stacks.math.columbia.edu/tag/04FK).

A suitable typed boundary is an arbitrary-scheme theorem with inputs `i`, `sT`, `sZ`, `f₀`, the commutative structural equation, and a concrete `SquareZeroIdealPresentation i J`. The last structure must express a sheaf-kernel/quotient presentation and annihilation by the ideal, not a lifting conclusion. State the vanishing premise using the actual derived `H1` of the literal internal-Hom sheaf. If an arbitrary universal cotangent presentation is used to avoid a chosen implementation, its derivation and universal property must be explicit and its comparison to `cotangentSheaf` must be proved.

Do not put `Presentation`, `HomDeformationInput`, a parameter point, or a smooth-open conclusion into this leaf.

### B. The pointwise small-extension criterion

Use [Stacks 02HX, Lemma 37.12.1, (4) ⇒ (1)](https://stacks.math.columbia.edu/tag/02HX). For `f : W → S`, with locally Noetherian `S` and locally finite type `f`, fix `w ∈ W`. Require a lift in every commutative diagram

\[
\operatorname{Spec}B\xrightarrow{\alpha}W,
\qquad \operatorname{Spec}B'\xrightarrow{\beta}S
\]

over a small extension `B' → B`, where the closed point maps to `w` and the induced residue-field map is an isomorphism. Conclude that `f` is smooth at `w`.

Here “small” has the literal meaning of [Stacks 02HS, Definition 10.141.1](https://stacks.math.columbia.edu/tag/02HS): local Artinian rings, a surjection, and kernel of module length one. Retain this quantification, rather than replacing it by dual numbers alone. A Lean-facing conclusion can be membership in the actual `f.smoothLocus`; the native Mathlib definition uses formal smoothness of the actual stalk map.

The final open restriction does not need another published input. The pinned Mathlib file `Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean` supplies `exists_smooth_of_formallySmooth_stalk`, `Scheme.Hom.isOpen_smoothLocus`, `Scheme.Hom.smoothLocus`, `smoothLocus_eq_top_iff`, and `preimage_smoothLocus_eq`.

### What the other cited results do and do not supply

SGA III Corollaries 5.4 and 5.6 concern successive ideal-adic extensions. Corollary 5.6 also assumes an affine base, a flat source, and locally free graded ideal pieces. Those conditions are not a direct substitute for the arbitrary small-extension argument above.

[Stacks 08U8](https://stacks.math.columbia.edu/tag/08U8) gives an obstruction in an Ext group of the derived pullback of the naive cotangent complex. Turning that into the displayed tangent-sheaf `H1` needs additional comparisons; it does not directly identify the project's sheaf. [Stacks 02H6](https://stacks.math.columbia.edu/tag/02H6) identifies smoothness with local finite presentation and formal smoothness and explains the lift-torsor argument. Vanishing at one fibre must not be promoted to formal smoothness on every fibre.

## 3. What is already represented honestly in the project

`CotangentPresentation s` is a sheaf of modules with an actual all-open relative derivation and its universal factorization property. `cotangentSheaf s` is its chosen object. `tangentSheaf s` is the actual internal-Hom dual of that object. It is not a rank token. `SmoothProperComplexVariety.smooth` gives smoothness of the actual target structure map and `smooth_cotangent_rank` supplies its finite locally free cotangent sheaf.

`HasVanishingFirstCohomology E` says every actual short exact sequence `0 → E → F → O → 0` admits a right inverse of its quotient. The existing theorem

```
CohomologyBaseChange.firstCohomology_iff_h1 E :
  HasVanishingFirstCohomology E ↔
    Subsingleton (CohomologyHypotheses.H1 E)
```

is already a proof. It uses the already recorded generic input `PublishedInputs.Cohomology.ext1_unit_h1` and the proved `YonedaExtensionSplitting.allExtensionsSplit_iff_ext1_subsingleton`. Its standard source is [Stacks 0B3A](https://stacks.math.columbia.edu/tag/0B3A). The frozen continuation baseline records that input under original roots OBL-025 and OBL-026. No second Yoneda-to-derived-cohomology input is needed.

`FirstCohomology.iso_iff` already transports the original vanishing predicate along an actual module-sheaf isomorphism. The native module graph allows importing `LSPublishedCohomologyBaseChange` before Geometry: its transitive imports do not include Geometry. A future import change must still be included in the source and acceptance guards.

## 4. Project proofs still required

| Proof boundary | Required actual assertion | Status |
| --- | --- | --- |
| Rational centre | From `hp` and `hb`, identify the residue field at `p` with `ℂ` compatibly with `H.toBase ≫ sS`, and obtain the corresponding closed-point map for each small-extension test. | Required; do not replace it by an arbitrary field isomorphism. |
| Family restriction | For `α : Spec B → H.parameter`, the represented map is exactly `familyChange ... α ... ≫ H.evaluation`; after restriction to the complex closed point it is the original `familyChange ... p hb ≫ H.evaluation`. | The actual universal property and the checked relative-functor comparison are available; the chosen test diagram still needs its composition equalities. |
| Small-extension ideal | For `B' ↠ B`, let `I` be the actual kernel. Flat base change of `pi` identifies the ideal of `Y_B ↪ Y_B'` with the sheaf associated to `O_Y_B' ⊗_{B'} I`. The maximal ideal annihilates `I`; its length-one residue-field module has dimension one. | Substantial missing ordinary sheaf/algebra proof. |
| Cotangent and tangent coefficients | Identify `Hom(g_B^*Ω_X/ℂ, J)` with the pushforward of `g_b^*T_X/ℂ ⊗_ℂ I` from the actual closed fibre. Preserve the relative base and the actual evaluation map. | Substantial missing ordinary proof; use universal cotangent comparison, finite local freeness, tensor-Hom, pullback composition and the actual kernel identification. |
| Cohomology support | Transport `H1` through the nilpotent closed-fibre homeomorphism and the literal coefficient-sheaf isomorphism. After choosing a residue-compatible basis of the length-one `I`, reduce to the original `hH1`. | Not supplied by the existing Yoneda/derived comparison alone. A general finite-dimensional version additionally uses finite-sum preservation. |
| Lift and universal property | Apply input A to get the actual global lifted family map. Use `H.universal (Spec B') β` to recover a parameter lift. Use naturality and injectivity at `Spec B` to prove that its restriction is the supplied `α`, and retain its base equation. | All-test representability is present; this is a project-owned translation. |
| Pointwise-to-open | Apply input B at the actual point, then use the native smooth locus and the one-point nature of `Spec ℂ` to get an open containing `Set.range p`. | Small ordinary geometric wrapper after the lifting argument. |

With `g_b` the exact original fibre map and `j : Y_b → Y_B`, the key missing comparison has the following mathematical shape:

\[
\mathcal H om_{\mathcal O_{Y_B}}(g_B^*\Omega_{X/\mathbf C},J)
\;\cong\;
j_*\bigl(g_b^*T_{X/\mathbf C}\otimes_{\mathbf C}I\bigr).
\]

This is a goal to prove from flatness and the actual small extension. It is not proposed as a project-specific published input. Since `I` has length one, a compatible choice of basis avoids a cohomology/base-change theorem for arbitrary tensor coefficients. Nilpotent thickenings have the same underlying topological space, but the `O`-module categories differ; the abelian-sheaf and scalar-restriction comparisons must therefore be written explicitly.

One can either work with maps to the fixed target `X` over `ℂ`, exactly as the original `Presentation` does, or with the conventional relative target `X ×_ℂ S`. The checked all-test relative-functor comparison makes these equivalent. The fixed-target route avoids an unnecessary extra target cotangent base-change layer; it does not remove the source ideal comparison.

## 5. Scoped next proof

The manageable independent task is a zero-new-input theorem that finite coproducts preserve the original Yoneda vanishing condition. In an arbitrary abelian category with enough injectives, use the existing proved representation of Ext1 classes and the pinned native equivalence `Ext.addEquivBiproduct`. Then instantiate at the actual `OModule X`, the actual unit `structureModule X`, and transport the chosen biproduct to the actual coproduct. Include the empty finite family.

This proves only finite coefficient-sum preservation. It does not prove the ideal comparison, the lifting obstruction theorem, OBL-056, or any new acceptance unit. A first meaningful larger prototype should keep inputs A and B as explicit parameters and close the small-extension coefficient comparison before attempting the final Hom smoothness proof.

## 6. Audit boundaries

- All frozen 3h source files remain unchanged.
- No pending original OBL-055 or OBL-056 is used as a proved input. OBL-056 already assumes finite presentation, so using OBL-055 to discharge it is optional downstream assembly, not part of this proof's logical prerequisites.
- The 3h differential-surjectivity converse assumes both structural maps are smooth. Applying it to the unknown Hom source here would be circular.
- No global formal-smoothness conclusion, properness-to-projectivity substitution, or dual-number-only test criterion is justified by this review.
- The new two-input boundary is a proposal for independent source/type review; no declarations containing admissions have been added.

The companion JSON binds the exact original declaration, definitions, existing bridge sources, native Mathlib revision and reviewed primary locators. Compiler execution is a separate, explicitly leased task.
