# Step 3f: published inputs and project translations for the formal-trait models

This is a source-level boundary audit, dated 2026-11-03. It does not certify the two existing formal-trait admissions or claim that they have been proved. The existing theorems are in `source/LSFormalTraitModel.lean`:

- `PublishedInputs.Step3f.formalTrait_twoComponent_lineNormalForm`;
- `PublishedInputs.Step3f.formalTrait_smooth_lineNormalForm`.

## What the current targets actually require

The base is the specified complex power-series trait. The hypotheses retain properness, flatness, local finite presentation, nodality, projectivity, and a smooth geometrically integral generic fibre. The reducible closed fibre is identified with the actual pushout of two projective lines at their marked points, with the given line bundle of degree one on each component. The smooth target instead has an actual projective-line closed fibre and degree two.

The reducible conclusion asks for a nonzero power series with zero constant coefficient, an actual isomorphism to the chosen `Smoothing.StandardSource` after base change by that power series, its commutation with the trait projection, and an actual sheaf isomorphism for the given line bundle. The smooth conclusion similarly uses the project's specified product family and its specified tensor-square hyperplane line. These are stronger implementation outputs than the existence of some relative plane-conic presentation.

## Exact generic published ingredients that can be isolated

| Generic statement | Primary source | Exact scope and remaining use |
| --- | --- | --- |
| If `f : X → S` has finite presentation and an `O_X`-module `G` has finite presentation, is flat over `S`, has support proper over `S`, and all positive higher direct images vanish, then `f_* G` is locally free and its formation commutes with arbitrary base change. | [Stacks, Lemma 36.32.4, tag 0D4E](https://stacks.math.columbia.edu/tag/0D4E) | This is a generic cohomology/base-change input. Its explicit higher-direct-image vanishing premise must be supplied. It does not itself assert the rank, evaluation surjectivity, or the desired embedding. |
| A proper curve over a field with vanishing first structure-sheaf cohomology and an invertible sheaf of degree one is isomorphic to the projective line. | [Stacks, Proposition 53.10.4, condition (7), tag 0C6U](https://stacks.math.columbia.edu/tag/0C6U) | This can identify individual fibres after proving its premises. It is a field statement; it does not trivialize a family over a trait. |
| For a cartesian square over `Spec(A)` and `Spec(B)`, finite locally free `B/A` makes the canonical cohomology base-change map an isomorphism for any quasi-coherent sheaf. | [Stacks, Lemma 30.5.3, tag 0CKW](https://stacks.math.columbia.edu/tag/0CKW) | Its degree-zero structure-sheaf specialization is implemented separately in `LSFiniteFreeBaseChange`. It addresses the dual-number normal form, not the relative-conic classification. |

Each row is a statement about arbitrary schemes or curves and their ordinary sheaves. None includes a contact structure, a selected `StandardSource`, an already-assembled family normal form, or the final project conclusion among its hypotheses or output.

## What the new papers supply

[Hu–Liu–Wan, arXiv:2610.10410v1](https://arxiv.org/html/2610.10410v1), Lemma 2.5, gives a relative anticanonical plane-conic presentation in its stable-family setting and an étale-local nodal equation. Lemma 2.2 compares the contact line with the inverse dualizing line up to a line from the base. These are useful structural guides, but their stated setting and selected line differ from the arbitrary trait family and arbitrary degree-(1,1) line in the current Lean signature. Their statements do not directly supply the chosen `StandardSource` isomorphism.

[Fu, arXiv:2611.01423v1](https://arxiv.org/html/2611.01423v1), §5.2, proof of Proposition 5.3, constructs a relative conic from a line of degree one on both central components, using disjoint sections, cohomology/base change, and Nakayama. This gives a promising proof route for the current model theorem. The construction still needs to be expressed using the current definitions, including its actual conic-to-`StandardSource` map and its line-bundle comparison.

The papers are preprints. This report does not treat their full LeBrun–Salamon conclusion, or a lemma containing the remaining project proof wholesale, as a permissible shortcut.

## Project translations still to prove

1. Obtain disjoint sections through the chosen smooth closed-fibre points. A suitable generic henselian lifting theorem must be cited with its precise hypotheses before becoming a leaf. The present report has not installed such a leaf.
2. Prove the required fibre cohomology, rank, and generation statements for the actual given line bundle. Apply a precise cohomology/base-change theorem and use the local nature of the power-series base to choose an actual free module of global sections.
3. Construct the relative embedding and its quadratic equation. Prove that its equation can be normalized to a conic with the actual nonzero smoothing element, including its unit factor. The nonvanishing and vanishing-constant-coefficient clauses in the target must follow from the actual generic and closed fibres.
4. Construct and verify the map from that plane conic to the chosen `StandardSource` after base change. Its two projective-line projections, scheme structure, and trait projection must agree with those already used by the later proof.
5. Identify the given line with the specified pullback of the two hyperplane lines. Degree calculations alone are not an existing isomorphism; the relative line comparison or Picard argument must supply the sheaf isomorphism.

For the smooth case, one can instead use a lifted section to construct a relative degree-one line and a rank-two pushforward, then identify the family with a projective bundle over the trait. Freeness over the local base and the degree-two line comparison remain explicit proof steps.

## Acceptance boundary

The two formal-trait admissions remain composite obligations. No source change in this batch moves them into a new admitted wrapper. The generic statements above identify reusable published inputs; accepting one of them does not accept any of the five project translations or either complete model theorem. The coordinate-normalized `standardConic_fundamentalClass_exists` is a separate obligation: generic duality/adjunction does not by itself verify the requested local frames and signs.
