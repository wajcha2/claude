# OBL-056 progress — 4 November 2026

**Status: isolated proof preparation; OBL-056 remains open.** Several ordinary algebraic and geometric translations now have complete local Lean checks. The obstruction coefficient comparison and the application to every small Artin test remain unfinished. No new published input has been introduced, no production proof has been selected, and this work adds zero acceptance credit.

This is a follow-up to `OBL056_BOUNDARY_PLAN.md` (SHA256 `8a719b36a12f1da44f0ad79ecbf27eceb6ca772739c30c7fa0d76fc8b21626f4`) and its JSON record. Both original files remain byte-identical. Their original seven boundaries are retained below. Complete receipts and exact source/output hashes are indexed in `OBL056_PROGRESS_20261104.json`.

## Progress against the seven boundaries

| Original boundary | Completed ordinary work | What remains |
| --- | --- | --- |
| **1. Rational centre** | `RationalResidue` identifies the residue field at the actual `p : Spec ℂ → H.parameter` with `ℂ` using its actual residue map. It proves the corresponding base-point identification and compatibility with the actual `H.toBase` residue map, from the original `hp` and `hb`. Twelve declarations completed in 35.545 s. | For an **arbitrary** 02HX test `α : Spec B → H.parameter` having the specified centre and residue-field isomorphism, construct the actual `i : Spec ℂ → Spec B` and prove `i ≫ α = p`, together with the base equation. The current proofs do not construct this test-dependent point. Boundary 1 is only partially complete. |
| **2. Family restriction** | `PresentationLifting` spells out the represented family as the literal `familyChange … ≫ H.evaluation`. `CentralCoefficient.familyChange_centre` and `evaluation_restrict` prove that its restriction is exactly the original fibre evaluation. These are actual scheme-map equalities, including arbitrary witnesses of the base equations. | Application to every 02HX test still depends on constructing the `i` and compatibility from boundary 1. The restriction lemmas explicitly take those data as arguments. |
| **3. Small-extension ideal** | `SmallExtensionKernel` proves that a length-one module over a local ring is linearly isomorphic to its actual residue field, its annihilator is the maximal ideal, and maximal-ideal elements act by zero. For the literal `RingHom.ker`, it proves properness and the square-zero ideal equality. Seven declarations completed in 27.819 s. | Prove that flat base change of the actual source family identifies the ideal of `Y_B → Y_B′` with the sheaf arising from the actual kernel `I = ker(B′ → B)`. The algebraic kernel facts alone do not identify that sheaf or its scalar action. |
| **4. Cotangent and tangent coefficients** | `CentralCoefficient.pullbackRestrictionIso` and `centralCoefficientIso` give the actual pullback-composition/map-equality isomorphism for arbitrary coefficient `E`. The tangent specialization has the exact original evaluation map and tangent sheaf. | Prove the internal-Hom, locally free dual, tensor, and closed-fibre pushforward comparisons for the actual thickening ideal. In particular, the obstruction sheaf has not yet been identified with the pushforward of the central tangent coefficient tensored with `I`. |
| **5. Cohomology support** | `FiniteFirstCohomology` proves finite-coproduct preservation and reflection of the actual Yoneda extension-splitting predicate, including the empty family; three declarations completed in 33.165 s. `centralCoefficient_h1_iff` uses the existing proved `FirstCohomology.iso_iff`. `centralTangent_h1` transfers the exact original `hH1` to the tangent coefficient restricted to the central fibre. | The abelian-sheaf/scalar-restriction comparison along the nilpotent closed fibre, the cohomology comparison for the actual obstruction sheaf, and compatibility with a residue-field basis of `I` remain open. Central-fibre vanishing is not a proof of vanishing on the whole Artinian family. |
| **6. Lift and universal property** | Root's `RelativeHomLifting.lift_iff_family` proves the all-test functor lifting equivalence. `PresentationLifting.lift_iff_evaluation` and `point_lift_iff_evaluation` specialize it to the supplied project `Presentation`, its actual evaluation, and the original base equations. The four-declaration specialization completed in 36.494 s, with no extra geometric premises. | Obtain the actual global family lift by the proposed obstruction input after proving its actual vanishing premise. The completed equivalence then translates that lift to the desired parameter lift; it does not create the family lift. |
| **7. Pointwise-to-open** | `SmoothLocusNeighborhood` proves that the actual smooth locus is a smooth open restriction and that membership of the actual field-valued point yields an open containing its whole image. It also accepts formal smoothness of the actual stalk map. Three declarations completed in 47.894 s. | Establish membership/formal smoothness at the point using the proposed 02HX criterion and the lifting argument for every permitted test. The ordinary open-neighborhood wrapper does not supply that criterion. |

## Exact scope of the central-coefficient result

Let `g` be the represented test-family evaluation, `g₀` the exact original central evaluation, and `j` the actual family-change map determined by a supplied compatible point `i`. The proved map equation is `j ≫ g = g₀`. The proved sheaf isomorphism is

\[
j^*(g^*E)\;\cong\;g_0^*E.
\]

For `E = tangentSheaf X.structureMap`, the proved consequence is vanishing of the original Yoneda first-cohomology predicate for `j^*(g^*E)`, directly from the original `hH1`. This is a central-fibre statement.

The substantial remaining coefficient comparison still has the shape

\[
\mathcal H om_{\mathcal O_{Y_B}}(g_B^*\Omega_{X/\mathbf C},J)
\;\cong\;
j_*\bigl(g_b^*T_{X/\mathbf C}\otimes_{\mathbf C}I\bigr),
\]

with the **actual** ideal `J` of the source thickening and the **actual** small-extension kernel `I`. It requires the flat-family ideal identification, compatible residue scalar structures, locally free duality, and the support/cohomology comparison. It has not been installed as a project-specific published input.

## The two proposed generic inputs remain proposals

1. **One square-zero thickening:** SGA 1, Exposé III, Proposition 5.1 and Corollary 5.2, printed pages 59–61 (arXiv PDF indices 74–76). For a literal square-zero closed immersion and its actual ideal, a smooth target, and an actual map from the closed subscheme, vanishing of the derived first cohomology of the actual internal-Hom obstruction sheaf gives a global extending map. The input must preserve the quotient/kernel data, structural equations and actual extension equation. It must not mention the project Hom presentation or conclude a smooth neighborhood. [Primary source](https://arxiv.org/pdf/math/0206203); corresponding lift-sheaf statements: [Stacks 04FH](https://stacks.math.columbia.edu/tag/04FH), [04FJ](https://stacks.math.columbia.edu/tag/04FJ), [04FK](https://stacks.math.columbia.edu/tag/04FK).

2. **Pointwise small-extension criterion:** [Stacks 02HX, Lemma 37.12.1, (4) ⇒ (1)](https://stacks.math.columbia.edu/tag/02HX). Keep the locally Noetherian base, locally finite type morphism, actual centre and residue-field isomorphism, and every literal small-extension test. “Small” means local Artinian rings, a surjection, and kernel of module length one as in [Stacks 02HS](https://stacks.math.columbia.edu/tag/02HS). Dual-number lifting alone does not replace these tests.

Neither input has been added by this progress record or by the ordinary proofs listed here. The original OBL-056 `sorry` and its written header remain unchanged.

## Evidence and inherited admissions

The central-coefficient module's ten declarations completed in **37.876 s**. Its focused dependency audit completed in **36.715 s**, traversing **31,783 constants / 179 project constants**, with no missing constants, custom project axioms or nonstandard axioms. The original `smooth_of_firstCohomology_vanishes` declaration is explicitly absent from that closure.

The first nine central declarations use only `propext`, `Classical.choice` and `Quot.sound`. The actual tangent specialization additionally inherits exactly `PublishedInputs.SheafFunctoriality.cotangentPresentation` through `tangentSheaf`. Its full printed type has SHA256 `a218eaeb1c06aa09472a97532fc408d0b621abcb4b4bacf421ba7c7b6ddcb63e`, identical to the previously accepted Point1 record. Its defining source, native module output and recursive source context also match that record. This is inherited eligibility, not a new publication review or a claim that the whole module is admission-free.

All listed pass results are complete **local diagnostic** receipts. Project imports retain their explicitly recorded older verified native pool where used; these results do not claim current resumed Step3h stock validation. Root independently read and rehashed the complete lifting, residue and central proof evidence. The full central handoff is `CENTRAL_COEFFICIENT_HANDOFF.json`, with a fetched-back exact 21-file evidence envelope. Failed earlier residue and kernel attempts remain preserved in their respective evidence histories.

The next small ordinary task proposed by root is a residue-point lifting lemma: for `f : T → X`, a point `t`, an isomorphism on the actual residue-field map at `t`, and a field-valued `p : Spec K → X` mapping to `f(t)`, construct `q : Spec K → T` with `q ≫ f = p` and `q(closedPoint K) = t`. This would address the still-open test-dependent portion of boundary 1. It has not yet been proved at the time of this note.
