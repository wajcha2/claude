# Publication eligibility of the two actual formal-trait proofs

The native closure contains **26 distinct admitted leaves**: 24 for the nodal theorem and 20 for the smooth theorem. **25 distinct leaves match documented generic published constructions or theorems.** The remaining leaf is the original project composite `Construction.Descent.TotalLine.projection_affine`; its generic replacement and actual Yoneda transport have been drafted and checked separately, but removal from these exact proof closures requires a fresh native audit.

The frozen proof snapshot passed 133 selected modules with no invalidations. The source review below does not claim canonical integration, reverse-cone replay or acceptance of all 43 point-1 obligations. Each JSON entry binds the exact declaration, native printed type, frozen source, output and transitive ancestry hashes.

| Direct admitted declaration | Publication decision | Primary locator |
|---|---|---|
| `Construction.Descent.TotalLine.projection_affine` | **Open: proved replacement required** | No exact project-composite primitive accepted; replace by proof. |
| `PublishedInputs.BaseChangeFibers.dualBaseChange_isIso` | Eligible generic published input | EGA I (1960), chapitre0,(5.4.5), canonical map(4.4.6); finite-rank convention at end(5.4.1) |
| `PublishedInputs.BaseChangeFibers.spec_pullback_isPushout` | Eligible generic published input | Lemma37.14.1 |
| `PublishedInputs.ClosedImmersionLocus.exists_open` | Eligible generic published input | Lemma76.49.3, specialized from algebraic spaces to schemes |
| `PublishedInputs.Cohomology.coherent_iff_finitePresentation` | Eligible generic published input | Lemma30.9.1(1)↔(3) |
| `PublishedInputs.Cohomology.ext1_unit_h1` | Eligible generic published input | Lemma20.5.1 |
| `PublishedInputs.Cohomology.h0_residue_baseChange_bijective` | Eligible generic published input | Robert, Theory of abelian varieties and their moduli spaces, draft stamp2023-03-07, AppendixA.1 LemmaA.1.1 third corollary bullet, printed pp81–82/PDFindices86–87; Ogus, base change notes, Proposition6 and Theorem8(2)–(3), printed pp3–5, canonical affine tensor form |
| `PublishedInputs.ConicQuadratic.reduced_normalForm` | Eligible generic published input | Tanaka, Discriminant divisors for conic bundles, arXiv2308.08119v2 (12 May 2024), §2.1(8), Proposition2.9(4), Corollary2.13(2), printed pp5–6,9–10,12 |
| `PublishedInputs.ConicQuadratic.smooth_iff_discriminant_ne_zero` | Eligible generic published input | Same version, Definition3.1 and Proposition3.12(1), printed p23 for the criterion |
| `PublishedInputs.ConicQuadratic.smooth_normalForm` | Eligible generic published input | Same version, Proposition2.9(4), Corollary2.13(3), printed pp9–10,12 |
| `PublishedInputs.EffectiveCartier.baseChange_line` | Eligible generic published input | Lemma31.15.5 |
| `PublishedInputs.EffectiveCartier.canonical_regular_and_zero_locus` | Eligible generic published input | Definition31.15.1, Definition31.15.6, Lemma31.15.9(2); Lemma31.15.10(1) |
| `PublishedInputs.EffectiveCartier.regular_zero_locus` | Eligible generic published input | Lemma31.15.10(2); Definition31.15.6 and Lemma31.15.9 |
| `PublishedInputs.LocalSplitting.finiteFreeQuotient` | Eligible generic published input | EGA I (1960), chapitre0,(5.4.9), printed p52 |
| `PublishedInputs.Picard.affineUFD_trivial` | Eligible generic published input | Lemma31.29.4(1) |
| `PublishedInputs.Picard.projectiveBundle_externalLineFactor` | Eligible generic published input | Kleiman, The Picard scheme (2005), convention printed p15, Exercise4.15 p33, Answer4.15 pp67–68 |
| `PublishedInputs.ProjectiveSpace.nonzero_quadratic_section_regular` | Eligible generic published input | §33.35.1, first paragraph; Lemma27.10.3 |
| `PublishedInputs.ProjectiveSpace.quadraticSections_bijective` | Eligible generic published input | Lemma30.8.1 and preceding monomial-basis paragraph; Lemma30.8.2 compatibility; Lemma27.10.3, canonical twist tensor multiplication |
| `PublishedInputs.ProjectiveSpace.quadraticVeronese_zeroModel` | Eligible generic published input | June27,2011 draft; Exercise7.4.D p158; §9.2.6, Exercise9.2.I, Remark9.2.8 p198; Exercise16.2.D p331; §17.4.5–6 p351; Exercise21.1.D p434 |
| `PublishedInputs.ProjectiveSpace.segreQuadric` | Eligible generic published input | Lemma27.13.6, construction and displayed coordinate order; Vakil, FOAG classes15–16 (2007), §5 Exercise5.B and Example5.1, printed pp16–17 |
| `PublishedInputs.ProjectiveSpace.standardAffineCharts` | Eligible generic published input | Lemma27.13.3 and relative projective-space construction; Lemma27.16.10, arbitrary-base polynomial Proj identification |
| `PublishedInputs.ProjectiveSpace.standardTautological` | Eligible generic published input | Definition27.10.1 and Lemmas27.10.2–3; multiplication-by-Xi frame; Lemma27.13.1 and relative characterization after Definition27.13.2 |
| `PublishedInputs.RelativeCartier.near_closed_point` | Eligible generic published input | Lemma31.19.9(2); Definition31.14.1 |
| `PublishedInputs.SectionRepresentability.finiteFree` | Eligible generic published input | EGA IV(4),(18.5.1), printed p125 |
| `PublishedInputs.SheafFunctoriality.pullback_locallyFree` | Eligible generic published input | Definition17.14.1(3), Lemma17.14.3 |
| `PublishedInputs.SheafFunctoriality.pullback_tensorProduct` | Eligible generic published input | Lemma17.16.4 |

## Precise remaining gate

The new `PublishedInputs.SectionRepresentability.finiteFree_affine` has an exact source: EGA IV(4), (18.5.1), printed p125, together with the affine relative-spectrum construction in Stacks 01M1, 01LP and 01LV. It asserts existence of an affine representing object for the actual section functor. The passage to the supplied `TotalLine.projection` is a Lean proof using naturality and uniqueness over the base. The old admission must disappear from a fresh exhaustive native leaf inventory before either final root is marked publication-boundary accepted.

The review found no further missing hypothesis or false statement in these 26 leaf types. In particular, Tanaka’s characteristic condition is in the residue field; the local Cartier criterion retains both flatness hypotheses and finite presentation; and the universal closed-immersion locus really has the proper-source/separated-target scope used here.

Full exact type, per-root shortest dependency paths, hypothesis and map comparisons, primary URLs and hashes are in `PUBLICATION_ELIGIBILITY.json`.
