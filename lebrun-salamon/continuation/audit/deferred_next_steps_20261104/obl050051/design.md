# Next 3i audit: OBL050 and OBL051

Date: 2026-11-04. Owner: `/root/published_leaf_audit`.

**Scope: read-only design and primary-source verification.** No Lean source was changed, no compiler was invoked, no Git tree/ref was written, and no new admission or acceptance credit is proposed by this document. The current 3h candidates remain frozen. This audit concerns the unchanged original statements and gives a possible implementation boundary for later approval.

## Recommendation

Build one genuine relative-Hom construction, retaining its actual evaluation map, and prove the project comparison around it. Use the fixed graph-Hilbert-polynomial pieces of that construction for `degree_open`; transfer them to an arbitrary supplied `HomSpacePresentation` through a proved canonical scheme isomorphism.

The all-test issue has a precise generic solution: **SGA 3, Exposé XI, Remark 3.4** gives the extension criterion for a Zariski sheaf commuting with filtered ring colimits. Its hypotheses must be discharged for the actual Hom functor. This avoids silently treating FGA's locally Noetherian convention as an all-test theorem.

The degree proof then has two substantive comparisons: the very ample power must be a power of the **given** line bundle, and its graph polynomial must be related to the project's **twist-exponent** degree. Neither comparison is contained in the original `degree_open` placeholder.

## 1. Exact current obligations

The read snapshot is `lebrun_recovery/source-checkpoint/source`. `SOURCE_GUARDS.json` records complete target hashes and exact extracted contracts.

| Obligation | Current location | Exact extra data required by its conclusion |
|---|---|---|
| OBL051 | `RecompileExtensionsPart01.lean`, `Skeleton.homSpacePresentation_exists` | A **scheme**, a map to `ComplexBase`, an evaluation on the actual pullback `RationalSourceOver`, and evaluation-induced bijections for **every** scheme `T → ComplexBase` |
| OBL050 | `LSHomDegree.lean`, `Lines.HomDegree.StandardInputs.degree_open` | An open-and-closed subset of the **supplied** `H.parameter`, with locally finite type and quasi-compact structure map, and the stated membership equivalence for every complex point |

OBL051 assumes `P : ProjectiveLineOverC`, `X : SmoothProperComplexVariety d`, and the separate `HasProjectiveEmbedding X`. Projectivity is not a field of `SmoothProperComplexVariety`. The target `HomSpacePresentation` has no finiteness, smoothness, reducedness, or quasi-compactness field. Its universal property is explicitly evaluated on nonreduced and non-Noetherian tests as well as ordinary complex points.

OBL050 additionally assumes a line bundle `L`, `IsAmpleLine L`, a marking `p`, and any integer `e`. The finite-type and quasi-compactness fields are essential: local constancy of degree by itself proves neither. An empty locus is permitted, so the proof must not add `0 ≤ e` or nonemptiness assumptions.

## 2. Primary sources and their actual scope

### 2.1 Hom construction and bounded graph pieces

Grothendieck, Bourbaki exposé 221, §3 explicitly restricts test schemes to locally Noetherian ones for convenience. Theorem 3.2 constructs the projective fixed-Hilbert-polynomial pieces; §4(c) constructs Hom as an open part of Hilbert when the source is projective and flat and the target is quasi-projective. The graph-polynomial pieces are open and closed in Hom and quasi-projective over the base. See printed pp. 259 and 267–268, PDF pp. 12 and 20–21. The checked erratum does not change §4(c). These statements provide geometric boundedness, but their test-category convention must be handled explicitly.

Primary source: [Grothendieck, exposé 221](https://www.numdam.org/item/SB_1960-1961__6__249_0.pdf). [Correct erratum](https://www.numdam.org/item/SB_1961-1962__7__302_1.pdf).

Nitsure's author exposition, Theorems 6.5–6.6, gives the corresponding graph/Hom construction. Its §1 also defines the test category using locally Noetherian schemes. It is useful corroboration, not an independent removal of this restriction. [Nitsure, *Construction of Hilbert and Quot Schemes*](https://arxiv.org/pdf/math/0504590).

### 2.2 Exact upgrade to arbitrary test schemes

**SGA 3, Exp. XI, Remark 3.4** states the general criterion needed here: if a functor is a Zariski sheaf and commutes with filtered colimits of rings, and a locally finitely presented scheme maps to it by a transformation bijective on locally finitely presented tests, that transformation is an isomorphism on all tests. The French primary text was checked in the editor-hosted revised edition, PDF p. 11 / printed p. 95, with original pagination 143. Its preceding Remark 3.2 specifies the relative limit condition.

Primary source: [Grothendieck, SGA 3, Exp. XI, §§3.2–3.4](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo11.pdf).

For the Hom functor, [Stacks 01ZM](https://stacks.math.columbia.edu/tag/01ZM) gives descent of finitely presented schemes, their morphisms, and equalities along affine-transition limits. [Stacks 01ZC](https://stacks.math.columbia.edu/tag/01ZC) identifies locally finite presentation with the relevant limit preservation for represented functors. The remaining Zariski-sheaf property is actual gluing of morphisms on the base-changed source. This is a proposed proof route, not a claim that these translations are already formalized.

The criterion is generic enough to be reused for OBL054 if that obligation supplies the same precise finiteness and evaluation hypotheses. No conclusion about OBL054's uninspected details is assumed here.

### 2.3 What the Stacks Hom results do and do not supply

[Stacks 0D1A](https://stacks.math.columbia.edu/tag/0D1A) defines the actual graph transformation; [0D1B](https://stacks.math.columbia.edu/tag/0D1B) makes it representable by open immersions. These formulations allow all scheme tests. [0D1C](https://stacks.math.columbia.edu/tag/0D1C), under finite-presentation, separation, flatness, and properness hypotheses, represents Hom by an **algebraic space**. That conclusion alone does not fill the project's `parameter : Scheme` field. Projectivity or a separate scheme-representability argument must remain visible.

The Hilbert **scheme of points** does not apply to one-dimensional graphs. Likewise, a sheaf-Hom representability theorem concerns module homomorphisms rather than maps of schemes. Neither is a replacement for OBL051.

### 2.4 Given ample line and degree normalization

[Stacks 01PS](https://stacks.math.columbia.edu/tag/01PS) defines ampleness by quasi-compactness and affine nonvanishing opens of positive tensor powers. This matches the project's intended predicate after its existing section/tensor-power normalization. [01VG](https://stacks.math.columbia.edu/tag/01VG), Lemma 29.38.5, compares absolute and relative ampleness over an affine base. [01VU](https://stacks.math.columbia.edu/tag/01VU) says that, over a quasi-compact base and for a finite-type morphism, some positive power of a relatively ample invertible sheaf is relatively very ample. The definition of relative very ampleness retains an actual pullback identification with the hyperplane sheaf; see [01VL](https://stacks.math.columbia.edu/tag/01VL).

[Stacks 01XT](https://stacks.math.columbia.edu/tag/01XT), the cohomology calculation for twists on projective space, supplies the standard numerical computation on `P¹`. Its specialization gives `χ(O(k)) = k + 1` for every integer `k`. Using that statement in the project still requires identifying the project's twist sheaf with the standard one; a numerical splitting-profile identity is not itself this geometric identification.

## 3. Concrete interface for OBL051

The following are mathematical interfaces, not asserted Lean declarations or compilable code. Names can be chosen during implementation without changing either original public statement.

### A. Generic relative Hom data

For actual scheme maps `z : Z → S` and `x : X → S`, retain:

- a scheme `H` and actual map `h : H → S`;
- an evaluation `ev : Z ×_S H → X` with `ev ≫ x = pr₁ ≫ z`;
- for each test `t : T → S`, a bijection **given by this evaluation**, from maps `T → H` over `S` to maps `Z ×_S T → X` over `S`.

The generic published construction should use the ordinary projective/flat source and quasi-projective target hypotheses, rather than `ProjectiveLineOverC`, contact structures, or a project-selected family. If the admitted construction is stated only for locally Noetherian tests, the lfp structure map of `H` and its universal evaluation must be part of that input, and the upgrade below must be proved separately. No extra hypothesis is to be added to the project's original theorem.

Ordinary references often write the target as `Hom_T(Z_T, X_T)`. The project writes maps `Z_T → X` over `S`. Their correspondence must use the actual pullback lift/projection and prove both inverse identities. This is small categorical comparison work, not a further geometric input.

### B. All-test upgrade with the same evaluation

Write `F(T) = Hom_S(Z ×_S T, X)` and let `η_T` be pullback followed by `ev`.

1. Prove the source base-change maps preserve identities and composition. This proves naturality of `η` for the exact evaluation formula.
2. Establish Zariski gluing for `F`: an open cover of `T` pulls back to a cover of `Z ×_S T`; compatible morphisms to `X` glue uniquely, and the over-`S` equation glues too.
3. For affine tests `Spec A` with `A = colim A_i`, prove the colimit comparison for `F`. Over `Spec ℂ`, the finitely generated `ℂ`-subalgebras form a suitable filtered system; finite presentation of the source and target gives descent and eventual equality of maps. Retain the over-base equations while descending.
4. Apply the generic criterion of SGA 3 XI 3.4 to the FGA evaluation transformation. A locally finitely presented test over the Noetherian base is locally Noetherian, so the verified restricted universal property applies.
5. Instantiate `Z`, `z`, `X`, `x` by the actual `ProjectiveLine`, `P.structureMap`, `X.scheme`, and `X.structureMap`. The resulting bijections fill `HomSpacePresentation.universal` literally.

Alternatively, the same argument can be implemented directly: extend the bijections first on affine tests by filtered colimits, then glue on arbitrary tests. The important output is the exact evaluation-induced map, not merely an abstract equivalence between two sets.

### C. Source-order and projectivity checks

`ProjectiveLineOverC` contains a chosen degree-zero spectrum isomorphism. Its structure map must not be silently replaced by a canonical map. Earlier `CotangentTwistProof.structureMap_smooth` provides smoothness of that actual map. The `ProjectiveLineProof.projectiveLine_smoothProper` and `projectiveLineVariety` declarations in Ext01 occur **after** OBL051, so a proof inserted at OBL051 cannot simply use them without an explicit independent reorganization.

The already-present generic polynomial-Proj smooth/flat/proper ingredients are preferable for an early independent source certificate. The target's `HasProjectiveEmbedding` must be unpacked into its closed immersion and its actual over-`ℂ` equality. Its chosen projective-space base isomorphism also requires proper normalization. These are implementation boundaries, not missing mathematical hypotheses.

## 4. Canonical comparison of arbitrary presentations

This project theorem should be proved without any published input. Let `H` and `K` be two `HomSpacePresentation P X` values.

Use `K.universal H.parameter H.toC` to select `u : H.parameter → K.parameter` over `ℂ` such that

`rationalSourceMap P u ≫ K.evaluation = H.evaluation`.

Use `H.universal K.parameter K.toC` analogously to select `v`. Prove the pullback-map identity and composition lemmas by `pullback.hom_ext`, then postcompose the two evaluation equations. Injectivity of `H.universal` at `H.parameter`, and of `K.universal` at `K.parameter`, gives `u ≫ v = 𝟙` and `v ≫ u = 𝟙`. Thus `u` is the required scheme isomorphism over the base.

Recommended interface:

| Output | Required equation |
|---|---|
| `iso : H.parameter ≅ K.parameter` | actual inverse scheme maps |
| base compatibility | `iso.hom ≫ K.toC = H.toC` |
| evaluation compatibility | `rationalSourceMap P ⟨iso.hom, baseCompatibility⟩ ≫ K.evaluation = H.evaluation` |
| point compatibility | for every `t`, `K.mapAt P (t ≫ iso.hom) = H.mapAt P t` |

The point identity follows from the evaluation identity and the same pullback projection calculations; it is not a new axiom. No finite-type assumption on the arbitrary supplied `H` is needed. In particular, the comparison must be constructed on the full parameter schemes, not deduced from a bijection on complex points.

## 5. Concrete reduction of OBL050

### A. Choose a polarization tied to the given line

From `IsAmpleLine L` and proper finite type `X/ℂ`, obtain a positive integer `m`, a suitable projective embedding `j`, and an actual sheaf isomorphism

`j* O(1) ≅ L^m`.

The existing `properAmpleClosedImmersion` does **not** provide this isomorphism: it takes existence of some ample line and produces an unspecified embedding. Reusing it alone would lose the link to the degree in OBL050. The positive-power result and its actual hyperplane comparison must be retained. Over the field, the finite-dimensional projective-space presentation can be normalized by a basis if the general relative very-ample definition initially uses a finite module.

### B. Compute the actual graph polynomial

Give `P¹ × X` the external product of the standard degree-one line on `P¹` and `L^m`. On the graph of an actual curve `f`, this restricts to

`O(1) ⊗ (f*L)^m`.

The implementation must construct this restriction isomorphism from pullback/tensor functoriality. Existing `StandardTautologicalP1.markedOneIso` identifies the standard degree-one line with `projectiveTwist P p 1`; existing Picard classification identifies `f*L` with its twist exponent. The proved degree tensor and power identities then yield the exponent

`1 + m * projectiveLineDegree P p (pullbackLine f L)`.

The geometric `P¹` twist cohomology calculation gives the graph Hilbert polynomial

`P_f(n) = (1 + m * projectiveLineDegree P p (pullbackLine f L)) * n + 1`.

This formula is a proposed derivation. Its value must not be inserted as an unexplained definition of a “Hilbert polynomial,” nor justified merely by `profile_riemannRoch`, which concerns predicted splitting numbers. It is enough to prove the comparison on complex points for OBL050's membership field, while the canonical Hilbert stratum itself supplies its scheme structure.

### C. Take the fixed polynomial piece and transfer it

For the requested integer `e`, take the canonical Hom piece with polynomial `P_e(n) = (1 + m*e)*n + 1`. Restricting the graph open locus to the projective fixed-polynomial Hilbert scheme gives a quasi-projective finite-type scheme over `ℂ`; it is quasi-compact because the ambient fixed-polynomial Hilbert scheme is Noetherian. The piece is open and closed within Hom. It need not be proper.

Pull this open set back along the canonical comparison `H.parameter ≅ Hcanonical.parameter`. Closedness follows by continuity. The induced isomorphism of the open subschemes transfers locally finite type and quasi-compactness of the maps to `ComplexBase`. Evaluation compatibility transfers the actual `mapAt` curve, so the polynomial calculation reduces membership to `m*degree = m*e`, then to `degree = e` using `m > 0`.

This works uniformly for negative `e` and empty loci. The already-proved independence of the marking confirms that no hidden choice of `p` changes the geometry, but the original `p` remains in the public statement.

## 6. Reuse and remaining formal work

| Existing source/API | Use or limitation |
|---|---|
| `PointsOver`, `RationalSourceOver`, `rationalSourceMap`, `HomSpacePresentation`, `mapAt` | Exact project functor/evaluation contract; no redesign needed |
| `InternalHomPresentation.comparison`, `comparison_comp`, `uniqueIso` in Base03 | A proved in-project pattern for universal-property comparison; these concern modules and cannot directly replace the scheme-Hom comparison |
| `projectiveLineDegree_spec`, `_iso`, `_independent`, `_tensor`, `_power` | Complete twist-degree arithmetic and classification normalization |
| `StandardTautologicalP1.markedOneIso`, `degree_one` | Actual standard hyperplane/twist-degree normalization |
| `NonvanishingLocusProof` and `SheafAmpleness.line_iff` | Existing translation of section and tensor-power presentations of ampleness; `SheafAmpleness.IsAmple` is a project predicate, not a Mathlib theorem |
| `LSStandardProjectiveSmooth`, `LSStandardProjectiveProper` | Generic standard-Proj smooth/flat/proper ingredients, subject to exact base-map normalization |
| `properAmpleClosedImmersion` | Existing embedding existence only; no prescribed `L^m ≅ j*O(1)` field |
| `profile_riemannRoch` | Integer profile arithmetic only; not by itself actual Euler characteristic or Hilbert polynomial |
| `Deformation.cotangentHom_bijective` | Useful to Source's OBL049/052 work after the actual Hom universal property; no need to place a tangent-isomorphism claim inside the representability input |

The pinned `Mathlib.lean` import index at commit `116662aa4c1e9106ab5c609b3214b02f6e11a65a` contains the standard projective-spectrum geometry modules but no dedicated Hom/Hilbert/ample module. This is an inspected API-index observation, not a claim of an exhaustive theorem-name impossibility proof.

Recommended implementation order after approval:

1. Prove the exact source-map identity/composition laws and the arbitrary-presentation comparison; these are zero-new-input categorical work.
2. Fix the generic published Hom/Hilbert interface and the generic all-test upgrade boundary, with citations and exact evaluation correspondence.
3. Establish the actual source/target projectivity and finite-presentation hypotheses before OBL051, without a source-order cycle.
4. Close OBL051 using the same universal evaluation on all tests.
5. Establish the prescribed ample-power/hyperplane and graph/twist-polynomial comparisons.
6. Assemble OBL050 by canonical-stratum transport; only then run its original statement and the changed/reverse-cone native gate.

The main remaining work is formal infrastructure and exact comparison, not a discovered missing hypothesis in either original theorem. This audit does not authorize an admission of `degree_open`, an all-test project Hom wrapper, or an unspecified canonical-map correspondence.

## 7. Cross-review of Root's OBL055 general functor probe

Read-only source reviewed: `root_diagnostics/next3i/LSRelativeHomFunctorTranslationProbe.lean`. It defines the actual morphism functor on every object of `Over S`, changes the target from `X/ℂ` to the pullback `X ×_ℂ S`, and constructs a `RepresentableBy` value from the project's relative presentation by the actual evaluation formula. The two target-change maps are the pullback lift and first projection; their directions agree with the project contract. This is a meaningful project comparison rather than a replacement label for its desired conclusion.

The proposed generic finite-presentation input is a mathematically valid **scheme-representer specialization** of Stacks 0D1C, not its literal printed syntax. Its exact justification should remain recorded:

- Properness supplies quasi-compactness and separation, hence quasi-separatedness. Together with local finite presentation this is finite presentation, by [Stacks 29.22.1](https://stacks.math.columbia.edu/tag/01TO), for both source and target.
- A scheme representing that same all-test morphism functor is isomorphic, as an algebraic space over the base, to the representer supplied by 0D1C. Yoneda uniqueness and invariance of local finite presentation transfer the conclusion.

The cleanest published-input header would expose source finite presentation/flat/proper and target finite presentation/separated, plus an actual scheme representation of the general functor. The proper-and-lfp formulation can then be a proved corollary. No scheme-existence conclusion should be extracted from 0D1C alone, and the project target-change/naturality proof should stay outside the published boundary. This assessment does not claim that Root's uncompiled probe or its proposed input has been accepted.
