# Published-input boundary audit (read-only source inspection)

Audit date: 3 November 2026. Source inspected: cumulative Step 3g V2 archive, SHA-256 `722c44bc3e21211634732fc92fb0d598b429f886ac85dec3d3699318d4a3fe32`. No Lean invocation or mutation of the recovered source was performed in this audit. A separately saved repair candidate is described at the end. Line references below are to `cumulative/source` in the recovered archive.

## 1. Definite mathematical error: determinant lemma omits alternation

`RecompileBasePart05A.lean:208–214` declares `LeBrunSalamon.PublishedInputs.Step3e.symplecticDeterminant` for arbitrary schemes, a rank-`2*n` bundle `E`, a line `L`, and a bilinear morphism `b : E ⊗ E → L`. Its sole form hypothesis is `IsIso (currySheaf b)`. It concludes `det E ≅ L^n`.

This is false. Let `X` be a complex elliptic curve and let `T` be a nontrivial two-torsion line bundle. Choose `T ⊗ T ≅ O_X` and set `E = O_X ⊕ T`, `L = O_X`, `n = 1`. The orthogonal direct sum of multiplication on `O_X` and the chosen perfect pairing on `T` is a perfect symmetric bilinear form `E ⊗ E → O_X`. Thus its curry is an isomorphism, but `det E = T` is nontrivial. The claimed conclusion would trivialize `T`.

There is no implicit alternating constraint: `currySheaf` is the ordinary tensor/internal-Hom adjunction, `RecompileBasePart03.lean:2987–2992`. It is defined for arbitrary three modules `Z,E,F`.

The incorrect admitted lemma is actually used by `contact_distribution_determinant` at lines 218–225, so it is on the proof path. A compiler can accept the use because the false lemma has `sorry`; compilation does not certify the hypothesis audit.

### Minimal mathematical repair

Add alternation of `b` as an explicit hypothesis, e.g.

```lean
(hAlt : ∀ (U : X.Opens) (u : SectionsOn E.sheaf U),
  b.app U ((tensorPresentation E.sheaf E.sheaf).pair.apply U u u) = 0)
```

Then the generic conclusion is the Pfaffian determinant identity. For the contact application, alternation is already proved: `intrinsicLevi_alternating`, lines 112–117; its proof at lines 64–71 uses `TangentBracketProof.self_eq_zero`. The equality `tensorLift_pair` (`RecompileBasePart03.lean:1205–1208`) transports that result to the actual bilinear morphism used in the repaired hypothesis. No new mathematical assumption on contact manifolds is needed.

The exact all-schemes Pfaffian leaf still needs a primary reference matching its scope or a ring-level proof followed by gluing. Adding the missing premise alone is not full published-leaf certification.

Primary supporting reference checked: I. Biswas and N. Hoffmann, *Some moduli stacks of symplectic bundles on a curve are rational*, arXiv:math/0604183v2, section 2, printed p. 2, equation (1) and the paragraph immediately following it. It explicitly requires alternating and nondegenerate, gives `det(A)=lambda^n` for symplectic similitudes, then states the induced `det(E) ≅ L^n`. URL: https://arxiv.org/pdf/math/0604183 . This is a curve statement, so do not cite it as an exact theorem for arbitrary schemes without the local algebra/gluing step.

Another checked primary source: D. S. Freed, *On Determinant Line Bundles* (1987), section 3, equations (3.4)–(3.6), gives the complex-vector-space Pfaffian and its square equal to the determinant, with skew-symmetry explicit. URL: https://abel.math.harvard.edu/~dafr/detsur.pdf . Again, this is a precise algebraic ingredient, not the entire general sheaf statement.

## 2. First-jet obligation has been renamed, not discharged

`LSClassicalReduction.lean:37–47` has a `PublishedInputs.Step3e.polarizedEmbedding_firstJets` theorem with exactly the old project interface:

```lean
(X : SmoothProperComplexVariety d) (L : LineBundle X.scheme)
(E : PolarizedProjectiveEmbedding X L) : SeparatesFirstJets X L := by sorry
```

The old name merely invokes this new name. The Step 3e plan explicitly says that `polarizedEmbedding_firstJets` is to be proved from the actual closed immersion and fat-point restriction, not treated as a literature leaf. The source's comment gives the affine-chart/cotangent-quotient argument, but that argument has not become a Lean proof.

This is a boundary-policy failure, not a claim that very-ampleness fails to separate first jets. The mathematical consequence is standard. The missing work is the required statement/coordinate/jet-restriction bridge in this formalization.

## 3. Normalized source bivector remains a project-specific admission

`RecompileExtensionsPart01.lean:3645–3653` admits `PublishedInputs.ProjectiveLineGeometry.normalizedSourceBivector`; `sourceBivector_existsUnique` at 3656–3663 is only an alias.

The admitted conclusion still mentions `identityCurveContact`, `ExternalSquareSections`, `VanishesQuadraticallyAlongDiagonal`, and `HasNormalizedContactSymbol`. The only explanatory comment says that this is the standard diagonal-divisor/Picard calculation on `P¹ × P¹`; it gives no precise publication locator. The original Step 3g plan explicitly required the normalized source bivector to be proved.

The expected mathematics is elementary and plausible: `I_Delta = O(-1,-1)`, so `I_Delta^2 ⊗ O(2,2) ≅ O`; the section is `(z-w)^2 ∂_z ⊗ ∂_w`. But the normalization, symmetry, coordinate independence, and identification with the actual symbol need proof. The new name supplies none of those steps.

## 4. Laurent expansion is explicitly a composite corollary

`LSCurveLaurentStandardInputs.lean:40–46` admits `laurentExpansionAtPole`; the previous theorem at 49–56 simply invokes it. The statement constructs an `ℂ`-algebra embedding of the function field of an integral affine complex curve into `ℂ((t))` such that a prescribed nonconstant regular function has negative order.

The comment itself calls the result a combination of compactification and boundary-DVR theory and cites five Stacks tags. Those tags were checked:

- 0BXW, Lemma 33.43.6: compactification of a reduced curve with discrete valuation local rings at the boundary.
- 04L2, Lemma 33.26.2: regular functions on a proper geometrically integral variety are constants.
- 00MC, Lemma 10.97.3: faithful flatness of local completion.
- 07NU, Section 15.44, particularly Lemma 15.44.5: a local ring is a DVR iff its completion is.
- 0C0S, Lemma 10.160.10: a complete regular equicharacteristic local ring is a power-series ring over the residue field, with the stated coefficient-field structure.

These are legitimate ingredients, but none is the admitted composite. The project plan requires the bridge: choose a boundary pole, establish the residue field and injective completion map, identify the completed DVR as `ℂ[[t]]`, extend to fractions, and prove the negative Laurent valuation. No falsehood was found in the intended final claim.

## 5. The same issue persists in Steps 3c and 3f

Examples:

- `RecompileExtensionsPart01.lean:1861–1866`: `smooth_diagonal_secondDerivatives_detect` is a direct `sorry`. The comment combines the regular diagonal's associated graded, `I/I² ≅ Ω`, and finite-projective duality. The original plan explicitly required deriving this second-derivative detection lemma.
- `RecompileExtensionsPart01.lean:1658–1670`: `diagonalRestriction_iff_quotientCoefficients` is still admitted in the exact project affine-frame/coefficient interface. It cites several facts but does not prove their composition.
- `LSNodalFixedEnds.lean:64–77`: `dualThickening_hom_vanishing` explicitly says in its comment that it is a derived classical corollary, not a verbatim published lemma, yet is directly admitted.
- `LSFormalTraitModel.lean:135–156`: `formalTrait_twoComponent_lineNormalForm` admits the whole model isomorphism and line-bundle identification. The comment sketches a construction through `Mbar_0,4`, sections, and degree-zero triviality. It does not supply one exact published theorem with this conclusion.
- `LSHomVelocity.lean:145–151`: the normal-form statement still directly mentions the project's `Lines.DualThickening` and `normalForm`. A generic relative-Spec theorem must be separated from its actual coordinate proof if following the accepted plan strictly.

These examples establish that the alleged published-leaf count is not an accepted count of exact published theorems. They do not prove every renamed statement is false.

## 6. Some candidate inputs genuinely match standard theorem families

The audit should not reject all classical facts merely because they are expressed in Lean.

- The universal property of projective space is real: Stacks Section 27.13 (Tag 01ND), Lemma 27.13.1, states representability of invertible sheaves with `N+1` generating sections. The actual lemma's tag is reached via its link; 01ND itself is the section. The project `ProjectiveCoordinates` still needs a documented translation to the specific Proj/base-change object and section maps.
- Degree-zero Künneth is real: Stacks Lemma 33.29.1 (0BED) gives a canonical tensor-product cohomology isomorphism under quasi-compactness and affine-diagonal assumptions. `kunneth_degreeZero_surjective` at `RecompileBasePart05C.lean:683–689` specializes this to proper smooth complex schemes and expands tensors as finite sums. The specialization and finite-sum expansion are straightforward but, under the accepted exact-leaf rule, belong in the wrapper proof.
- Projection formula is real: Stacks Lemma 20.54.2 in Section 20.54 (01E6) supplies the finite-locally-free projection formula. The project statement at `RecompileBasePart05C.lean:748–753` also specializes to `f_*O_X = O_Y` and takes global sections. Those translations are distinct from the published leaf.
- Constancy of Euler characteristic is real: Stacks Lemma 36.32.2 (0B9T). `familyDegreeConstant` in `LSContactLineTests.lean:41–57` combines it with Picard classification and `χ(O(d)) = d+1`, as its own comment acknowledges.
- Birkhoff–Grothendieck and `Pic(P¹)=ℤ` are appropriate leaf families. Their use with the chosen `ProjectiveLineOverC`, marked-point twists, and splitting interface needs the equivalence audit the plan already requires.

## Recommended acceptance rule

Maintain distinct fields for (a) admitted declaration, (b) exact published theorem with stable locator, (c) verified translation of hypotheses and conclusion, (d) Lean wrapper proof, and (e) successful kernel verification of that wrapper and its affected dependency cone. A `PublishedInputs` prefix or lack of a direct `sorry` in an alias is not sufficient.

For every newly named leaf, compare the *expanded mathematical statement*, not its name, against the source. Multiple published ingredients must be admitted separately and their composition proved. Incorrect statements must be repaired before recompilation. Do not count such repairs as fully certified until the amended source has passed its incremental build and the published-boundary review.

For the user-facing status: the current cumulative source does not meet the first milestone, even if all pending compilation were to succeed unchanged. It contains at least one false admitted input and several direct admissions expressly excluded by the accepted plan.

## Separately preserved minimal repair candidate

At the root agent's request, a candidate copy is saved as `../repairs/RecompileBasePart05A.lean`, with its unified diff at `../repairs/symplectic_determinant_alternation.patch`. The recovered file remains untouched.

- Original file SHA-256: `a08103402653960105581427d25a5354fd78d6edb8c519831f28c0bab94ccc72`.
- Candidate file SHA-256: `33a16dfc0235fa9846bc4f71aa085f1863c9554068fd325edf03137608829fa2`.
- The only change is the determinant input's explicit `hAlt` premise, an explanatory status comment, and the contact caller's proof of that premise through `tensorLift_pair` and `intrinsicLevi_alternating`.
- The caller now uses `C.sequence` explicitly when passing the intrinsic contact sequence to `intrinsicLeviMorphism` and `intrinsicLeviPair`.
- Direct `sorry` count in this module is unchanged at one; no new admission was introduced.
- Kernel status: **NOT COMPILED**. Exact full-scope published-input audit: **PENDING**.

The repair restores the mathematically necessary hypothesis. It is not yet a certified formalization step or a completed exact published leaf.

## Continuation work after authorization to pursue the milestone

The recovered source and the minimal repair above remain preserved. The following work is in `../continuation/source` and is a candidate until kernel replay succeeds.

### Determinant boundary narrowed and source located

The unrestricted `symplecticDeterminant` admission has been replaced by `PublishedInputs.Step3e.alternatingDiscriminantTrivial`, restricted to a smooth proper connected scheme over the actual complex base. Its source is Asher Auel's 2009 Penn dissertation, *Cohomological invariants of line bundle-valued symmetric bilinear forms*, Proposition 1.10 (printed p. 15), together with Definition 1.7 (p. 13). The admitted conclusion is only the underlying-line part of the published trivial-discriminant statement. The chapter assumes noetherian separated connected schemes (p. 5), and Section 1.2 assumes 2 invertible (p. 12). Smooth proper complex schemes satisfy these conditions; the wrapper supplies their actual structure map and existing instances. The regularity definition (p. 7) is the adjoint-map isomorphism. Source: <https://math.dartmouth.edu/~auel/papers/docs/AUEL_thesisSS.pdf>.

In `RecompileBasePart05A.lean`, `SymplecticDeterminantProof.dualPower_evaluation` constructs the inverse tensor-power evaluation from the already proved line-dual evaluation. `determinant_of_discriminantTrivial` then constructs the desired determinant isomorphism by tensor associativity, commutativity and unit isomorphisms. The theorem `symplecticDeterminant` is now a proved wrapper; the contact caller also proves alternation. There is still exactly one direct `sorry` in Part05A, now at the explicitly sourced discriminant leaf.

### Direct first-jet proof candidate

The direct `sorry` at `PublishedInputs.Step3e.polarizedEmbedding_firstJets` has been removed and replaced by a call to `FirstJetProof.projectiveEmbedding_firstJets`. No admitted helper was added. Two new modules contain the actual argument:

- `LSFirstJetEmbedding.lean`: transports the original sheaf-valued jet map to the existing local coefficient normalization; forms constant linear combinations of actual global sections; proves that projective immersivity of their coefficient tuple supplies every first jet; proves preservation of generating tuples under pullback and universal-coordinate uniqueness on arbitrary test schemes.
- `LSFirstJetEmbeddingGeometry.lean`: constructs the dual-number map associated to each point derivation through the actual affine chart and its canonical ring comparison. It constructs pulled line frames with their exact coefficients. A radial coordinate derivative is multiplication by the explicit unit `1 + epsilon * k`; the universal quotient therefore identifies the two projective morphisms. The actual closed immersion is a monomorphism, so its tangent kernel vanishes. The finite-contraction lemma produces the original fat-point jets.

This uses the full test-scheme universal property already present in `ProjectiveCoordinates`, including nonreduced schemes. It needs no choice of fixed homogeneous chart or additional projective tangent theorem. The original public target and its wrapper remain unchanged. `LSClassicalReduction` now has three direct admissions rather than four. The local import graph was checked to be acyclic. **These changes are source candidates, not kernel-certified results; diagnostic and full replay receipts must remain distinct.**
