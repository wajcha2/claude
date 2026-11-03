# Pullback preserves the specified rank: reference clarification

Date: 3 November 2026. Scope: the existing Step 3b leaf and its rank-one use in the first-jet proof. This is a citation and hypothesis comparison, not acceptance of the full current compilation graph.

## Finding

Preservation of the **same constant rank** is explicitly stated in primary mathematical sources. The existing Stacks reference should be supplemented with a precise rank statement. Stacks Lemma 17.14.3, Tag **01C8**, states preservation of local freeness and omits its proof; it does not itself display the rank clause. Tag **01C5** identifies the containing section, not that lemma. This clarification supplies more precise support for the historical Step 3b record; it does not establish a mathematical contradiction or revoke its historical acceptance.

The strongest directly inspected book reference is Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, author-hosted pre-publication version dated **27 July 2024**, §14.1.7, **Exercise 14.1.B(b)**, printed **page 402** (PDF page index 401). It treats an arbitrary morphism of ringed spaces and states that a locally free sheaf of rank `n` pulls back to one of rank `n`. Part (c) describes the inverse-image trivializing neighborhoods and their pulled-back transition matrices. The exercise introduces `n ∈ ℤ₊`, so the explicitly displayed formulation covers positive ranks.

An all-constant-rank formulation is Sarah Griffith, *Maps to Projective Space Defined by Global Sections of Invertible Sheaves*, **Proposition 2.12, page 4**. Section 2, beginning on page 2, assumes an arbitrary morphism of ringed spaces and a module sheaf on the target. Proposition 2.12 states preservation of constant rank and proves it by pulling back a trivialization with the same number of generators. There is no positive-rank restriction. This source is **author-hosted expository notes**; it is not being described as a peer-reviewed paper or a textbook edition.

Primary sources:

- [Vakil, 27 July 2024 pre-publication text, Exercise 14.1.B(b)–(c), p. 402](https://math.stanford.edu/~vakil/216blog/FOAGjul2724public.pdf).
- [Griffith, Proposition 2.12, p. 4; section hypotheses on p. 2](https://www.sarahcelestegriffith.com/assets/docs/Maps_to_Projective_Space.pdf).
- [Stacks, Lemma 17.14.3, Tag 01C8](https://stacks.math.columbia.edu/tag/01C8).
- [Stacks, Section 17.14, Tag 01C5, including the fixed-rank definition](https://stacks.math.columbia.edu/tag/01C5).

## Comparison with the actual Lean declaration

The current leaf in `source/RecompileBasePart04.lean` is:

```lean
theorem LeBrunSalamon.PublishedInputs.SheafFunctoriality.pullback_locallyFree
    {X Y : Scheme} (f : X ⟶ Y) {E : OModule Y} {r : ℕ}
    (hE : IsLocallyFreeOfRank E r) :
    IsLocallyFreeOfRank (pullbackModule f E) r
```

The declarations in `source/RecompileBasePart01.lean` expand its predicates as follows:

```lean
def IsLocallyFreeOfRank {X : Scheme} (E : OModule X) (r : ℕ) : Prop :=
  ∃ q : SheafOfModules.LocalGeneratorsData.{0} E,
    SheafOfModules.LocalGeneratorsData.IsLocallyFreeData q ∧
    ∀ i : q.I, Nonempty ((q.generators i).I ≃ Fin r)

noncomputable abbrev pullbackModule {X Y : Scheme}
    (f : X ⟶ Y) (E : OModule Y) : OModule X :=
  (Scheme.Modules.pullback f).obj E
```

| Lean data | Published mathematical meaning |
|---|---|
| `X`, `Y`, `f` | Schemes and their actual morphism; these supply a morphism of ringed spaces. Neither reference requires smoothness, properness, flatness, finite type, or a field. |
| `E : OModule Y` | A genuine sheaf of modules over the structure sheaf of the target. |
| `q.X`, `q.coversTop` | A family of open subsets covering the space. |
| `q.IsLocallyFreeData` | On every member of the cover, the canonical map from the free sheaf indexed by `(q.generators i).I` is an isomorphism. |
| `(q.generators i).I ≃ Fin r` | Every local basis has the same prescribed finite cardinality `r`. This is the usual constant-rank condition expressed by explicit generator data. |
| `pullbackModule f E` | The actual module-sheaf pullback functor, rather than only inverse image of the underlying sheaf of sets. |
| Conclusion with the same `r` | Local freeness with the unchanged rank, exactly the additional clause stated in the references above. |

These definitions add no contact, projective-embedding, first-jet, or LeBrun–Salamon hypothesis to the generic leaf. The cover and generator packaging is a literal presentation of finite local triviality; it does not hide a separate geometric application.

## Rank one in the first-jet argument

The first-jet modules use `LineBundle`, defined as a rank-one algebraic vector bundle, and its actual `pullbackLine`. For example, `LSFirstJetEmbeddingGeometry.lean` obtains quasi-coherence from `(pullbackLine f L).locallyFree` with `L : LineBundle Y`; `LSFirstJetEmbedding.lean` also pulls back line bundles and the projective hyperplane line bundle. These uses instantiate the preserved rank as **1**. Vakil's explicitly positive-rank statement therefore covers the first-jet use directly.

This observation does not replace the generic leaf's quantification over every `r : ℕ`. Griffith's Proposition 2.12 supplies the inspected all-rank wording; a book-only route can instead handle rank zero separately.

## Optional rank-zero proof

If one chooses to retain only Vakil as the admitted reference, a future Lean proof can separate `r = 0`: the input sheaf is locally isomorphic to the zero free sheaf, hence is zero by locality; the pullback functor, being a left adjoint, preserves the initial object; and the zero sheaf has rank zero. The positive-rank case then uses the cited book statement. This is a possible proof implementation, not a claim that such a zero-case proof has already been added or compiled.

## Evidence boundary

No proof source was changed, no Lean process was invoked, and no external library dependency or NYLL source was introduced for this reference clarification. No progress-ledger unit is promoted by this report alone. Whole-current-graph compilation and the native transitive trust audit remain separate acceptance requirements.

Inspected source hashes:

- `RecompileBasePart01.lean`: `46d783aa22de8543b21fe79accb874576a18c8fe68ffbf717a7e86f5dbce61bf`.
- `RecompileBasePart04.lean`: `fef347742972b6c8bd206648e25de31e98d980006400923e79782883d1ab5308`.
