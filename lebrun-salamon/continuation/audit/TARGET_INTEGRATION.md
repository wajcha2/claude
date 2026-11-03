# Exact target integration and topology bridge

## Status

Three new Lean modules implement the frozen statement inside the existing import graph, explicit metric-data transports, and the topological part of the final assembly. They introduce **zero** `sorry`, `admit`, custom `axiom`, or `opaque` declarations. They are currently **uncompiled**. Their static source audit is `TARGET_INTEGRATION_SOURCE_AUDIT.json`.

The unconditional frozen theorem is **not** proved. The completed source assembly is explicitly conditional on `PositiveQKSimpleConnectedness`, and it continues to inherit the existing proof tree's admissions. No admission has been added to fill the remaining topology gap.

## Frozen statement preservation

`target/MainStatement.lean` is unchanged, with SHA-256:

`9afe9c5b2e63db17e8f217b71c821eaca83fe26c5cfbc2956fc1b92832d09296`.

The Riemannian core in that file and in `source/RecompileBasePart01.lean` is identical after comments and whitespace are removed. The normalized core hash is `27fc34de5a8b48f7ec28f0d59f5d705cd5bab12e58b5b6e58d2c8a795eebf233`. Thus importing the existing core avoids duplicate declarations without changing the operational definitions of positive quaternionic-Kähler structure or parallel curvature.

`LSMilestoneStatement.lean` imports `RecompileBasePart01` and contains the entire `LeBrunSalamon.AuditedStatement` namespace payload byte-for-byte from the frozen file. Its payload hash is `69ec424a6d47486e562316983c2c6c8e187e379c9377989270a1a56a01ccbba3`. Only the import/header and an explicit closing `end` for the file's noncomputable section surround the copied payload.

The source hypotheses therefore remain the original compact, connected, inhabited, smooth Riemannian manifold of real dimension `4*n`, with `2 ≤ n` and the original positive-QK predicate. Simple connectedness has not been inserted into the frozen proposition.

## Lean implementation

| Module | Implemented content | Remaining qualification |
|---|---|---|
| `LSMilestoneStatement.lean` | Importable exact audited structures and proposition, using the existing identical Riemannian core | Source identity checked; elaboration pending |
| `LSMilestoneTopology.lean` | Actual mathlib diffeomorphism and homeomorphism from each frozen metric homothety; simple connectedness in both directions; source simple connectedness from a Wolf homothety; actual point-symmetry involution and differential inner-product preservation | No new published theorem is used; elaboration pending |
| `LSMilestoneTarget.lean` | Skeleton/Audited space round trips; exact transports of homotheties and point symmetries; assembly of a Wolf model once its simple-connectedness field is supplied; exact reduction of the frozen endpoint to source simple connectedness | Inherits existing project admissions and leaves simple connectedness open |

The metric transports preserve the actual carrier, metric and manifold instances, equivalence and inverse, positive metric-tensor scale, and differential metric equation. They neither relabel an abstract space as a Wolf space nor replace a metric homothety by an existential label.

The new topology proof uses the existing smooth equivalence to construct `Diffeomorph`, then `Homeomorph`, then applies mathlib's `ContinuousMap.HomotopyEquiv.simplyConnectedSpace_iff`. The relevant APIs are documented in [Diffeomorph](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Diffeomorph.html), [Homotopy.Equiv](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Homotopy/Equiv.html), and [FundamentalGroupoid.SimplyConnected](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.html). The pinned-toolchain elaboration remains the authority on the exact available API.

The strongest new assembly statement is:

```lean
theorem leBrunSalamonStatement_iff_sourceSimpleConnectedness :
    AuditedStatement.LeBrunSalamonStatement n M ↔
      (2 ≤ n → IsPositiveQuaternionicKahler n M → SimplyConnectedSpace M)
```

Its forward direction uses only the actual Wolf homothety and topology. Its reverse direction obtains the existing `SymmetricHomothety`, transports simple connectedness of the source along its actual diffeomorphism to the target, and supplies the missing Wolf-model field. The reverse direction relies on the current project proof tree, including its unresolved admissions. Consequently this equivalence is a precise interface reduction, not an independent proof of either side.

The separately named conditional endpoint remains:

```lean
theorem leBrunSalamonStatement_of_simpleConnectedness
    (hSC : PositiveQKSimpleConnectedness) :
    AuditedStatement.LeBrunSalamonStatement n M
```

## Exact remaining geometric bridge

The missing consequence is simple connectedness for a closed connected positive quaternionic-Kähler manifold. The classical source candidate is Simon Salamon, *Quaternionic Kähler manifolds*, Inventiones Mathematicae **67** (1982), 143–171, DOI [10.1007/BF01393378](https://link.springer.com/article/10.1007/BF01393378), Theorem 6.6, p. 163. The theorem locator is corroborated by the introduction of [Tachibana-type theorems and special Holonomy](https://link.springer.com/article/10.1007/s10455-022-09837-1), which uses holonomy contained in `Sp(n)Sp(1)` and explicitly attributes simple connectedness of positive QK manifolds to that theorem. The full 1982 theorem text was not accessible in the inspected publisher page, so its precise original wording and surrounding hypotheses have not yet been accepted as a completed leaf audit.

Salamon's own [Quaternion-Kähler Geometry survey](https://archive.intlpress.com/site/pub/files/_fulltext/journals/sdg/2001/0006/0001/SDG-2001-0006-0001-a005.pdf), pp. 85–88, explains local quaternionic endomorphism frames preserved by the Levi-Civita connection, gives the holonomy definition, and defines positive QK using completeness and positive scalar curvature. That primary account supports the intended mathematical interpretation. It does not supply Lean proofs that the project's operational predicates agree with the standard definitions.

Before installing a permissible exact published input, the relevant Step 2 obligations remain: operational smooth endomorphism fields versus intrinsic smooth sections; the parallel local rank-three quaternionic bundle versus the holonomy formulation; identification and uniqueness of the actual curvature witness and sign convention; scalar contraction/basis independence; and the required compactness-to-completeness specialization. The new topology module proves the homothety transport itself. It does not claim to discharge those geometric definition bridges or the full point-symmetry/distance-isometry equivalence.

## Acceptance checklist proposal

A defensible fixed count for the remaining milestone is **153 acceptance units**: the original 91 nonpublished obligations; the 50 published-namespace leaf candidates present at takeover; the eight Step 2 definition-validation obligations; and four final gates (exact frozen endpoint, dependency-complete compilation, transitive trust audit, and reproducible locked checkpoint). Splitting an existing obligation or leaf refines its acceptance test without increasing the denominator. Newly discovered work must be attached to its governing obligation/gate or trigger an explicit scope revision.

Credit requires the corresponding implementation, exact publication/hypothesis audit where relevant, and matching compiled dependency evidence. The original **43/91** wrappers that were source-refactored are a useful **47.25% source-rewrite indicator**, not 43 accepted milestone units. Likewise the new no-sorry transport modules are concrete progress within the target/definition gates; they do not earn an unconditional endpoint or publication-audit pass while the simple-connectedness bridge and compilation remain open. A final acceptance numerator must be calculated from individually recorded evidence, not line counts or the number of declarations written.
