# Fu route review after Point 1

**Decision:** retain the verified foundations and finish the five original 3h obligations next. Investigate a replacement for the later branch-descent argument before implementing its remaining inputs. This review changes no theorem, accepted unit, or dependency.

## Baseline and scope

Reviewed against accepted commit `bd3524b4bb12ac73cbf7572698208b017071b699`, whose compiled source is bound by `SOURCE.sha256` digest `e19bfd5e8fbd5a687b798edf53b2f645c53c90731ff078608c5be6effce45ee0`. Point 1 remains accepted at 74/133 units. A proposed replacement earns no credit until its actual translations, liveness changes, and current native dependency graph are verified.

## What the new paper changes

Baohua Fu, [*The classification of Fano contact manifolds revisited*, arXiv:2611.01423v1](https://arxiv.org/html/2611.01423v1), constructs twistor conics in §4. Section 5.2 treats a relative conic over a reduced affine base and proves regularity by cancellation at its nodal locus. Section 5.3 uses slice vector fields and their quadratic term, uniqueness of a general twistor conic, and birational descent from the coarse universal square. Lemma 3.3 still uses a theorem about finite covers and contact lines; finite-cover infrastructure is not automatically obsolete. These are the relevant differences for the existing formal architecture.

The original finite-cover source is Hwang–Mok, *Cartan–Fubini type extension of holomorphic maps for Fano manifolds of Picard number 1*, J. Math. Pures Appl. 80 (2001), 563–575, Lemma 4.2. Its statement is also explicitly recorded as Proposition 2.2 in Hwang, [*Deformation of holomorphic maps onto Fano manifolds of second and fourth Betti numbers 1*, arXiv:0908.2009](https://arxiv.org/pdf/0908.2009). This is a Picard-number-one result; the current contact-square base requires a separate comparison.

## Comparison with the actual formal interfaces

The findings below are deductions from the present definitions, not assertions that the paper already supplies those Lean comparisons.

| Current interface | Consequence for a Fu implementation |
|---|---|
| `ProjectiveNodalFamily` is a scheme family obtained from a finite stable-map-stack cover; its base is proper, integral and normal. | It is not definitionally the coarse unparameterized stable-map space. A finite-cover comparison must be constructed before importing a birational conclusion. |
| `FullHomComparison` has a finite surjective map to the full Hom open, a smooth surjective map to the family’s smooth locus, and an actual source isomorphism commuting with evaluation. | Parameterization and finite-cover data must be descended with their evaluation maps. One cannot simply declare `squareEvaluation` birational. |
| The completed nodal regularity interfaces use trait models with a discrete valuation ring. | Their explicit ring identities are reusable, but a relative chart over an arbitrary reduced base and the required gluing still need proofs. |
| `ProperPair` records an integral proper dominant source and two-vector data. | These fields alone do not establish normality, connected fibers, or the direct-image identity needed for descent. |
| `CoveredMovingPair` retains a full Hom neighborhood and the whole product of two projective lines, including the diagonal. | A replacement must preserve this actual coverage and its evaluation identities, or explicitly rebuild the later consumers. |

The existing `contactValueDescent_obligation` in `LSBranchRamification.lean` constructs a finite value image, normalizes it, passes to a good open, proves sheet splitting, excludes ramification with transverse tests, applies purity and finite étale triviality, and recovers a section from a graph. The elementary split-component degree-one lemma is already proved. The remaining cost lies in the geometric inputs and their composition.

A direct appeal to the cited Picard-number-one cover theorem on the current base `X × X` would miss a hypothesis. A valid shorter route must first work on the appropriate single-target slices and then prove compatibility when assembling the global object. This is the principal architectural question to settle.

## Obligation decisions

| Original obligations | Decision |
|---|---|
| 044–048, cotangent and smoothness (3h) | Retain and complete now. These are used by deformation and evaluation interfaces. |
| 049–056, Hom spaces and deformations (3i) | Retain pending construction of the actual twistor-conic parameter space. |
| 057–064, stable families and global functions (3j) | Retain. Coarse-space comparison may alter individual consumers, but none has been shown unused. |
| 065, 067, 068, 070, spreading and finite/line-space geometry | Keep available; the shorter route still has finite-image and line-bundle geometry. |
| 066, 071, 072, generic sheets and normalization | Review after the replacement descent interface exists; no retirement now. |
| 073–077, branch tests, purity and finite étale triviality | Strongest candidates for replacement by the slice/birational route. All remain pending until proved unnecessary in the rebuilt graph. |
| 078, extension from height one | Retain while the present extension argument is used. |
| 079–091, contact directions, group action and metric recovery (3m–3n) | Retain. Fu’s quadratic construction does not supply the project’s automorphism, adjoint, or metric translations by itself. |

## Required next comparison work

After 3h, specify the coarse conic space and universal-square evaluation, together with the maps from the current finite and parameterized covers. State the slice section and its compatibility using the actual contact and line-bundle maps. Construct the relative nodal chart over a reduced base and transport the already checked conic identities into it. Only then compare the new descent proof’s transitive assumptions with obligations 066 and 071–078.

Keep the exact frozen classification statement and the fixed denominator of 133. Do not admit the entire new classification proof, introduce its desired conclusion as a geometric input, or remove an admission merely because its corresponding old argument looks avoidable.

## Reviewed source bindings

- `LSStableMapFamily.lean`: `0360a40ba6a0fc816bd44e0887350661d51d76c5bad19e6577d94cac9f32d0b2`
- `LSStableFamilyTraits.lean`: `8e52c140d75bbd6794e7ded0e4ab498e772900974f9a26285249a08f6f0cf3de`
- `RecompileExtensionsPart02.lean`: `b665e4c47cd5687ea13c49c076e2ab7023272c0cb4bfc1058bd4041c172fb06e`
- `RecompileExtensionsPart04Geometry.lean`: `97e4af54a212b50d235ce936a9e87e91d6908da4c0395ed6830e73c844fbcd5e`
- `LSBranchRamification.lean`: `a12747b7dd5b9d810117d4866412b2f3debcd8d5e3e0ddebe5222b704fec5068`
