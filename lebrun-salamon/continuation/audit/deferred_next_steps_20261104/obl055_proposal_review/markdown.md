# Independent review of the proposed OBL-055 integration

**Conclusion:** the proposed generic input is a faithful scheme-representer specialization of the cited published theorem. The project comparison and its placement preserve the original public statement. This is a source and publication-scope review of an isolated proposal; it is not an integrated compilation, a native acceptance, or an obligation credit.

## Exact reviewed artifacts

| Artifact | SHA256 |
|---|---|
| New `LSRelativeHomFunctor.lean` | `43a0cd70213ad836841d0e6dcc9d9ce5ed581ac4d02bff1a70042bc9cfd8b171` |
| Proposed `RecompileExtensionsPart04Geometry.lean` | `fa5d3ff620150a3ce71ca806d2902c3ccb05edd7d2ed8356e059a4e57fef2e2f` |
| Original Geometry | `97e4af54a212b50d235ce936a9e87e91d6908da4c0395ed6830e73c844fbcd5e` |
| Root integration guard | `0633ec2c6ab69a295417b0e2df7f5c6f769e6367b6ced3f216187f7e8efe348b` |
| Original public 055 header | `277b0534307bd3854341c0048d64b2c59187a92fae64441e0a8fe2fa4d1b3546` |

These files are under `root_diagnostics/next_batch_candidate/root/`. I independently applied all three guard edits forward and backward and recovered both whole files exactly. The original header is byte-identical. Geometry has one fewer direct admission; the new generic module has exactly one, separately named `LeBrunSalamon.PublishedInputs.RelativeHom.locallyOfFinitePresentation`.

## Published input and actual functor

[Stacks Proposition 99.12.3, Tag 0D1C](https://stacks.math.columbia.edu/tag/0D1C) gives an algebraic-space relative-morphism representer locally of finite presentation when the source is proper, flat, and of finite presentation and the target is separated and of finite presentation. The candidate supplies exactly these hypotheses. Both occurrences of finite presentation are exposed as local finite presentation, quasi-compactness, and quasi-separatedness, as in [Definition 29.22.1, Tag 01TO](https://stacks.math.columbia.edu/tag/01TO).

The conclusion concerns a **supplied scheme representing the functor**. Passing from the published algebraic-space representer to that supplied representative uses Yoneda uniqueness and isomorphism invariance of local finite presentation. This is a generic mathematical specialization, not a project-specific theorem or a claim that properness alone produces a scheme representer. Its admitted statement contains no contact, conic, selected-family, or smoothness-of-Hom predicate.

The functor is evaluated on every object of `Over S`, including nonreduced schemes. [Stacks Section 99.12, Tag 0D19](https://stacks.math.columbia.edu/tag/0D19) uses maps from the base-changed source to the base-changed target over the test scheme. The code initially uses maps from the base-changed source to the original target over `S`. The four copied `homBaseChangeEquiv` declarations prove the actual equivalence, both projection equations, and its naturality. This resolves that presentation difference explicitly.

## Project translation and source placement

`targetChangeEquiv` converts the project's maps to `X` over the complex base into maps to `X × S` over `S`, using the actual pullback lift and both projections. `presentationRepresentation` then uses the supplied `H.universal` for every test scheme; its naturality proof identifies the actual family-change maps. The final comparison applies the generic input to `pullback.snd X.structureMap sS`. All source and target property conversions are discharged by the existing instances in the completed conditional diagnostic.

The three comparison declarations are inserted inside `LeBrunSalamon.Construction.Smoothing.HomDeformationInput.FunctorComparison`, after `familyChange` and `Presentation` and before `StandardInputs`. The required project structures therefore precede their uses. The new generic module imports only Mathlib; Geometry adds that module as one import. The public 055 declaration keeps its original name, arguments, instances, target, and surrounding scope and replaces only its admitted body.

I independently verified the ten generic functor declarations, four target-normalization declarations, and three project-comparison declarations are byte-identical to their completed diagnostic blocks. The enclosing namespace relocation is explicit. The combined isolated proposals for 052, 055, and 057 form a 311-module acyclic import graph over the frozen 308-module baseline.

## Evidence boundary

The comparison diagnostic source `59cbcc588e537e2086481618563bee2d3a84944395dbd67b868bd2b4240431de` completed in 32.694 seconds with zero errors and output `799137c4ceb93f1e69ec0b8379e8936710484ba561075d84703735623d93af22`. The normalization's actual source is `b80a07b1bbc10c07697424cb647653ce8f71d3a58364f44c3be5ef41bcebaf4c`; its guarded profile `66ffef95…` completed in 31.352 seconds with zero errors and output `0c21c4622ea0015ecbd4bc3a9141d55ed61ada6d73c176c1097521479e47a5e6`. Both diagnostics keep the new generic result as an explicit parameter or do not use it, and their recorded axiom checks contain only the standard logical axioms.

The new admitted input still requires its publication registration and the actual integrated sources still require the native and affected-consumer gates. This review requests no additional hypothesis or source change. No compiler, production file, acceptance record, or Git ref was changed during the review.
