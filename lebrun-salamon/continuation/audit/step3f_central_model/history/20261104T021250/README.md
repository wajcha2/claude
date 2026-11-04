# Step 3f: actual standard-source / plane-quadratic comparison

The twelve modules listed in `SCOPE.json` are integrated with native checks against a coherent current source ancestry. The exact replay used the validated c8 V2 seeds and the pinned runtime. It used no historical fallback artifact directories. All 74 accepted module sources still matched the live tree when integration was verified; the replay reported no changed runtime files or invalidated accepted modules.

## What is proved

The standard relative Segre construction supplies its actual determinant subscheme. The importing proofs derive the all-test quotient-tuple property, preserving the tensor line and the four normalized coordinates. From that property and the original `StandardSource` universal property, the proofs construct the generating three-tuple `(U1*V0, U0*V1, U0*V0)` and its actual equation `xy = a*z²`.

The literal quadratic zero scheme has the same all-test presentation. Comparing the two presentations gives inverse scheme morphisms, a proof of their base-map equality, and an isomorphism of the chosen line bundles. `FormalTraitSourceComparison.model_quadratic_comparison` specializes this construction to the original power-series parameter map. It retains the original `Model`, `modelProjection`, and `modelLine` definitions. It does not assume that an arbitrary given family is isomorphic to that model; the final family normal form is assembled separately.

## Published input boundary

The only new direct admission in these twelve files is `PublishedInputs.ProjectiveSpace.segreQuadric`. Its statement is the generic relative Segre embedding with its scheme image, the line O(1,1), and normalized coordinate pullbacks over an arbitrary commutative coefficient ring. The primary-source comparison is recorded in `SEGRE_SOURCE_BOUNDARY.md`: Stacks 01WD gives the map and coordinate construction, and Vakil classes 15–16, §5.B / Example 5.1 gives the scheme image ideal. The quotient-tuple, source, coefficient, and chosen-line translations are proved rather than admitted.

This report does not classify all inherited published leaves as accepted. Their native closure inventory is a separate check. Kernel compilation with an admitted theorem also does not prove the admitted statement.

## Remaining scope

The selected replay accepted 74 of 75 modules. `LSStandardCentralPlane`, the final central-fibre embedding wrapper, reached its 25-second wall limit with an empty diagnostic log. It was kept outside the live source graph. Every one of its selected dependencies passed. The full generic model comparison itself passed in 3.775 seconds.

The two original formal-trait normal-form wrappers remain separate acceptance gates. This partial chain is not a full-project build and does not establish that the milestone has been met. `REPLAY_STATUS.json` preserves the unsuccessful final target status, while `receipts/` and `ancestry_receipts/` preserve the successful module evidence and exact source hashes.
