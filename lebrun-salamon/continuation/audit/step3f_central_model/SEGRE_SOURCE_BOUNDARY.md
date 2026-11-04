# Generic Segre input and proved conic translations

This is the source boundary for the off-graph candidate `LSNormalizedSegre.lean`.
It is a publication comparison, not a kernel or current-dependency acceptance receipt.

## Published construction

The Stacks Project, Lemma 27.13.6, [Tag 01WD](https://stacks.math.columbia.edu/tag/01WD),
constructs the relative Segre closed immersion over an arbitrary base. In the
case of two projective lines it uses the actual line bundle O(1,1) and the four
sections in the order X₀Y₀, X₁Y₀, X₀Y₁, X₁Y₁.

Ravi Vakil's author notes, *Foundations of Algebraic Geometry*,
[classes 15–16 (2007)](https://math.stanford.edu/~vakil/0708-216/216class1516.pdf),
§5.B and Example 5.1, printed pages 16–17, identify the scheme image over an
arbitrary coefficient ring with the ideal of the 2×2 minors. For two projective
lines the ideal has the single generator Z₀Z₃−Z₁Z₂. This is a statement about
the scheme image, including its nonreduced test schemes, rather than only the
set of points over a field.

The candidate input `PublishedInputs.ProjectiveSpace.segreQuadric` specializes
these two generic statements to Spec R, with R an arbitrary commutative ring.
Its `Data` records this same normalized construction: the actual product of
two copies of the normalized polynomial Proj, its isomorphism onto the literal
determinant zero scheme, the base map, the O(1,1) identification, and the four
specified section equations. The zero scheme uses the existing actual
section-graph fibre product and the representing total-line API.

## What is proved outside the input

The following are project translations and are deliberately absent from the
published input:

- Unique factorization of an arbitrary map satisfying the determinant section
  equality, obtained from the actual zero-scheme universal property.
- The arbitrary generating quotient-tuple formulation, with its selected line
  comparison retained.
- Passage from four Segre coordinates to the three conic coordinates
  (U₁V₀, U₀V₁, U₀V₀), using U₁V₁=δU₀V₀ and explicit finite-free quotient maps.
- The all-test-scheme presentation of the base change of the project's
  `StandardSource`.
- Its actual isomorphism to the split plane quadratic xy=δz², over the original
  base and preserving the original selected O(1,1) line.
- Specialization to the central fibre δ=0 and its actual polarized plane
  embedding, including equality with the literal quadratic image.

These translations are implemented in the separate candidate files
`LSNormalizedSegreQuotients`, `LSNormalizedSegrePairs`,
`LSStandardConicTriple`, `LSPlaneConicZeroPresentation`,
`LSStandardConicZeroComparison`, and `LSStandardCentralPlane`.
Their native checks and current import closure must be recorded independently.

## Normalization requirement

The construction uses the single normalized `StandardTautological.chosen`
witness. Its specialization to the project's `projectiveCoordinates` therefore
requires the current constructor that selects that same witness. An old
arbitrary universal-quotient witness cannot be identified with the fixed
homogeneous coordinates by definitional equality. Any check using old
descendant artifacts together with the current normalized constructor is an
interface diagnostic only until the descendants are rebuilt.
