import Mathlib

noncomputable section

set_option autoImplicit false

/-!
# LeBrun--Salamon: affine extensions, cohomology and split-bundle evaluation

PREFERRED ENTRY: `LeBrunSalamon.Construction.leBrunSalamon_project`.
One source file. The exact 20,436-line starting checkpoint was fully rebuilt on
28 October 2026; its 792 selected dependency traces passed their recorded gates.
The v23 point-ideal/integer-twist additions had focused component checks, but
their final integration was not rebuilt. THIS continuation is entirely uncompiled:
the user deferred every Lean/Lake invocation, including focused checks, until
the source reaches 30,000 lines. All current compilation flags are false.
Stage 2 foundationBuild was accepted in the verified v20 baseline.
Stage 3 linesAndSmoothing remains in progress.

Actual normalized point-ideal frames are constructed for finite points, infinity,
and arbitrary existing complex-base identifications. Their common Laurent
transition gives an actual global isomorphism between any two marked point ideals.
Duality proves point independence of the original O(1), and hence of every O(d).
The original integer-twist addition and duality statements now have proofs.
Additive section evaluation and the tensor-section laws are also proved.
The uncompiled normalization continuation computes both actual chart restriction
maps and the chosen transition t^d, including tensor/Hom restriction coherence.
It identifies genuine O(d) sections with the standard Laurent matching space,
supplies negative-section vanishing and twist uniqueness independently of
Picard classification, and gives actual complex-linear H0 dimensions with
the required base-automorphism correction. Explicit local primitives and gap
representatives now live in the original sheaves. Further source drafts
identify actual twist endomorphisms with complex scalars, construct their
reciprocal inverses and two actual generating sections in nonnegative degree,
and compute actual point evaluation through the pullback-unit comparison.
The affine continuation derives whole-chart unit lifts for arbitrary middle
sheaves by proving local freeness and quasi-coherence, and constructs actual
extensions from overlap cocycles, including nonsplit negative-degree examples.
The original Yoneda cohomology predicate is compared with the actual Cech
equation. Actual finite sums now have rank, generation, section-dimension,
cohomology and two-point evaluation proofs. Evaluation is transported to
arbitrary supplied bases and arbitrary distinct point pairs. All these terms
remain uncompiled. Picard existence, arbitrary vector-bundle splitting and
its uniqueness, differential/ample comparisons, and the later suitable-line
and deformation constructions remain open.
This is NOT a complete formal proof of the conjecture.

## Route and interfaces

Core: normalized symmetric kernel of the actual L boxtimes L; no final conclusion
is assumed in its definition. Skeleton: all major manuscript stages, through
adjoint contact classification and homothety to a genuine symmetric metric model.
Refinement: covered moving pairs, qualified contact-value descent, ordered diagonal
symbols, and Jets.Inputs (nonzero coefficients, Taylor realization, actual global
contraction/jet comparison). The final assembly uses these explicit proof inputs,
not the admitted original conjecture, the admitted global criterion, or *_target.
Construction adds actual square-zero tangent tests, a represented relative Hom
scheme for the fixed nodal source, and finite-image/all-sheet descent geometry.
The obsolete symmetricJets projection is retained as a DERIVED compatibility method.
Constructing any full input package remains the project; no constructor is admitted.

The proof follows the pinned manuscript, including its symmetry-forced cubic
argument. It does not substitute a VMRT or Hwang--Mok extension theorem.
Construction refines smoothing into five inputs and descent into eight inputs.
Its Manifest records 17 smaller source-linked construction steps.
Blueprint lists 21 source-linked work packages. Project stores their source labels,
commit hashes, staged acceptance criteria, and declaration/proof status.
The chronological Phase namespaces are retained as the supporting library.

## Trust and verification

Theorem proofs may be `sorry`; these introduce sorryAx. Some intrinsic objects are
chosen from admitted existence theorems with specified universal properties, so
definitions can also depend on sorryAx. Acceptance of a statement is not a proof.
Legacy candidates must not be confused with their intrinsic replacements. Local
first-jet coordinates are normalized on ALL local functions; global generation is
not built into them. An assembly without local sorry can still inherit admissions.

Pinned mathlib: 116662aa4c1e9106ab5c609b3214b02f6e11a65a.
Toolchain: leanprover/lean4:v4.36.0-rc1. The v22 starting source was fully built on
28 October 2026. Its exact source hash and the earlier component logs are
historical evidence; no code added in the current continuation has been compiled.
Manuscript: openai/math commit 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a,
Contact-Fano-manifolds-and-the-LeBrun-Salamon-conjecture-September-23-2026.
Foundations: Stacks 01UM (differentials), 01CF (powers), 01PR (ampleness),
031T (normal extension), 0CBX (split nodes), 088U (proper scheme covers).
Run the next pinned whole-file verification when the requested 30,000-line threshold is reached.
The checkpoint separates the full v22 build, the v23 focused checks, and current
uncompiled source drafts. Static inventories and reviews are not kernel checks.
The affine contact example, P1 coefficient construction, dual-number maps, node calculation,
and elementary jet operations have checked proofs without sorryAx. Some completed local
law proofs inherit admitted geometric dependencies. The preferred root still requires
explicit project inputs and has sorryAx dependencies; no complete proof is claimed.
-/

open Bundle
open scoped Bundle ContDiff ENNReal
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing

namespace LeBrunSalamon

/-- The Euclidean model space of (real) dimension `4*n` (mathlib). -/
abbrev Model (n : ℕ) := EuclideanSpace ℝ (Fin (4 * n))

/-- The boundaryless model with corners for a `4*n`-manifold (mathlib). -/
abbrev model (n : ℕ) : ModelWithCorners ℝ (Model n) (Model n) :=
  modelWithCornersSelf ℝ (Model n)

/-- A triple of orthogonal real-linear complex structures obeying
`IJ = K = -JI` and `I² = J² = K² = -id`.

This is a **fiberwise** notion. On a quaternionic-Kähler manifold there
need not be a global choice of `I,J,K`! -/
def IsQuaternionicTriple
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (I J K : V →ₗ[ℝ] V) : Prop :=
  I.comp I = -(LinearMap.id : V →ₗ[ℝ] V) ∧
  J.comp J = -(LinearMap.id : V →ₗ[ℝ] V) ∧
  K.comp K = -(LinearMap.id : V →ₗ[ℝ] V) ∧
  I.comp J = K ∧
  J.comp I = -K ∧
  (∀ v w : V, inner ℝ (I v) (I w) = inner ℝ v w) ∧
  (∀ v w : V, inner ℝ (J v) (J w) = inner ℝ v w) ∧
  (∀ v w : V, inner ℝ (K v) (K w) = inner ℝ v w)

section Riemannian

variable (n : ℕ) (M : Type*)
variable [EMetricSpace M] [ChartedSpace (Model n) M]
variable [IsManifold (model n) ∞ M]
variable [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
variable [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
  (fun x : M => TangentSpace (model n) x)]
variable [IsRiemannianManifold (model n) M]

/-- The degree-one metric regularity needed by the canonical Levi--Civita construction. -/
local instance riemannianOnceSmooth :
    IsContMDiffRiemannianBundle (model n) 1 (Model n)
      (fun x : M => TangentSpace (model n) x) :=
  IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)


/-- A (not automatically smooth) tangent vector field. -/
abbrev VF := (x : M) → TangentSpace (model n) x

/-- A pointwise real-linear endomorphism field of the tangent bundle. -/
abbrev EndField :=
  (x : M) → TangentSpace (model n) x →ₗ[ℝ] TangentSpace (model n) x

/-- A fiberwise 3-plane field of endomorphisms. It becomes an actual
smooth rank-three subbundle when `HasLocalQuaternionicFrames` holds. -/
abbrev QDistribution :=
  (x : M) → Submodule ℝ
    (TangentSpace (model n) x →ₗ[ℝ] TangentSpace (model n) x)

/-- A vector field is smooth at `x`; the tangent-bundle charts are from
mathlib, not a newly postulated smoothness predicate. -/
def IsSmoothVFAt (X : VF n M) (x : M) : Prop :=
  ContMDiffAt (model n) (model n).tangent ∞
    (fun y : M => (⟨y, X y⟩ : TangentBundle (model n) M)) x

/-- Globally smooth vector field, needed for second covariant derivatives. Quantifying only over once-
differentiable fields at a single point is INSUFFICIENT for the curvature commutator. -/
def IsSmoothVF (X : VF n M) : Prop :=
  ∀ x : M, IsSmoothVFAt n M X x

/-- Smoothness at `x` of a tangent endomorphism field, tested on vector fields smooth near `x`. This is a
useful *operational* predicate, not yet an identification with the intrinsic C-infinity section space of
the endomorphism bundle. -/
def IsSmoothEndFieldAt (A : EndField n M) (x : M) : Prop :=
  ∀ Y : VF n M, IsSmoothVFAt n M Y x →
    IsSmoothVFAt n M (fun y => A y (Y y)) x

/-- An endomorphism field is a section of `Q` on some neighborhood of
`x`. No global quaternionic frame is required. -/
def IsLocalSection (Q : QDistribution n M) (A : EndField n M)
    (x : M) : Prop :=
  ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, A y ∈ Q y

/-- Local smooth quaternionic frames generate the rank-three field Q. Two frames on overlapping
neighborhoods generate the same subbundle, but are not expected to agree pointwise. -/
def HasLocalQuaternionicFrames (Q : QDistribution n M) : Prop :=
  ∀ x : M,
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ A B C : EndField n M,
        (∀ y ∈ U,
          IsQuaternionicTriple (TangentSpace (model n) y)
            (A y) (B y) (C y) ∧
          Q y = Submodule.span ℝ
            ({A y, B y, C y} : Set
              (TangentSpace (model n) y →ₗ[ℝ]
                TangentSpace (model n) y))) ∧
        (∀ y ∈ U,
          IsSmoothEndFieldAt n M A y ∧
          IsSmoothEndFieldAt n M B y ∧
          IsSmoothEndFieldAt n M C y)

/-- Parallelism of Q with respect to mathlib's actual Levi--Civita connection. The product rule defines
(∇_v A)(x) = B, with `B ∈ Q x`. Crucially, the SAME `B` works for all test vector fields `Y`. -/
noncomputable def IsParallelQuaternionicDistribution
    (Q : QDistribution n M) : Prop :=
  let nabla := CovariantDerivative.leviCivitaConnection (model n) M
  ∀ (x : M) (v : TangentSpace (model n) x) (A : EndField n M),
    IsLocalSection n M Q A x →
    IsSmoothEndFieldAt n M A x →
    ∃ B : TangentSpace (model n) x →ₗ[ℝ]
        TangentSpace (model n) x,
      B ∈ Q x ∧
      ∀ Y : VF n M, IsSmoothVFAt n M Y x →
        (nabla (fun y => A y (Y y)) x) v =
          A x ((nabla Y x) v) + B (Y x)

/-- A pointwise (1,3)-curvature tensor; no smoothness is silently assumed by this type abbreviation. -/
abbrev CurvatureAt (x : M) :=
  TangentSpace (model n) x →ₗ[ℝ]
    (TangentSpace (model n) x →ₗ[ℝ]
      (TangentSpace (model n) x →ₗ[ℝ] TangentSpace (model n) x))

/-- A field of (1,3)-tensors. -/
abbrev CurvatureField := (x : M) → CurvatureAt n M x

/-- Recognize `R` as the curvature of the Levi--Civita connection:

`R(X,Y)Z = ∇_X(∇_Y Z) - ∇_Y(∇_X Z) - ∇_[X,Y] Z`.

IMPORTANT: the test fields are C-infinity, unlike the earlier draft that
only assumed differentiability at the evaluation point. This is an
explicit mathematical definition, not an unproved primitive constant.
-/
noncomputable def IsLeviCivitaCurvature (R : CurvatureField n M) : Prop :=
  let nabla := CovariantDerivative.leviCivitaConnection (model n) M
  ∀ (x : M) (X Y Z : VF n M),
    IsSmoothVF n M X → IsSmoothVF n M Y → IsSmoothVF n M Z →
      R x (X x) (Y x) (Z x) =
        (nabla (fun y => (nabla Z y) (Y y)) x) (X x) -
        (nabla (fun y => (nabla Z y) (X y)) x) (Y x) -
        (nabla Z x) (VectorField.mlieBracket (model n) X Y x)

/-- Positivity of the scalar curvature computed by contracting `R(e_j,e_i)e_i` with `e_j`, with the
curvature sign convention above. Using an actual orthonormal basis excludes a vacuous basis quantifier.
Independence from the choice of basis is classical but NOT proved here. -/
def HasPositiveScalarCurvature (R : CurvatureField n M) : Prop :=
  ∀ x : M,
    ∃ b : OrthonormalBasis (Fin (4 * n)) ℝ
        (TangentSpace (model n) x),
      0 < ∑ i : Fin (4 * n), ∑ j : Fin (4 * n),
        inner ℝ (R x (b j) (b i) (b i)) (b j)

/-- The tensorial equation ∇R = 0 for the (1,3)-tensor `R`.

We first demand smoothness of `R(X,Y,Z)` on smooth fields, because
mathlib's chosen covariant derivative has unconstrained behavior on
non-differentiable sections. Then we use the usual three-input
Leibniz rule for the Levi--Civita connection. -/
noncomputable def IsParallelCurvature (R : CurvatureField n M) : Prop :=
  let nabla := CovariantDerivative.leviCivitaConnection (model n) M
  ∀ (x : M) (v : TangentSpace (model n) x) (X Y Z : VF n M),
    IsSmoothVF n M X → IsSmoothVF n M Y → IsSmoothVF n M Z →
      IsSmoothVFAt n M (fun y => R y (X y) (Y y) (Z y)) x ∧
      (nabla (fun y => R y (X y) (Y y) (Z y)) x) v =
        R x ((nabla X x) v) (Y x) (Z x) +
        R x (X x) ((nabla Y x) v) (Z x) +
        R x (X x) (Y x) ((nabla Z x) v)

/-- Positive quaternionic-Kähler structure: a local quaternionic rank-three subbundle parallel under Levi
--Civita, and positive *actual* Levi--Civita scalar curvature. The curvature witness is explicitly
constrained by the commutator formula, not an arbitrary scalar. -/
noncomputable def IsPositiveQuaternionicKahler : Prop :=
  ∃ (Q : QDistribution n M) (R : CurvatureField n M),
    HasLocalQuaternionicFrames n M Q ∧
    IsParallelQuaternionicDistribution n M Q ∧
    IsLeviCivitaCurvature n M R ∧
    HasPositiveScalarCurvature n M R

/-- Local Riemannian symmetry in the classical intrinsic form `∇R=0`. This is equivalent to the existence
of local geodesic reflections; that equivalence is not proved in this file. -/
noncomputable def IsLocallyRiemannianSymmetric : Prop :=
  ∃ R : CurvatureField n M,
    IsLeviCivitaCurvature n M R ∧ IsParallelCurvature n M R

/- The exact original `LeBrunSalamon.leBrunSalamon` statement is now
located in LSCompletedTargets, after its constructed project inputs.
This source-order relocation prevents the geometric construction from
depending on the theorem it is intended to prove. -/

end Riemannian
end LeBrunSalamon

open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.Limits

/-- Underlying arrow of mathlib's categorical automorphism wrapper. -/
abbrev CategoryTheory.Aut.hom {C : Type*} [Category C] {X : C}
    (f : CategoryTheory.Aut X) : X ⟶ X := f.asIso.hom

namespace LeBrunSalamon.PhaseOne

/-! ## 1. Schemes over the complex numbers -/

/-- The base scheme Spec(C), constructed by mathlib. -/
abbrev ComplexBase : Scheme := Spec (CommRingCat.of ℂ)

/-- A smooth, proper, connected, nonempty complex scheme of pure relative
    dimension `d`. The map to Spec(C) is explicit, and smoothness/properness
    use mathlib's actual morphism properties. This does NOT assert that the
    scheme is projective. -/
structure SmoothProperComplexVariety (d : ℕ) where
  scheme : Scheme
  structureMap : scheme ⟶ ComplexBase
  smooth : SmoothOfRelativeDimension d structureMap
  proper : IsProper structureMap
  connected : ConnectedSpace scheme
  nonempty : Nonempty scheme

/- These are existing hypotheses carried by the geometry object, not
new axioms. Registering the projections prevents later implicit
separatedness/smoothness requirements from being silently unavailable. -/
attribute [instance] SmoothProperComplexVariety.smooth
  SmoothProperComplexVariety.proper SmoothProperComplexVariety.connected
  SmoothProperComplexVariety.nonempty

instance smoothProperComplexVariety_smooth {d : ℕ}
    (X : SmoothProperComplexVariety d) : Smooth X.structureMap :=
  SmoothOfRelativeDimension.smooth (n := d) (f := X.structureMap)

/-! ## 1b. Genuine cotangent and tangent modules on affine charts -/

/-- The module of Kähler differentials of a complex algebra `A`.
    Mathlib constructs this as the conormal module of the diagonal. -/
noncomputable abbrev AffineCotangent
    (A : Type*) [CommRing A] [Algebra ℂ A] :=
  KaehlerDifferential ℂ A

/-- Algebraic vector fields on `Spec A`, expressed as C-derivations of A.
    Mathlib identifies these with Hom_A(Ω_{A/C}, A). -/
abbrev AffineVectorFields
    (A : Type*) [CommRing A] [Algebra ℂ A] :=
  Derivation ℂ A A

/-- The dual of the Kähler-differential module on an affine chart.
    There is an existing mathlib equivalence with `AffineVectorFields A`. -/
noncomputable abbrev AffineTangent
    (A : Type*) [CommRing A] [Algebra ℂ A] :=
  (KaehlerDifferential ℂ A →ₗ[A] A)

/-! ## 1c. The contact bracket on an affine chart -/

/-- An algebraic one-form on a smooth affine chart with **trivialized**
    contact line: an A-linear functional on C-derivations of A.
    Without the smoothness assumption, the natural map from Ω¹ to
    its double dual need not be an isomorphism. -/
abbrev AffineOneForm
    (A : Type*) [CommRing A] [Algebra ℂ A] :=
  AffineVectorFields A →ₗ[A] A

/-- The hyperplane module cut out by an A-valued one-form. -/
abbrev AffineDistribution
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (θ : AffineOneForm A) :=
  LinearMap.ker θ

/-- The Levi bracket of two sections of the kernel of an affine one-form,
    evaluated by the form. The Lie bracket is mathlib's *commutator of
    derivations*. The overall sign is irrelevant for contact nondegeneracy.

    This is only the *value* of the Levi pairing, not yet the sheaf-level
    alternating form. Its A-bilinearity and perfection are later tasks. -/
def affineLeviValue
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (θ : AffineOneForm A)
    (u v : AffineDistribution θ) : A :=
  θ ⁅u.1, v.1⁆

/-! ## 2. Locally free sheaves of a specified rank -/

/-- The mathlib category of O_X-modules. -/
abbrev OModule (X : Scheme) := X.Modules

/-- A sheaf of O_X-modules is locally free of rank `r` when it admits
    a cover by free trivializations with `r` generators. This adds the
    prescribed rank to mathlib's locally-free-sheaf predicate.

    The covering and generators are mathlib's `LocalGeneratorsData`;
    `IsLocallyFreeData` requires the free-sheaf maps to be isomorphisms.
    The rank is fixed by the cardinality equivalence of local free bases. -/
def IsLocallyFreeOfRank {X : Scheme} (E : OModule X) (r : ℕ) : Prop :=
  ∃ q : SheafOfModules.LocalGeneratorsData.{0} E,
    SheafOfModules.LocalGeneratorsData.IsLocallyFreeData q ∧
    ∀ i : q.I, Nonempty ((q.generators i).I ≃ Fin r)

/-- An algebraic vector bundle as its locally free sheaf of fixed rank. -/
structure AlgebraicVectorBundle (X : Scheme) (r : ℕ) where
  sheaf : OModule X
  locallyFree : IsLocallyFreeOfRank sheaf r

/-- An invertible O_X-module: a locally free sheaf of rank one. -/
abbrev LineBundle (X : Scheme) := AlgebraicVectorBundle X 1

/-- Global sections of an O_X-module, evaluated on the largest open. -/
abbrev GlobalSections {X : Scheme} (E : OModule X) : Type _ :=
  ↥(E.presheaf.obj (Opposite.op (⊤ : X.Opens)))

/-- Morphisms of O_X-modules use mathlib's category structure. -/
abbrev BundleHom {X : Scheme} (E F : OModule X) := E ⟶ F

/-! ## 3. A corank-one distribution and its contact line -/

/-- The short exact vector-bundle sequence for a contact structure:

    0 → F → T → L → 0,

    with rank(F)=2n, rank(T)=2n+1, rank(L)=1.

    `T` is presently an INPUT, not the intrinsically constructed tangent
    sheaf. Exactness alone also does NOT imply the contact condition.
    Both points must be addressed before calling this a contact manifold. -/
structure ContactSequence (X : Scheme) (n : ℕ)
    (T : AlgebraicVectorBundle X (2 * n + 1)) where
  distribution : AlgebraicVectorBundle X (2 * n)
  line : LineBundle X
  inclusion : distribution.sheaf ⟶ T.sheaf
  form : T.sheaf ⟶ line.sheaf
  comp_zero : inclusion ≫ form = 0
  shortExact :
    ({ X₁ := distribution.sheaf
       X₂ := T.sheaf
       X₃ := line.sheaf
       f := inclusion
       g := form
       zero := comp_zero } : ShortComplex (OModule X)).ShortExact

/-! ## 4. Fiberwise linear algebra for the Levi pairing -/

/-- A line-valued bilinear pairing, represented by its map into
    the L-valued dual. This is ordinary mathlib linear algebra. -/
abbrev LineValuedBilinearForm
    (R : Type*) [CommRing R]
    (V L : Type*) [AddCommGroup V] [Module R V]
    [AddCommGroup L] [Module R L] :=
  V →ₗ[R] (V →ₗ[R] L)

/-- A bilinear pairing is alternating when b(v,v)=0. -/
def IsAlternatingLinePairing
    {R : Type*} [CommRing R]
    {V L : Type*} [AddCommGroup V] [Module R V]
    [AddCommGroup L] [Module R L]
    (b : LineValuedBilinearForm R V L) : Prop :=
  ∀ v : V, b v v = 0

/-- A *perfect* alternating L-valued pairing: the induced map

       V → Hom_R(V,L)

    is bijective. At stalks, this gives the correct algebraic meaning of
    nondegeneracy of the contact Levi form. We have not constructed the
    geometric Levi pairing from the sheaf morphism `form` above. -/
def IsPerfectAlternatingLinePairing
    {R : Type*} [CommRing R]
    {V L : Type*} [AddCommGroup V] [Module R V]
    [AddCommGroup L] [Module R L]
    (b : LineValuedBilinearForm R V L) : Prop :=
  IsAlternatingLinePairing b ∧ Function.Bijective b

/-- The affine contact condition for a trivialized contact line.
    This says that the Lie-bracket expression, initially only defined as
    a function on pairs of fields in ker θ, is represented by an actual
    A-bilinear alternating *perfect* pairing. One cannot silently infer
    A-bilinearity without checking the usual Leibniz identity.
    Surjectivity of θ is ALSO required: nondegeneracy on ker θ alone
    does not ensure a corank-one contact distribution. -/
def IsAffineContactForm
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (θ : AffineOneForm A) : Prop :=
  Function.Surjective θ ∧
  ∃ b : LineValuedBilinearForm A (AffineDistribution θ) A,
    IsPerfectAlternatingLinePairing b ∧
    ∀ u v : AffineDistribution θ, b u v = affineLeviValue θ u v

/-! ## 5. A data container for subsequent contact geometry -/

/-- A pre-contact geometry datum on a smooth proper complex scheme.

    We deliberately DO NOT name this `ContactFano`:
    * `tangent` still needs identifying with T_X;
    * contact Levi nondegeneracy must be checked;
    * the contact line's ampleness is not yet defined;
    * neither K_X nor -K_X is yet constructed.

    Mere existence of this data does not establish any classification. -/
structure ContactCandidate (n : ℕ) where
  variety : SmoothProperComplexVariety (2 * n + 1)
  tangent : AlgebraicVectorBundle variety.scheme (2 * n + 1)
  contactSequence : ContactSequence variety.scheme n tangent

end LeBrunSalamon.PhaseOne

namespace LeBrunSalamon.FoundationExamples.AffineThreeSpace

open LeBrunSalamon.PhaseOne

/-- Polynomial coordinate ring of affine three-space over the complex numbers. -/
abbrev A := MvPolynomial (Fin 3) ℂ

abbrev x : A := MvPolynomial.X 0
abbrev y : A := MvPolynomial.X 1
abbrev z : A := MvPolynomial.X 2

/-- The actual polynomial one-form dz - x dy, evaluated on derivations. -/
def theta : AffineOneForm A where
  toFun D := D z - x * D y
  map_add' D E := by simp; ring
  map_smul' a D := by simp [smul_eq_mul]; ring

@[simp] theorem theta_apply (D : AffineVectorFields A) :
    theta D = D z - x * D y := rfl

/-- A contact-plane field with coordinate coefficients (a,b,x*b). -/
def planeField (a b : A) : AffineVectorFields A :=
  MvPolynomial.mkDerivation ℂ ![a, b, x * b]

@[simp] theorem planeField_x (a b : A) : planeField a b x = a := by
  simp [planeField, x]

@[simp] theorem planeField_y (a b : A) : planeField a b y = b := by
  simp [planeField, y]

@[simp] theorem planeField_z (a b : A) : planeField a b z = x * b := by
  simp [planeField, z]

@[simp] theorem theta_planeField (a b : A) : theta (planeField a b) = 0 := by
  simp

def plane (a b : A) : AffineDistribution theta :=
  ⟨planeField a b, theta_planeField a b⟩

@[simp] theorem plane_x (a b : A) : (plane a b).val x = a := planeField_x a b
@[simp] theorem plane_y (a b : A) : (plane a b).val y = b := planeField_y a b

def eX : AffineDistribution theta := plane 1 0
def eY : AffineDistribution theta := plane 0 1

theorem kernel_z (u : AffineDistribution theta) : u.val z = x * u.val y := by
  have h : theta u.val = 0 := u.property
  exact sub_eq_zero.mp h

theorem kernel_ext {u v : AffineDistribution theta}
    (hx : u.val x = v.val x) (hy : u.val y = v.val y) : u = v := by
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  fin_cases i
  · exact hx
  · exact hy
  · change u.val z = v.val z
    rw [kernel_z, kernel_z, hy]

/-- The displayed fields are an actual basis of the contact plane. -/
theorem kernel_decomposition (u : AffineDistribution theta) :
    u = (u.val x) • eX + (u.val y) • eY := by
  apply kernel_ext <;> simp [eX, eY, smul_eq_mul]

/-- Levi pairing in these coordinates; this is an A-bilinear morphism. -/
def leviPair : LineValuedBilinearForm A (AffineDistribution theta) A where
  toFun u :=
    { toFun := fun v => u.val x * v.val y - u.val y * v.val x
      map_add' := by intros; simp; ring
      map_smul' := by intros; simp [smul_eq_mul]; ring }
  map_add' := by intros; apply LinearMap.ext; intro v; simp; ring
  map_smul' := by intros; apply LinearMap.ext; intro v; simp [smul_eq_mul]; ring

@[simp] theorem leviPair_apply (u v : AffineDistribution theta) :
    leviPair u v = u.val x * v.val y - u.val y * v.val x := rfl

/-- The coordinate pairing is precisely theta of the derivation commutator. -/
theorem leviPair_is_bracket (u v : AffineDistribution theta) :
    leviPair u v = affineLeviValue theta u v := by
  simp only [affineLeviValue, theta_apply, Derivation.commutator_apply]
  rw [kernel_z u, kernel_z v]
  simp only [Derivation.leibniz, smul_eq_mul, leviPair_apply]
  ring

/-- The Levi form is nonzero on the displayed pair, fixing its sign. -/
theorem levi_basis_value : affineLeviValue theta eX eY = 1 := by
  rw [← leviPair_is_bracket]
  simp [eX, eY]

theorem leviPair_perfect : IsPerfectAlternatingLinePairing leviPair := by
  refine ⟨?_, ?_, ?_⟩
  · intro u
    simp only [leviPair_apply]
    ring
  · intro u v h
    have hx := congrArg (fun l => l eY) h
    have hy := congrArg (fun l => l eX) h
    apply kernel_ext
    · simpa [eY] using hx
    · simpa [eX] using hy
  · intro l
    refine ⟨plane (l eY) (-l eX), ?_⟩
    apply LinearMap.ext
    intro v
    have hv := congrArg l (kernel_decomposition v)
    simp only [map_add, map_smul, smul_eq_mul] at hv
    simp only [leviPair_apply, plane_x, plane_y]
    rw [hv]
    ring

theorem theta_surjective : Function.Surjective theta := by
  intro a
  refine ⟨MvPolynomial.mkDerivation ℂ ![0, 0, a], ?_⟩
  simp [theta, y, z]

/-- A nonvacuous three-dimensional example for the project's contact predicate. -/
theorem theta_isAffineContactForm : IsAffineContactForm theta := by
  exact ⟨theta_surjective, leviPair, leviPair_perfect, leviPair_is_bracket⟩

theorem theta_nonzero : theta ≠ 0 := by
  intro h
  obtain ⟨D, hD⟩ := theta_surjective 1
  simp [h] at hD

end LeBrunSalamon.FoundationExamples.AffineThreeSpace



/-!
# Phase 2 -- algebraic rational curves and deformation data

The projective line itself is a *mathlib Proj scheme* of the graded binary polynomial ring, rather than an
opaque type. Its map to Spec(C) now **factors through** mathlib's `Proj.toSpecZero`. The identification of
the degree-zero ring with C is constructed below from constant polynomials. Alternate degree-zero
identifications are allowed, and rational points are transported through their induced base isomorphisms.

We define actual C-scheme morphisms, marked C-points, pullbacks of sheaves, free rational curves (global
generation), two-component curves glued at a marked point at the level of maps, and flat proper families.
We do NOT assert that the last data produce an actual nodal union, nor do we silently assume a
classification of line bundles on P1.
-/

namespace LeBrunSalamon.PhaseTwo

open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.Limits
open LeBrunSalamon.PhaseOne

/-! ## 2A. The projective line and morphisms over C -/

/-- A genuine scheme: Proj(C[U,V]), graded by total degree.
    This uses mathlib's `Proj` and `MvPolynomial.homogeneousSubmodule`.
    The base morphism is fixed below by `Proj.toSpecZero`. -/
noncomputable abbrev ProjectiveLine : Scheme :=
  AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ)

/-- The degree-zero coefficient spectrum of the standard homogeneous
    polynomial grading. The missing identification with `Spec ℂ` is a
    concrete graded-ring isomorphism, not an arbitrary projective-line map. -/
noncomputable abbrev BinaryDegreeZeroSpectrum : Scheme :=
  Spec (CommRingCat.of ↥(MvPolynomial.homogeneousSubmodule (Fin 2) ℂ 0))

/-- A projective line over ℂ with its map **forced** to factor through
    mathlib's canonical `Proj.toSpecZero`. What remains to construct is the
    specific zero-degree isomorphism coming from constant polynomials.
    In particular a user may no longer supply an unrelated structure map. -/
structure ProjectiveLineOverC where
  zeroDegreeIso : BinaryDegreeZeroSpectrum ≅ ComplexBase

/-- The canonical Proj-to-Spec construction followed by the supplied
    identification of the degree-zero ring with ℂ. -/
noncomputable def ProjectiveLineOverC.structureMap
    (P : ProjectiveLineOverC) : ProjectiveLine ⟶ ComplexBase :=
  (AlgebraicGeometry.Proj.toSpecZero
     (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ)) ≫ P.zeroDegreeIso.hom

/-- A C-valued point of the projective line, rather than an arbitrary
    scheme-theoretic point (which could be the generic point). -/
structure ProjectiveLinePoint (P : ProjectiveLineOverC) where
  map : ComplexBase ⟶ ProjectiveLine
  overC : map ≫ P.structureMap = 𝟙 ComplexBase

namespace ProjectiveLinePoint

set_option backward.isDefEq.respectTransparency false

/-- A rational point viewed over a different identification of the
degree-zero spectrum with the complex base. -/
def rebase {P : ProjectiveLineOverC} (Q : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) : ProjectiveLinePoint Q where
  map := (Q.zeroDegreeIso.symm ≪≫ P.zeroDegreeIso).hom ≫ p.map
  overC := by
    have hp : p.map ≫ Proj.toSpecZero
        (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) = P.zeroDegreeIso.inv := by
      apply (cancel_mono P.zeroDegreeIso.hom).1
      simpa only [ProjectiveLineOverC.structureMap, Category.assoc, Iso.inv_hom_id]
        using p.overC
    change ((Q.zeroDegreeIso.inv ≫ P.zeroDegreeIso.hom) ≫ p.map) ≫
      (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) ≫
        Q.zeroDegreeIso.hom) = 𝟙 _
    simp only [Category.assoc]
    rw [← Category.assoc p.map, hp]
    simp

@[ext]
theorem ext {P : ProjectiveLineOverC} {p q : ProjectiveLinePoint P}
    (h : p.map = q.map) : p = q := by
  cases p
  cases q
  cases h
  rfl

theorem rebase_self {P : ProjectiveLineOverC} (p : ProjectiveLinePoint P) :
    rebase P p = p := by
  apply ext
  simp [rebase]

theorem rebase_rebase {P : ProjectiveLineOverC} (Q R : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) : rebase R (rebase Q p) = rebase R p := by
  apply ext
  simp [rebase, Category.assoc]

/-- Changing the coefficient-spectrum identification loses no marked points. -/
def rebaseEquiv (P Q : ProjectiveLineOverC) :
    ProjectiveLinePoint P ≃ ProjectiveLinePoint Q where
  toFun := rebase Q
  invFun := rebase P
  left_inv p := by rw [rebase_rebase, rebase_self]
  right_inv p := by rw [rebase_rebase, rebase_self]

theorem rebase_map_eq_iff {P : ProjectiveLineOverC} (Q : ProjectiveLineOverC)
    (p q : ProjectiveLinePoint P) : (rebase Q p).map = (rebase Q q).map ↔ p.map = q.map := by
  change (Q.zeroDegreeIso.symm ≪≫ P.zeroDegreeIso).hom ≫ p.map =
    (Q.zeroDegreeIso.symm ≪≫ P.zeroDegreeIso).hom ≫ q.map ↔ _
  exact cancel_epi _

end ProjectiveLinePoint


/-- A morphism `P¹ → X` over the chosen structure maps to Spec(C). -/
structure ParametrizedCurve (P : ProjectiveLineOverC)
    {d : ℕ} (X : SmoothProperComplexVariety d) where
  map : ProjectiveLine ⟶ X.scheme
  overC : map ≫ X.structureMap = P.structureMap

/-- A C-rational constant map, factoring through a C-point of the target.
    This is stronger and better specified than constancy only on the
    underlying topological space of a scheme. -/
def IsConstantOverC (P : ProjectiveLineOverC)
    {d : ℕ} (X : SmoothProperComplexVariety d)
    (f : ProjectiveLine ⟶ X.scheme) : Prop :=
  ∃ p : ComplexBase ⟶ X.scheme,
    p ≫ X.structureMap = 𝟙 ComplexBase ∧ f = P.structureMap ≫ p

/-- A nonconstant morphism P¹ → X of C-schemes. -/
structure RationalCurve (P : ProjectiveLineOverC)
    {d : ℕ} (X : SmoothProperComplexVariety d) where
  map : ProjectiveLine ⟶ X.scheme
  overC : map ≫ X.structureMap = P.structureMap
  nonconstant : ¬ IsConstantOverC P X map

/-- Forget nonconstancy without relying on a nonexistent parent projection. -/
def RationalCurve.toParametrizedCurve {P : ProjectiveLineOverC}
    {d : ℕ} {X : SmoothProperComplexVariety d}
    (f : RationalCurve P X) : ParametrizedCurve P X :=
  ⟨f.map, f.overC⟩

/-- A nonconstant rational curve equipped with a C-valued marked point. -/
structure PointedRationalCurve (P : ProjectiveLineOverC)
    {d : ℕ} (X : SmoothProperComplexVariety d) where
  curve : RationalCurve P X
  point : ProjectiveLinePoint P

/-- Two distinct C-valued marked points on the same rational curve. -/
structure TwoPointedRationalCurve (P : ProjectiveLineOverC)
    {d : ℕ} (X : SmoothProperComplexVariety d) where
  curve : RationalCurve P X
  first : ProjectiveLinePoint P
  second : ProjectiveLinePoint P
  distinct : first.map ≠ second.map

/-- A C-valued point of a complex variety. This records a morphism of
    schemes over Spec(C), not merely a topological point. -/
structure ComplexPoint {d : ℕ} (X : SmoothProperComplexVariety d) where
  map : ComplexBase ⟶ X.scheme
  overC : map ≫ X.structureMap = 𝟙 ComplexBase

/-- Evaluation of a parametrized curve at a marked C-point. -/
def curveEvaluation (P : ProjectiveLineOverC)
    {d : ℕ} (X : SmoothProperComplexVariety d)
    (f : ParametrizedCurve P X) (p : ProjectiveLinePoint P) :
    ComplexBase ⟶ X.scheme :=
  p.map ≫ f.map

/-- Incidence with a specified C-valued point of X. -/
def PassesThrough (P : ProjectiveLineOverC)
    {d : ℕ} (X : SmoothProperComplexVariety d)
    (f : RationalCurve P X) (x : ComplexPoint X) : Prop :=
  ∃ p : ProjectiveLinePoint P, p.map ≫ f.map = x.map

/-! ## 2B. Pullbacks, generation, and free rational curves -/

/-- Pullback of an O_X-module along a scheme morphism (from mathlib's
    genuine pullback FUNCTOR, not an arbitrary sheaf on P¹). -/
noncomputable abbrev pullbackModule {X Y : Scheme}
    (f : X ⟶ Y) (E : OModule Y) : OModule X :=
  (Scheme.Modules.pullback f).obj E

/-- A sheaf is globally generated if some actual family of its global
    sections generates it. In mathlib, `GeneratingSections` packages an
    epimorphism from a free sheaf indexed by the chosen global sections. -/
def IsGloballyGenerated {X : Scheme} (E : OModule X) : Prop :=
  Nonempty (SheafOfModules.GeneratingSections E)

/-- Freeness of a rational curve relative to a supplied tangent sheaf.
    As in algebraic geometry, this is the global generation of f^*T_X.
    It becomes the standard condition only once the tangent input is
    identified with the INTRINSIC tangent sheaf of X. -/
def IsFreeRationalCurve (P : ProjectiveLineOverC)
    {d : ℕ} (X : SmoothProperComplexVariety d)
    (TX : AlgebraicVectorBundle X.scheme d)
    (f : RationalCurve P X) : Prop :=
  IsGloballyGenerated (pullbackModule f.map TX.sheaf)

/-- Prescribed splitting type of the pulled-back tangent sheaf. The
    comparison sheaf `E` must be fixed independently (e.g. by building
    actual O(a_i) and direct sums); existentially choosing `E` would be
    meaningless, so we do not do that. -/
def HasPrescribedTangentPullback (P : ProjectiveLineOverC)
    {d : ℕ} (X : SmoothProperComplexVariety d)
    (TX : AlgebraicVectorBundle X.scheme d)
    (f : RationalCurve P X) (E : OModule ProjectiveLine) : Prop :=
  Nonempty (pullbackModule f.map TX.sheaf ≅ E)

/-- A concrete pullback of a line bundle. Rank-one local freeness of the
    result follows from mathlib's pullback theory but is not proved here. -/
noncomputable abbrev pullbackLineSheaf {X Y : Scheme}
    (f : X ⟶ Y) (L : LineBundle Y) : OModule X :=
  pullbackModule f L.sheaf

/-- The pullback of L along a curve has the specified sheaf isomorphism
    type on P¹. This does NOT assign numerical degree without identifying
    the supplied model with the genuine twist O(d). -/
def HasPrescribedLineType (P : ProjectiveLineOverC)
    {d : ℕ} (X : SmoothProperComplexVariety d)
    (f : ParametrizedCurve P X) (L : LineBundle X.scheme)
    (target : LineBundle ProjectiveLine) : Prop :=
  Nonempty (pullbackLineSheaf f.map L ≅ target.sheaf)

/-- A contact-degree-one rational curve relative to a separately verified
    model of O_{P¹}(1). Such curves are central in the non-projective-space
    contact-Fano case. In standard contact P^(2n+1), by contrast, L=O(2)
    and there are *no* contact-degree-one rational curves. A later case
    distinction must therefore precede arguments using this structure. -/
structure ContactLineCandidate (P : ProjectiveLineOverC)
    (n : ℕ) (X : ContactCandidate n)
    (O1 : LineBundle ProjectiveLine) where
  curve : RationalCurve P X.variety
  contactDegreeOne : Nonempty
    (pullbackLineSheaf curve.map X.contactSequence.line ≅ O1.sheaf)

/-! ## 2C. Reducible curves: the two-component combinatorics -/

/-- Two nonconstant rational curves, with specified C-valued marked
    points whose images in X agree. This is the *combinatorial/gluing
    datum* of a two-component nodal stable map. It does not construct the
    glued nodal source scheme or impose transverse branches. -/
structure TwoComponentCurve (P : ProjectiveLineOverC)
    {d : ℕ} (X : SmoothProperComplexVariety d) where
  left : RationalCurve P X
  right : RationalCurve P X
  leftNode : ProjectiveLinePoint P
  rightNode : ProjectiveLinePoint P
  nodeAgreement : leftNode.map ≫ left.map = rightNode.map ≫ right.map

/-- Both components have contact degree one. Under a valid O(1) model,
    the resulting connected reducible curve has expected L-degree two.
    The degree-additivity theorem is not asserted here. -/
structure TwoContactLines (P : ProjectiveLineOverC)
    (n : ℕ) (X : ContactCandidate n)
    (O1 : LineBundle ProjectiveLine) where
  left : ContactLineCandidate P n X O1
  right : ContactLineCandidate P n X O1
  leftNode : ProjectiveLinePoint P
  rightNode : ProjectiveLinePoint P
  nodeAgreement :
    leftNode.map ≫ left.curve.map = rightNode.map ≫ right.curve.map

/-! ## 2D. The normal exact sequence -- with an explicit caveat -/

/-- Candidate for the normal sequence of an *immersed* rational curve:

       0 → T_{P¹} → f^*T_X → N_f → 0.

    It records a real short exact sequence of mathlib module sheaves.
    However `differential` is not yet the canonical df, and `TP1`, `TX`
    are not yet identified with intrinsic tangent sheaves. Thus this
    structure is not by itself a proof that the curve is immersed.
    The normal bundle is rank 2n when dim X = 2n+1. -/
structure NormalSequenceCandidate (P : ProjectiveLineOverC)
    (n : ℕ) (X : ContactCandidate n)
    (f : ParametrizedCurve P X.variety)
    (TP1 : AlgebraicVectorBundle ProjectiveLine 1) where
  normal : AlgebraicVectorBundle ProjectiveLine (2 * n)
  differential : TP1.sheaf ⟶ pullbackModule f.map X.tangent.sheaf
  quotient : pullbackModule f.map X.tangent.sheaf ⟶ normal.sheaf
  comp_zero : differential ≫ quotient = 0
  shortExact :
    ({ X₁ := TP1.sheaf,
       X₂ := pullbackModule f.map X.tangent.sheaf,
       X₃ := normal.sheaf,
       f := differential,
       g := quotient,
       zero := comp_zero } :
       ShortComplex (OModule ProjectiveLine)).ShortExact

/-! ## 2E. Proper flat families of curves with maps to a fixed target -/

/-- A proper flat family of schemes C → B, equipped with a map C → X
    over C. Not every flat proper family is a family of connected
    arithmetic-genus-zero curves; those are further conditions. -/
structure ProperFlatFamilyOfMaps {d : ℕ}
    (X : SmoothProperComplexVariety d) where
  base : Scheme
  baseToC : base ⟶ ComplexBase
  total : Scheme
  projection : total ⟶ base
  isFlat : AlgebraicGeometry.Flat projection
  isProper : AlgebraicGeometry.IsProper projection
  evaluation : total ⟶ X.scheme
  evaluationOverC : evaluation ≫ X.structureMap = projection ≫ baseToC

/-- A C-valued parameter of a family. -/
structure ParameterPoint {d : ℕ}
    {X : SmoothProperComplexVariety d}
    (F : ProperFlatFamilyOfMaps X) where
  map : ComplexBase ⟶ F.base
  overC : map ≫ F.baseToC = 𝟙 ComplexBase

/-- Actual scheme-theoretic fibre of the family over a C-valued point;
    this is a mathlib categorical pullback, not an arbitrary fibre. -/
noncomputable abbrev fibreScheme {d : ℕ}
    {X : SmoothProperComplexVariety d}
    (F : ProperFlatFamilyOfMaps X)
    (b : ParameterPoint F) : Scheme :=
  CategoryTheory.Limits.pullback F.projection b.map

/-- The map to X induced by restricting a family map to a fibre. -/
noncomputable def fibreEvaluation {d : ℕ}
    {X : SmoothProperComplexVariety d}
    (F : ProperFlatFamilyOfMaps X)
    (b : ParameterPoint F) : fibreScheme F b ⟶ X.scheme :=
  CategoryTheory.Limits.pullback.fst F.projection b.map ≫ F.evaluation

/-- Smoothness of the scheme-theoretic fibre as a one-dimensional
    complex scheme. This uses mathlib's actual relative-smoothness
    predicate on the projection C_b → Spec(C). Arithmetic genus and
    connectedness of the fibre are NOT part of this condition. -/
def IsSmoothOneDimensionalFibre {d : ℕ}
    {X : SmoothProperComplexVariety d}
    (F : ProperFlatFamilyOfMaps X)
    (b : ParameterPoint F) : Prop :=
  AlgebraicGeometry.SmoothOfRelativeDimension 1
    (CategoryTheory.Limits.pullback.snd F.projection b.map)

/-- A flat family with one designated special parameter and another
    parameter. No smoothness or nodality of the corresponding fibres is
    built into this *setup*: those conditions need separate definitions. -/
structure TwoFibreDeformationSetup {d : ℕ}
    (X : SmoothProperComplexVariety d) where
  family : ProperFlatFamilyOfMaps X
  special : ParameterPoint family
  general : ParameterPoint family
  distinct : special.map ≠ general.map

/-- A genuine proper flat map family with a specified smooth
    one-dimensional fibre. The special fibre is NOT assumed nodal,
    and we therefore do not name this a smoothing of a nodal conic. -/
structure SmoothGeneralFibreSetup {d : ℕ}
    (X : SmoothProperComplexVariety d) where
  setup : TwoFibreDeformationSetup X
  smoothGeneral : IsSmoothOneDimensionalFibre setup.family setup.general

end LeBrunSalamon.PhaseTwo

/-!
# Phase 3 -- diagonal ideals, two-point data and jets

This phase adds **genuine** scheme-theoretic constructions using mathlib:
* `X ×_{Spec ℂ} X` and the actual diagonal morphism;
* its kernel ideal sheaf `I_Δ`, powers, and their closed subschemes;
* vanishing of a (possibly twisted) section to a prescribed order, defined by
  pulling the section back to the actual infinitesimal neighborhood;
* principal-parts sheaves `P^k(E)` using pushforward/pullback along that
  neighborhood (no invented jet-bundle primitive);
* infinitesimal neighborhoods of a geometric point and the jet-separation
  condition for global sections of a line bundle;
* affine diagonal ideals and affine principal-parts rings, plus symmetry of
  ordinary two-point functions under exchange of factors.

Crucial scope limits:
* `TwoPointSection E` is a section of a **specified** O-module on X×X.
  In particular, we have NOT identified a model with `L ⊠ L`; tensor products
  of sheaves and their swap linearization are still required.
* We have NOT constructed the leading quadratic symbol in
  `I_Δ²/I_Δ³ ⊗ (L ⊠ L)` or identified it with the contact form.
* The existing `ContactCandidate` is not yet a true contact Fano manifold.

There are no new proofs and no added `sorry` or `axiom` declarations.
-/

namespace LeBrunSalamon.PhaseThree

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseTwo
open scoped TensorProduct

/-! ## 3A. Fibre square and scheme-theoretic diagonal -/

/-- The actual fibre square `X ×_{Spec ℂ} X` of a given complex scheme.
    The construction is mathlib's categorical pullback in schemes. -/
noncomputable abbrev SelfProduct {X : Scheme}
    (s : X ⟶ ComplexBase) : Scheme :=
  pullback s s

/-- Projection from the fibre square to its first factor. -/
noncomputable abbrev firstProjection {X : Scheme}
    (s : X ⟶ ComplexBase) : SelfProduct s ⟶ X :=
  pullback.fst s s

/-- Projection from the fibre square to its second factor. -/
noncomputable abbrev secondProjection {X : Scheme}
    (s : X ⟶ ComplexBase) : SelfProduct s ⟶ X :=
  pullback.snd s s

/-- The canonical diagonal `X → X ×_{Spec ℂ} X`. -/
noncomputable abbrev diagonal {X : Scheme}
    (s : X ⟶ ComplexBase) : X ⟶ SelfProduct s :=
  pullback.diagonal s

/-- Swap the factors of the fibre square.  Unlike a guessed involution,
    this is built by the universal property of the categorical pullback. -/
noncomputable def swapSelfProduct {X : Scheme}
    (s : X ⟶ ComplexBase) : SelfProduct s ⟶ SelfProduct s :=
  pullback.lift (secondProjection s) (firstProjection s) (by
    simpa [firstProjection, secondProjection] using (pullback.condition (f := s) (g := s)).symm)

/-- The kernel ideal of the diagonal morphism. It cuts out the true
    closed diagonal exactly when the structure map `s : X -> Spec(C)`
    is SEPARATED. For a nonseparated map it can instead describe the
    schematic image of the diagonal, a different object. -/
noncomputable abbrev diagonalIdeal {X : Scheme}
    (s : X ⟶ ComplexBase) : (SelfProduct s).IdealSheafData :=
  (diagonal s).ker

/-- The genuine `order`-th power `I_Δ^order` as an ideal sheaf datum. -/
noncomputable abbrev diagonalIdealPower {X : Scheme}
    (s : X ⟶ ComplexBase) (order : ℕ) :
    (SelfProduct s).IdealSheafData :=
  (diagonalIdeal s) ^ order

/-- Closed subscheme cut out by `I_Δ^order`. Under the indispensable
    separatedness hypothesis on s, `order=1` is the true diagonal,
    `order=2` its first infinitesimal neighborhood, and `order=0`
    the empty subscheme. Without separatedness the identification with
    the diagonal is NOT justified. -/
noncomputable abbrev diagonalPowerSubscheme {X : Scheme}
    (s : X ⟶ ComplexBase) (order : ℕ) : Scheme :=
  (diagonalIdealPower s order).subscheme

/-- The canonical immersion of the `order`-th power neighborhood
    into `X × X`. -/
noncomputable abbrev diagonalPowerInclusion {X : Scheme}
    (s : X ⟶ ComplexBase) (order : ℕ) :
    diagonalPowerSubscheme s order ⟶ SelfProduct s :=
  (diagonalIdealPower s order).subschemeι

/-- The proposed order-k diagonal neighborhood, cut out by
    `I_Δ^(k+1)`. This is the genuine neighborhood when `s` is separated,
    a hypothesis enforced on the vanishing/jet definitions below. -/
noncomputable abbrev diagonalJetNeighborhood {X : Scheme}
    (s : X ⟶ ComplexBase) (k : ℕ) : Scheme :=
  diagonalPowerSubscheme s (k + 1)

/-! ## 3B. Actual sections, restriction and vanishing order -/

/-- A global section of an O-module, encoded by the corresponding
    morphism `O_X → E`. The identification with sections on the largest
    open is furnished in mathlib by `SheafOfModules.unitHomEquiv`. -/
noncomputable abbrev AlgebraicSection {X : Scheme} (E : OModule X) :=
  (SheafOfModules.unit X.ringCatSheaf ⟶ E)

/-- The ordinary additive structure on morphisms of module sheaves, with the
coefficient sheaf supplied explicitly to avoid ambiguous category inference. -/
noncomputable instance algebraicSection_addCommGroup {X : Scheme} (E : OModule X) :
    AddCommGroup (AlgebraicSection E) :=
  SheafOfModules.instAddCommGroupHom X.ringCatSheaf _ _

/-- Pull back a global section along a morphism `f : Y → X`.
    We retain the honest source `f* O_X`, rather than silently replacing
    it with `O_Y`; they are canonically isomorphic but not definitionally
    identical. -/
noncomputable def restrictSection {X Y : Scheme} (f : Y ⟶ X)
    {E : OModule X} (σ : AlgebraicSection E) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
      (Scheme.Modules.pullback f).obj E :=
  (Scheme.Modules.pullback f).map σ

/-- Vanishing to order at least `order` on the diagonal means
    the actual pulled-back section is zero on `V(I_Δ^order)`.
    SEPARATEDNESS is explicitly required, since otherwise `V(I_Δ)`
    need not be the actual diagonal.
    This works for sections of ANY O-module on X×X, including the
    intended twist `L ⊠ L` once it has been constructed.

    `order=1` means restriction to Δ vanishes;
    `order=2` means quadratic vanishing along Δ. -/
def VanishesToOrderAlongDiagonal {X : Scheme}
    (s : X ⟶ ComplexBase) [AlgebraicGeometry.IsSeparated s]
    (E : OModule (SelfProduct s))
    (σ : AlgebraicSection E) (order : ℕ) : Prop :=
  restrictSection (diagonalPowerInclusion s order) σ = 0

/-- Exactly order `k` is vanishing to order at least `k` but not to
    order `k+1`. This is useful when the first nonzero normal symbol
    is expected to encode the contact form. -/
def HasExactDiagonalOrder {X : Scheme}
    (s : X ⟶ ComplexBase) [AlgebraicGeometry.IsSeparated s]
    (E : OModule (SelfProduct s))
    (σ : AlgebraicSection E) (k : ℕ) : Prop :=
  VanishesToOrderAlongDiagonal s E σ k ∧
    ¬ VanishesToOrderAlongDiagonal s E σ (k + 1)

/-- Quadratic vanishing along the diagonal: `σ ∈ I_Δ² E`.
    We express this via pullback to the closed subscheme V(I_Δ²),
    not by postulating an unconstructed subsheaf `I_Δ² E`. -/
def VanishesQuadraticallyAlongDiagonal {X : Scheme}
    (s : X ⟶ ComplexBase) [AlgebraicGeometry.IsSeparated s]
    (E : OModule (SelfProduct s))
    (σ : AlgebraicSection E) : Prop :=
  VanishesToOrderAlongDiagonal s E σ 2

/-- A twisted two-point section for a specified sheaf `E` on X×X.
    In the future, take `E = L ⊠ L` with its canonical interchange
    linearization. We do NOT call an arbitrary E an external tensor. -/
structure TwoPointSection {X : Scheme} (s : X ⟶ ComplexBase)
    (E : OModule (SelfProduct s)) where
  value : AlgebraicSection E

/-- A two-point section with the essential quadratic-vanishing property
    occurring in the contact-Fano argument. No symmetry is claimed yet. -/
structure QuadraticallyVanishingTwoPointSection {X : Scheme}
    (s : X ⟶ ComplexBase) [AlgebraicGeometry.IsSeparated s]
    (E : OModule (SelfProduct s)) where
  datum : TwoPointSection s E
  vanishing : VanishesQuadraticallyAlongDiagonal s E datum.value

/-! ## 3C. Principal-parts (jet) sheaves from the diagonal -/

/-- The map from the order-(k+1) neighborhood of the diagonal to the
    **first** copy of X. -/
noncomputable abbrev jetSourceProjection {X : Scheme}
    (s : X ⟶ ComplexBase) (k : ℕ) :
    diagonalJetNeighborhood s k ⟶ X :=
  diagonalPowerInclusion s (k + 1) ≫ firstProjection s

/-- The map from the same neighborhood to the **second** copy of X. -/
noncomputable abbrev jetTargetProjection {X : Scheme}
    (s : X ⟶ ComplexBase) (k : ℕ) :
    diagonalJetNeighborhood s k ⟶ X :=
  diagonalPowerInclusion s (k + 1) ≫ secondProjection s

/-- The intrinsic sheaf of principal parts of order `k` of an O_X-module E,
    under the explicitly required separatedness assumption on `s`:

    P^k_X(E) = p₁* ( O_{Δ^(k)} ⊗ p₂*E ).

    In this expression the tensor by the structure sheaf is implemented
    by *pullback along p₂* to the infinitesimal neighborhood, not by an
    unimplemented tensor operation on sheaves. The `p₁*` is mathlib's
    actual pushforward of sheaves of modules.

    This is a sheaf of O_X-modules. Local freeness requires hypotheses
    and is NOT asserted here. -/
noncomputable abbrev PrincipalPartsSheaf {X : Scheme}
    (s : X ⟶ ComplexBase) [AlgebraicGeometry.IsSeparated s]
    (E : OModule X) (k : ℕ) : OModule X :=
  (Scheme.Modules.pushforward (jetSourceProjection s k)).obj
    ((Scheme.Modules.pullback (jetTargetProjection s k)).obj E)

/-- First principal parts/first jets: `P¹_X(E)`. -/
noncomputable abbrev FirstJetSheaf {X : Scheme}
    (s : X ⟶ ComplexBase) [AlgebraicGeometry.IsSeparated s]
    (E : OModule X) : OModule X :=
  PrincipalPartsSheaf s E 1

/-- The ordinary 0-jet sheaf `P⁰_X(E)` (expected to be isomorphic to E
    if the diagonal has its standard closed immersion structure). -/
noncomputable abbrev ZeroJetSheaf {X : Scheme}
    (s : X ⟶ ComplexBase) [AlgebraicGeometry.IsSeparated s]
    (E : OModule X) : OModule X :=
  PrincipalPartsSheaf s E 0

/-! ## 3D. Pointwise jets and separation by global sections -/

/-- The ideal sheaf of a specified ℂ-rational point x: Spec(ℂ) → X,
    as the kernel ideal of its scheme morphism. -/
noncomputable abbrev pointIdeal {d : ℕ}
    {X : SmoothProperComplexVariety d} (x : ComplexPoint X) :
    X.scheme.IdealSheafData :=
  x.map.ker

/-- The order-`order` fat point `V(m_x^order)`.
    `order=2` is the first infinitesimal neighborhood at x. -/
noncomputable abbrev pointPowerSubscheme {d : ℕ}
    {X : SmoothProperComplexVariety d}
    (x : ComplexPoint X) (order : ℕ) : Scheme :=
  ((pointIdeal x) ^ order).subscheme

/-- The actual inclusion of the fat point into X. -/
noncomputable abbrev pointPowerInclusion {d : ℕ}
    {X : SmoothProperComplexVariety d}
    (x : ComplexPoint X) (order : ℕ) :
    pointPowerSubscheme x order ⟶ X.scheme :=
  ((pointIdeal x) ^ order).subschemeι


noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo

namespace FatPointOpenFactorizationProof

/-- Positive powers give the same actual topological image as a closed immersion. -/
theorem kernelPowerInclusion_range {Y Z : Scheme} (f : Y ⟶ Z)
    [IsClosedImmersion f] (k : ℕ) (hk : k ≠ 0) :
    Set.range (f.ker ^ k).subschemeι = Set.range f := by
  calc
    _ = ((f.ker ^ k).support : Set Z) :=
      Scheme.IdealSheafData.range_subschemeι _
    _ = (f.ker.support : Set Z) := by
      rw [Scheme.IdealSheafData.support_pow f.ker k hk]
    _ = closure (Set.range f) := Scheme.Hom.support_ker f
    _ = Set.range f := f.isClosedEmbedding.isClosed_range.closure_eq

/-- The preimage is the entire fat point, not merely an open containing its reduction. -/
theorem kernelPower_preimage_eq_top {Y Z : Scheme} (f : Y ⟶ Z)
    [IsClosedImmersion f] (k : ℕ) (hk : k ≠ 0)
    (U : Z.Opens) (hU : Set.range f ⊆ (U : Set Z)) :
    (f.ker ^ k).subschemeι ⁻¹ᵁ U = ⊤ := by
  apply top_unique
  intro z _
  change (f.ker ^ k).subschemeι z ∈ U
  exact hU ((kernelPowerInclusion_range f k hk).le ⟨z, rfl⟩)

/-- A genuine complex point is a closed immersion by its stored section equation. -/
theorem complexPoint_isClosedImmersion {d : ℕ}
    {X : SmoothProperComplexVariety d} (x : ComplexPoint X) :
    IsClosedImmersion x.map :=
  AlgebraicGeometry.isClosedImmersion_of_comp_eq_id X.structureMap x.map x.overC

/-- Direct specialization to the original definitions of the point ideal and its power. -/
theorem pointPower_preimage_eq_top {d : ℕ}
    {X : SmoothProperComplexVariety d} (x : ComplexPoint X)
    (k : ℕ) (hk : k ≠ 0) (U : X.scheme.Opens)
    (hU : Set.range x.map ⊆ (U : Set X.scheme)) :
    pointPowerInclusion x k ⁻¹ᵁ U = ⊤ := by
  letI : IsClosedImmersion x.map := complexPoint_isClosedImmersion x
  exact kernelPower_preimage_eq_top x.map k hk U hU

/-- Membership of the unique complex point is enough for every positive-order fat point. -/
theorem pointPower_preimage_eq_top_of_mem {d : ℕ}
    {X : SmoothProperComplexVariety d} (x : ComplexPoint X)
    (k : ℕ) (hk : k ≠ 0) (U : X.scheme.Opens)
    (z : ComplexBase) (hz : x.map z ∈ U) :
    pointPowerInclusion x k ⁻¹ᵁ U = ⊤ := by
  apply pointPower_preimage_eq_top x k hk U
  rintro _ ⟨w, rfl⟩
  change x.map w ∈ U
  rw [Subsingleton.elim w z]
  exact hz

/-- The actual scheme morphism from V((ker x)^k) to the chosen open. -/
def pointPowerLift {d : ℕ}
    {X : SmoothProperComplexVariety d} (x : ComplexPoint X)
    (k : ℕ) (hk : k ≠ 0) (U : X.scheme.Opens)
    (hU : Set.range x.map ⊆ (U : Set X.scheme)) :
    pointPowerSubscheme x k ⟶ U.toScheme := by
  letI : IsClosedImmersion x.map := complexPoint_isClosedImmersion x
  exact IsOpenImmersion.lift U.ι (pointPowerInclusion x k) (by
    rw [Scheme.Opens.range_ι]
    exact (kernelPowerInclusion_range x.map k hk).le.trans hU)

/-- The factorization has exactly the original fat-point inclusion as its composite. -/
theorem pointPowerLift_fac {d : ℕ}
    {X : SmoothProperComplexVariety d} (x : ComplexPoint X)
    (k : ℕ) (hk : k ≠ 0) (U : X.scheme.Opens)
    (hU : Set.range x.map ⊆ (U : Set X.scheme)) :
    pointPowerLift x k hk U hU ≫ U.ι = pointPowerInclusion x k := by
  unfold pointPowerLift
  exact IsOpenImmersion.lift_fac _ _ _

end FatPointOpenFactorizationProof

end

/-- The restriction map on global sections into sections of the
    order-`k` infinitesimal neighborhood of a point, as a *function on
    morphisms* `O_X → E`. Again the source after pullback is f*O_X,
    canonically but not definitionally the structure sheaf of the fat
    point. -/
noncomputable def jetRestrictionAt {d : ℕ}
    {X : SmoothProperComplexVariety d}
    (x : ComplexPoint X) (E : OModule X.scheme) (k : ℕ) :
    AlgebraicSection E →
      ((Scheme.Modules.pullback (pointPowerInclusion x (k + 1))).obj
          (SheafOfModules.unit X.scheme.ringCatSheaf) ⟶
       (Scheme.Modules.pullback (pointPowerInclusion x (k + 1))).obj E) :=
  fun σ => restrictSection (pointPowerInclusion x (k + 1)) σ

/-- Separation of k-jets at a specified geometric point:

    H⁰(X,E) → H⁰(X, E ⊗ O_X / m_x^(k+1))

    is surjective (expressed using the corresponding sheaf morphisms).
    In particular, `k=1` is first-jet separation, **not** just global
    generation or point separation. -/
def SeparatesJetsAt {d : ℕ}
    {X : SmoothProperComplexVariety d}
    (E : OModule X.scheme) (x : ComplexPoint X) (k : ℕ) : Prop :=
  Function.Surjective (jetRestrictionAt x E k)

/-- A line bundle separates first jets at every ℂ-rational point. -/
def SeparatesFirstJets {d : ℕ}
    (X : SmoothProperComplexVariety d) (L : LineBundle X.scheme) : Prop :=
  ∀ x : ComplexPoint X, SeparatesJetsAt L.sheaf x 1

/-- A line bundle separates k-jets at all ℂ-rational points. -/
def SeparatesJetsEverywhere {d : ℕ}
    (X : SmoothProperComplexVariety d) (L : LineBundle X.scheme)
    (k : ℕ) : Prop :=
  ∀ x : ComplexPoint X, SeparatesJetsAt L.sheaf x k

/-! ## 3E. Affine algebra: actual diagonal ideals and jet rings -/

/-- Coordinate ring of the affine fibre square Spec(A) × Spec(A)
    over Spec(ℂ). Mathlib equips this tensor product with a commutative
    ℂ-algebra structure. -/
abbrev AffineTwoPointRing (A : Type*) [CommRing A] [Algebra ℂ A] :=
  A ⊗[ℂ] A

/-- The diagonal multiplication map `A ⊗_ℂ A → A`, induced by the
    identity `A → A` through mathlib's base-change universal property.
    It sends a pure tensor `a ⊗ b` to `ab`. -/
noncomputable def affineDiagonalMultiplication
    (A : Type*) [CommRing A] [Algebra ℂ A] :
    AffineTwoPointRing A →ₐ[A] A :=
  (AlgHom.liftEquiv ℂ A A A) (AlgHom.id ℂ A)

/-- The kernel of multiplication: the genuine affine diagonal ideal. -/
noncomputable abbrev affineDiagonalIdeal
    (A : Type*) [CommRing A] [Algebra ℂ A] :
    Ideal (AffineTwoPointRing A) :=
  RingHom.ker (affineDiagonalMultiplication A).toRingHom

/-- The ring of k-th principal parts of the affine algebra A:
    `(A ⊗_ℂ A) / I_Δ^(k+1)`.
    The left/right A-actions are available via the two tensor factors,
    though the API relating them is not yet developed here. -/
noncomputable abbrev affinePrincipalParts
    (A : Type*) [CommRing A] [Algebra ℂ A] (k : ℕ) :=
  (AffineTwoPointRing A) ⧸ ((affineDiagonalIdeal A) ^ (k + 1))

/-- Affine vanishing to order at least k along the diagonal. -/
def AffineVanishesToOrder
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (b : AffineTwoPointRing A) (k : ℕ) : Prop :=
  b ∈ (affineDiagonalIdeal A) ^ k

/-- Affine quadratic diagonal vanishing. -/
def AffineVanishesQuadratically
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (b : AffineTwoPointRing A) : Prop :=
  AffineVanishesToOrder A b 2

/-- Genuine exchange symmetry of a regular two-point function:
    the natural tensor-factor flip fixes it. -/
def IsSymmetricAffineTwoPointFunction
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (b : AffineTwoPointRing A) : Prop :=
  (TensorProduct.comm ℂ A A) b = b

/-- The affine vector space underlying an external tensor square of a
    line-bundle module M over Spec(A): `M ⊗_ℂ M`. For a finitely generated
    projective rank-one A-module M, this is the underlying ℂ-module of
    global sections of the external square on Spec(A ⊗_ℂ A).

    The *module structure over A ⊗_ℂ A* is not yet packaged in this file.
    This construction is affine and is NOT the global sheaf `L ⊠ L`. -/
abbrev AffineTwistedTwoPointModule
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (M : Type*) [AddCommGroup M] [Module A M]
    [Module ℂ M] [IsScalarTower ℂ A M] :=
  M ⊗[ℂ] M

/-- Exchange symmetry for an affine, line-bundle-valued two-point
    tensor. This is the *genuine* tensor factor swap; it does not merely
    assume an unexplained symmetry predicate. -/
def IsSymmetricAffineTwistedTwoPointSection
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (M : Type*) [AddCommGroup M] [Module A M]
    [Module ℂ M] [IsScalarTower ℂ A M]
    (b : AffineTwistedTwoPointModule A M) : Prop :=
  (TensorProduct.comm ℂ M M) b = b

end LeBrunSalamon.PhaseThree

/-!
# Phase 4 -- contact symmetries, Hamiltonians, transitivity, and adjoint orbits

The affine part below is built from *actual* derivations and their Lie bracket. For a trivialized contact
form `theta : Der_C(A) →_A A`, it gives the standard infinitesimal condition `[V, ker(theta)] subset
ker(theta)`, the Hamiltonian `theta(V)`, a point-derivation model of the Zariski tangent space, and
surjectivity of evaluation at rational points.

The global part uses actual sheaf morphisms and the categorical group `Aut(X)`. Intrinsic tangent and
differential constructions occur later in Phases 25 and 30; this early phase does not use them; we
therefore speak of contact-*sequence* automorphism candidates. Their chosen sheaf identifications are NOT
yet canonically the differential of the scheme automorphism. Consequently, this is not yet the algebraic
group of contact automorphisms, nor does it define its Lie algebra globally.

The Lie-theoretic part reuses mathlib's adjoint representation and models projective orbits concretely as
sets of one-dimensional linear subspaces. A *marked orbit* is not automatically the adjoint variety: this
requires an algebraic adjoint group, a highest-root line / minimal nonzero nilpotent orbit, and an
algebraic scheme structure on the orbit.

There are no additional `sorry`s or custom axioms.
-/

namespace LeBrunSalamon.PhaseFour

open CategoryTheory
open AlgebraicGeometry
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree

/-! ## 4A. Affine contact vector fields and Hamiltonians -/

/-- A C-derivation `V` is a contact vector field for the (trivialized)
    affine contact form `theta` when `[V,W]` lies in `ker theta` for every
    algebraic vector field `W` in `ker theta`.

    This is a condition on the *distribution*, not on preserving the
    chosen one-form exactly: a contact vector field may satisfy
    `L_V theta = a * theta` for a nonzero function `a`. -/
def IsAffineContactVectorField
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (theta : AffineOneForm A) (V : AffineVectorFields A) : Prop :=
  ∀ W : AffineDistribution theta,
    theta ⁅V, W.1⁆ = 0

/-- Contact vector fields, as a subtype of the *actual* module of
    algebraic derivations. Lie-algebra closure is a theorem to prove,
    not an extra field of this subtype. -/
abbrev AffineContactVectorFields
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (theta : AffineOneForm A) :=
  { V : AffineVectorFields A // IsAffineContactVectorField theta V }

/-- For a trivialized contact line, the contact Hamiltonian of a
    derivation `V` is the regular function `theta(V)`. -/
def affineHamiltonian
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (theta : AffineOneForm A) (V : AffineVectorFields A) : A :=
  theta V

/-- An affine function is a contact Hamiltonian if some **contact**
    vector field maps to it. On a genuine contact affine variety this is
    every regular function, but the assertion is not made here. -/
def IsAffineContactHamiltonian
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (theta : AffineOneForm A) (h : A) : Prop :=
  ∃ V : AffineVectorFields A,
    IsAffineContactVectorField theta V ∧ affineHamiltonian theta V = h

/-- The function obtained by bracketing two contact fields and evaluating
    with `theta`. Once the contact-Hamiltonian correspondence is proved,
    this becomes the Jacobi bracket of their Hamiltonians. -/
def affineJacobiValue
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (theta : AffineOneForm A)
    (V W : AffineContactVectorFields theta) : A :=
  theta ⁅V.1, W.1⁆

/-- An **affine** algebraic automorphism preserving the contact
    distribution. The `tangentTransport` field is not arbitrary: its
    action on every derivation is constrained by conjugation with the
    actual C-algebra automorphism.

    Thus this encodes the genuine distribution-preserving condition on
    Spec(A). It is not a group instance yet, since closure of these
    structures under composition has not been formalized. -/
structure AffineContactAutomorphism
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (θ : AffineOneForm A) where
  algebraAut : A ≃ₐ[ℂ] A
  tangentTransport : AffineVectorFields A ≃ₗ[ℂ] AffineVectorFields A
  transportEq : ∀ (V : AffineVectorFields A) (a : A),
    (tangentTransport V) a = algebraAut (V (algebraAut.symm a))
  preservesDistribution : ∀ V : AffineVectorFields A,
    θ V = 0 ↔ θ (tangentTransport V) = 0

/-! ## 4B. Infinitesimal transitivity on a smooth affine chart -/

/-- A derivation at a C-point `p : A →_C C`, written without a new
    `A`-module structure on C. This is precisely the Leibniz rule for
    the Zariski tangent space `Der_C(A,C_p)`. -/
def IsPointDerivation
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (p : A →ₐ[ℂ] ℂ) (D : A →ₗ[ℂ] ℂ) : Prop :=
  ∀ a b : A,
    D (a * b) = p a * D b + p b * D a

/-- The Zariski tangent vectors at the C-rational point `p` of Spec(A),
    represented as C-linear point derivations. In finite-type smooth
    geometry this is the usual tangent fibre. -/
abbrev AffineTangentAt
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (p : A →ₐ[ℂ] ℂ) :=
  { D : A →ₗ[ℂ] ℂ // IsPointDerivation p D }

/-- Affine contact vector fields span the tangent space at `p` when
    evaluation `V |→ (a |→ p(V(a)))` is onto point derivations.
    The evaluation equation is given on all `a : A`.

    WARNING: this uses vector fields on an *affine chart*, not GLOBAL
    contact vector fields on a compact contact variety. This predicate
    alone cannot imply global homogeneity. -/
def IsAffineInfinitesimallyTransitiveAt
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (theta : AffineOneForm A) (p : A →ₐ[ℂ] ℂ) : Prop :=
  ∀ D : AffineTangentAt A p,
    ∃ V : AffineVectorFields A,
      IsAffineContactVectorField theta V ∧
        ∀ a : A, D.1 a = p (V a)

/-- Affine infinitesimal transitivity at every C-rational point.
    This is a local chart-level notion and must NOT be confused with
    transitivity of GLOBAL contact fields on the projective variety. -/
def IsAffineInfinitesimallyTransitiveEverywhere
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (theta : AffineOneForm A) : Prop :=
  ∀ p : A →ₐ[ℂ] ℂ, IsAffineInfinitesimallyTransitiveAt theta p

/-- The affine, trivially line-bundle-valued moment evaluation at p:
    V |→ p(theta(V)). It is *not* yet a global contact moment map. -/
def affineHamiltonianEvaluation
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (theta : AffineOneForm A) (p : A →ₐ[ℂ] ℂ) :
    AffineContactVectorFields theta → ℂ :=
  fun V => p (affineHamiltonian theta V.1)

/-! ## 4C. Global Hamiltonians and scheme automorphisms -/

/-- A global vector field **relative to the tangent-bundle candidate**.
    Once the candidate is identified with T_X, this is H^0(X,T_X). -/
abbrev GlobalVectorField (n : ℕ) (X : ContactCandidate n) :=
  AlgebraicSection X.tangent.sheaf

/-- A global contact Hamiltonian **as a section of the contact line**:
    H^0(X,T) → H^0(X,L), induced by the actual quotient map T → L.
    To restrict this to contact vector fields, a global Lie derivative
    and the intrinsic tangent sheaf must first be available. -/
noncomputable def globalHamiltonian
    (n : ℕ) (X : ContactCandidate n)
    (V : GlobalVectorField n X) :
    AlgebraicSection X.contactSequence.line.sheaf :=
  V ≫ X.contactSequence.form

/-- Mathlib's genuine group of automorphisms of the underlying scheme.
    The subgroup preserving the *contact* distribution is not yet
    defined without a canonical differential on T_X. -/
abbrev SchemeAutomorphism (X : Scheme) := CategoryTheory.Aut X

/-- Automorphism of the exact contact-*candidate* sequence.  The three
    bundle isomorphisms and two squares really commute after pullback.

    Crucially, `tangentPullbackIso` is a *chosen* isomorphism, not yet
    the canonical differential of `schemeAut`, so this is not by itself
    a fully certified contact automorphism. -/
structure ContactSequenceAutomorphismCandidate
    (n : ℕ) (X : ContactCandidate n) where
  schemeAut : SchemeAutomorphism X.variety.scheme
  overC : schemeAut.hom ≫ X.variety.structureMap = X.variety.structureMap
  tangentPullbackIso :
    (Scheme.Modules.pullback schemeAut.hom).obj X.tangent.sheaf ≅ X.tangent.sheaf
  distributionPullbackIso :
    (Scheme.Modules.pullback schemeAut.hom).obj
        X.contactSequence.distribution.sheaf ≅
      X.contactSequence.distribution.sheaf
  linePullbackIso :
    (Scheme.Modules.pullback schemeAut.hom).obj
        X.contactSequence.line.sheaf ≅
      X.contactSequence.line.sheaf
  preservesDistribution :
    (Scheme.Modules.pullback schemeAut.hom).map X.contactSequence.inclusion ≫
        tangentPullbackIso.hom =
      distributionPullbackIso.hom ≫ X.contactSequence.inclusion
  preservesContactForm :
    (Scheme.Modules.pullback schemeAut.hom).map X.contactSequence.form ≫
        linePullbackIso.hom =
      tangentPullbackIso.hom ≫ X.contactSequence.form

/-- An honest abstract-group action on a C-scheme, by scheme
    automorphisms over C (not merely permutations of its points).
    An algebraic *group-scheme* action is stronger and not yet supplied. -/
structure ComplexSchemeGroupAction
    (G : Type*) [Group G] {d : ℕ}
    (X : SmoothProperComplexVariety d) where
  act : G →* SchemeAutomorphism X.scheme
  overC : ∀ g : G, (act g).hom ≫ X.structureMap = X.structureMap

/-- Transitivity on C-rational points: for every pair p,q there is
    an element g carrying p to q. For geometric homogeneity one will
    additionally require an algebraic group scheme and algebraic action. -/
def ComplexSchemeGroupAction.IsTransitiveOnComplexPoints
    {G : Type*} [Group G] {d : ℕ}
    {X : SmoothProperComplexVariety d}
    (action : ComplexSchemeGroupAction G X) : Prop :=
  ∀ p q : ComplexPoint X,
    ∃ g : G, p.map ≫ (action.act g).hom = q.map

/-- Such an action admits contact-sequence-compatible lifts. This does
    not claim that the lifts form a group action or are actual derivatives. -/
def ComplexSchemeGroupAction.AdmitsContactSequenceLifts
    {G : Type*} [Group G] (n : ℕ)
    (X : ContactCandidate n)
    (action : ComplexSchemeGroupAction G X.variety) : Prop :=
  ∀ g : G,
    ∃ f : ContactSequenceAutomorphismCandidate n X,
      f.schemeAut = action.act g

/-- Pointwise homogeneous *contact-sequence candidate*: a group acts
    transitively on C-points of the scheme, and every group element admits
    compatible lifts on the contact exact sequence. Neither an algebraic
    group action nor compatibility with the canonical tangent differential
    is proved by this definition, so this is NOT yet `IsHomogeneousContact`. -/
def IsPointHomogeneousContactSequenceCandidate
    {G : Type*} [Group G] (n : ℕ)
    (X : ContactCandidate n)
    (action : ComplexSchemeGroupAction G X.variety) : Prop :=
  action.IsTransitiveOnComplexPoints ∧
    action.AdmitsContactSequenceLifts n X

/-! ## 4D. Lie algebra adjoint action and projective orbits -/

/-- The actual adjoint representation of a complex Lie algebra,
    a mathlib Lie algebra homomorphism into its linear endomorphisms. -/
abbrev adjointRepresentation
    (g : Type*) [LieRing g] [LieAlgebra ℂ g] :
    g →ₗ⁅ℂ⁆ Module.End ℂ g :=
  LieAlgebra.ad ℂ g

/-- A vector of the Lie algebra is nilpotent for the adjoint action
    if the endomorphism `ad(v)` is nilpotent. -/
def IsAdjointNilpotent
    {g : Type*} [LieRing g] [LieAlgebra ℂ g]
    (v : g) : Prop :=
  IsNilpotent ((adjointRepresentation g) v)

/-- A group representation on the underlying complex vector space that
    preserves Lie brackets. We do not pretend this is automatically the
    *adjoint group* (or even an algebraic group). -/
structure BracketPreservingLinearAction
    (G : Type*) [Group G]
    (g : Type*) [LieRing g] [LieAlgebra ℂ g] where
  act : G →* (g ≃ₗ[ℂ] g)
  preservesBracket :
    ∀ (sigma : G) (x y : g),
      act sigma ⁅x, y⁆ = ⁅act sigma x, act sigma y⁆

/-- The orbit of a vector, projectivized *as actual linear subspaces*:
    the set of lines span(g.v) in g. This avoids conflating an abstract
    projective-space point with an algebraic Proj-scheme morphism. -/
def projectiveOrbitAsLines
    {G : Type*} [Group G]
    {g : Type*} [LieRing g] [LieAlgebra ℂ g]
    (rho : BracketPreservingLinearAction G g) (v : g) :
    Set (Submodule ℂ g) :=
  { ell | ∃ sigma : G,
      ell = Submodule.span ℂ ({rho.act sigma v} : Set g) }

/-- A nonzero marked orbit for a bracket-preserving group action. The
    nonzero condition ensures its orbit consists of one-dimensional lines;
    the identification with `Projectivization C g` is in mathlib.

    This is NOT yet an adjoint variety: one must additionally specify the
    simple group, its genuine adjoint action, and the **highest-root line**
    (equivalently a minimal nonzero nilpotent orbit). -/
structure MarkedProjectiveLieOrbit
    (G : Type*) [Group G]
    (g : Type*) [LieRing g] [LieAlgebra ℂ g] where
  representation : BracketPreservingLinearAction G g
  markedVector : g
  markedVector_nonzero : markedVector ≠ 0

/-- Projectivized orbit attached to the nonzero marked vector. -/
def MarkedProjectiveLieOrbit.orbit
    {G : Type*} [Group G]
    {g : Type*} [LieRing g] [LieAlgebra ℂ g]
    (O : MarkedProjectiveLieOrbit G g) : Set (Submodule ℂ g) :=
  projectiveOrbitAsLines O.representation O.markedVector

/-- An explicitly checkable nilpotence requirement for a marked orbit.
    Minimality, which singles out the adjoint variety, requires further
    root-theoretic and algebraic-orbit infrastructure. -/
def MarkedProjectiveLieOrbit.IsNilpotent
    {G : Type*} [Group G]
    {g : Type*} [LieRing g] [LieAlgebra ℂ g]
    (O : MarkedProjectiveLieOrbit G g) : Prop :=
  IsAdjointNilpotent O.markedVector

end LeBrunSalamon.PhaseFour

/-!
# Phase 5 -- twistor sphere bundles, real structures and Wolf-family targets

There are two related geometries, which must NOT be conflated:

* Riemannian: given a quaternionic rank-three subbundle Q of End(TM), the
  underlying set of the twistor sphere bundle consists of pairs `(x,J)`,
  where `J in Q_x`, `J^2 = -1` and `J` is orthogonal. **This is constructed
  below from the actual Riemannian tangent spaces**. It is not yet equipped
  with the natural complex manifold structure obtained via Levi--Civita.
  Fibrewise, its standard model is the sphere of unit imaginary quaternions.

* Complex-algebraic: the twistor space of a positive quaternionic-Kähler
  manifold is a contact Fano manifold Z of complex dimension `2n+1` with a
  fixed-point-free antiholomorphic real structure. Its twistor fibres are
  rational curves with **L-degree TWO**, `L|C = O(2)`, and
  `N_(C/Z) = O(1)^(2n)`; these are not PhaseTwo's contact lines (L-degree 1).
  We describe actual morphisms and isomorphism conditions relative to
  SPECIFIED models for O(1) and O(2). Those twists, the intrinsic tangent
  sheaf, the differential, Fano ampleness and the complex structure on the
  Riemannian twistor bundle must still be constructed.

A "real structure" on a complex scheme must be semilinear over complex conjugation. A *relative*
involution over an explicitly supplied base involution is defined below. It is a genuine antiholomorphic
real structure ONLY when that base involution is established to be induced by `Complex.conjAe` (from
mathlib, as an R-algebra automorphism of C).

No classification theorem, twistor theorem or additional `sorry` is assumed. References for the defining
properties: Salamon (1982); LeBrun (1989); standard accounts of positive quaternionic-Kähler twistor
spaces.
-/

namespace LeBrunSalamon.PhaseFive

open CategoryTheory
open AlgebraicGeometry
open LeBrunSalamon
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseFour

/-! ## 5A. Actual underlying twistor sphere bundle from a Q-distribution -/

/-- A single orthogonal complex structure on a real inner product space.
    The relation `J.comp J = -id` means `J^2 = -1` (not J^2 = +1). -/
def IsOrthogonalComplexStructure
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (J : V →ₗ[ℝ] V) : Prop :=
  J.comp J = -(LinearMap.id : V →ₗ[ℝ] V) ∧
  ∀ v w : V, inner ℝ (J v) (J w) = inner ℝ v w

section SphereBundle

variable (n : ℕ) (M : Type*)
variable [EMetricSpace M] [ChartedSpace (Model n) M]
variable [IsManifold (model n) ∞ M]
variable [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
variable [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
  (fun x : M => TangentSpace (model n) x)]
variable [IsRiemannianManifold (model n) M]

/-- The unit sphere of compatible complex structures in Q_x.
    This is a REAL, FIBREWISE geometric definition, not an abstract
    "twistor" predicate. The later result that it is S^2 uses the local
    quaternionic frames from `HasLocalQuaternionicFrames`. -/
abbrev TwistorFiber (Q : QDistribution n M) (x : M) :=
  { J : TangentSpace (model n) x →ₗ[ℝ] TangentSpace (model n) x //
      J ∈ Q x ∧ IsOrthogonalComplexStructure (TangentSpace (model n) x) J }

/-- The underlying SET of the twistor bundle: `(x,J)`, with J in Q_x
    and J^2=-1. The Sigma type has no automatically supplied complex or
    smooth manifold structure; constructing one is a significant task. -/
abbrev TwistorTotalSet (Q : QDistribution n M) :=
  Σ x : M, TwistorFiber n M Q x

/-- Projection from the twistor point-set bundle onto the base. -/
def twistorProjection (Q : QDistribution n M)
    (z : TwistorTotalSet n M Q) : M :=
  z.1

/-- The genuine fibrewise antipodal RELATION `J ↦ -J`.
    The corresponding map of the total bundle and its continuity and
    antiholomorphicity are separate, later constructions. -/
def AreAntipodalInTwistorFiber (Q : QDistribution n M) (x : M)
    (J K : TwistorFiber n M Q x) : Prop :=
  K.1 = -J.1

/-- Two points of the total twistor set are antipodal if they have the
    same base point and opposite complex structures on its tangent space.
    The existential formulation avoids opaque transport across fibres. -/
def AreAntipodalTwistorPoints (Q : QDistribution n M)
    (z w : TwistorTotalSet n M Q) : Prop :=
  ∃ (x : M) (J K : TwistorFiber n M Q x),
    z = ⟨x, J⟩ ∧ w = ⟨x, K⟩ ∧
      AreAntipodalInTwistorFiber n M Q x J K

/-- A model for S^2 from mathlib's ACTUAL quaternion algebra: the unit
    pure imaginary quaternions. No arbitrary 'sphere' type is postulated.
    Via a local quaternionic frame it identifies with the fibre above. -/
abbrev UnitImaginaryQuaternions :=
  { q : Quaternion ℝ // q.re = 0 ∧ Quaternion.normSq q = 1 }

/-- The equation expressing a compatible complex structure in local
    quaternionic frame `(I,J,K)` with unit imaginary quaternion coordinates.
    The local frame is an INPUT, so no global frame is asserted. -/
def IsQuaternionicFrameCoordinate (Q : QDistribution n M) (x : M)
    (I J K : TangentSpace (model n) x →ₗ[ℝ]
      TangentSpace (model n) x)
    (q : UnitImaginaryQuaternions) (Z : TwistorFiber n M Q x) : Prop :=
  IsQuaternionicTriple (TangentSpace (model n) x) I J K ∧
  Q x = Submodule.span ℝ
    ({I, J, K} : Set
      (TangentSpace (model n) x →ₗ[ℝ] TangentSpace (model n) x)) ∧
  Z.1 = q.1.imI • I + q.1.imJ • J + q.1.imK • K

end SphereBundle

/-! ## 5B. Semilinear scheme involutions and their C-valued fixed points -/

/-- Mathlib's genuine complex conjugation as an R-algebra automorphism.
    The induced Spec(C) automorphism still needs to be constructed and
    proven to be the chosen `κ` in the definitions below. -/
abbrev complexConjugation : ℂ ≃ₐ[ℝ] ℂ := Complex.conjAe

/-- A semilinear involution on the complex scheme `X`, relative to a
    SPECIFIED involution `κ` on Spec(C). The cover equation says that
    `τ` is NOT generally a morphism OVER C. It becomes a real structure
    when `κ` is the automorphism induced by the actual conjugation of C.

    `κ` is deliberately a parameter: taking κ=id would yield an ordinary
    holomorphic involution, NOT an antiholomorphic real structure. -/
structure SemilinearSchemeInvolution {X : Scheme}
    (s : X ⟶ ComplexBase) (κ : SchemeAutomorphism ComplexBase) where
  lift : SchemeAutomorphism X
  coversBase : lift.hom ≫ s = s ≫ κ.hom
  square : lift.hom ≫ lift.hom = 𝟙 X
  baseSquare : κ.hom ≫ κ.hom = 𝟙 ComplexBase

/-- The action of a semilinear involution on a C-rational point `p`:
    p |-> κ ∘ p ∘ τ, in categorical composition order. Its target is
    again a C-point if the compatibility and involution laws hold;
    that theorem is intentionally not formalized here. -/
def semilinearConjugatePoint {X : Scheme}
    {s : X ⟶ ComplexBase} {κ : SchemeAutomorphism ComplexBase}
    (τ : SemilinearSchemeInvolution s κ)
    (p : ComplexBase ⟶ X) : ComplexBase ⟶ X :=
  κ.hom ≫ p ≫ τ.lift.hom

/-- Fixed-point-free means NO fixed C-valued geometric point, not
    absence of fixed points in the UNDERLYING scheme (generic points can
    be fixed even for genuine antiholomorphic real structures). -/
def IsFixedPointFreeOnComplexPoints {X : Scheme}
    {s : X ⟶ ComplexBase} {κ : SchemeAutomorphism ComplexBase}
    (τ : SemilinearSchemeInvolution s κ) : Prop :=
  ∀ p : ComplexBase ⟶ X,
    p ≫ s = 𝟙 ComplexBase →
      semilinearConjugatePoint τ p ≠ p

/-! ## 5C. Twistor lines and their correct contact degree -/

/-- A candidate TWISTOR LINE `f : P^1 → Z` with the prescribed restriction
    `f^* L = O(2)`. The supplied bundle `O2` must INDEPENDENTLY be identified
    with mathlib's geometric O(2); using an arbitrary line bundle here would
    weaken the meaning. Twistor lines have degree 2 for the contact line.

    Compare PhaseTwo.ContactLineCandidate, where the degree is ONE. -/
structure TwistorLineCandidate (P : ProjectiveLineOverC)
    (n : ℕ) (X : ContactCandidate n)
    (O2 : LineBundle ProjectiveLine) where
  curve : RationalCurve P X.variety
  contactDegreeTwo :
    Nonempty (pullbackLineSheaf curve.map X.contactSequence.line ≅ O2.sheaf)

/-- Twistor line together with a normal exact sequence and the normal
    splitting `N_{C/Z} ≅ O(1)^(2n)`, relative to a SUPPLIED model for
    that direct sum. The latter needs its own construction from O(1).
    Also `normalSequence.differential` must later be identified with df.
    Hence this remains a candidate, not an embedded twistor line. -/
structure TwistorLineNormalCandidate (P : ProjectiveLineOverC)
    (n : ℕ) (X : ContactCandidate n)
    (TP1 : AlgebraicVectorBundle ProjectiveLine 1)
    (O2 : LineBundle ProjectiveLine)
    (expectedNormal : AlgebraicVectorBundle ProjectiveLine (2 * n)) where
  line : TwistorLineCandidate P n X O2
  normalSequence : NormalSequenceCandidate P n X
    ⟨line.curve.map, line.curve.overC⟩ TP1
  correctNormalType :
    Nonempty (normalSequence.normal.sheaf ≅ expectedNormal.sheaf)

/-- An invariant twistor line equipped with candidate real structures
    on both source and target, semilinear over the SAME involution κ.
    The fixed-point-free restriction is appropriate for the antipodal
    real structure of a twistor fibre. To obtain an actual real twistor
    line, κ must be complex conjugation and the P¹ involution must be
    identified with its standard antipodal real structure. -/
structure RealTwistorLineCandidate (P : ProjectiveLineOverC)
    (n : ℕ) (X : ContactCandidate n)
    (O2 : LineBundle ProjectiveLine)
    (κ : SchemeAutomorphism ComplexBase)
    (τZ : SemilinearSchemeInvolution X.variety.structureMap κ)
    (τP : SemilinearSchemeInvolution P.structureMap κ) where
  line : TwistorLineCandidate P n X O2
  invariantCurve :
    τP.lift.hom ≫ line.curve.map = line.curve.map ≫ τZ.lift.hom
  antipodalSource : IsFixedPointFreeOnComplexPoints τP

/-! ## 5D. Scale-isometries, and an INDEX of the Wolf-space list -/

/-- Metric homothety: an actual bijection scaling extended distances by
    a *positive finite* constant. For Riemannian manifolds, the classical
    smoothness of metric isometries relates this to homothety of metrics,
    but it is NOT proved here. The metric itself is not just a label. -/
structure MetricHomothety (A B : Type*) [EMetricSpace A] [EMetricSpace B] where
  toEquiv : A ≃ B
  distanceScale : ℝ≥0∞
  scale_pos : 0 < distanceScale
  scale_finite : distanceScale ≠ ⊤
  preservesDistanceUpToScale :
    ∀ x y : A, edist (toEquiv x) (toEquiv y) = distanceScale * edist x y

/-- The classical compact Wolf families, as a finite *indexing family*.
    These constructors are NOT definitions of the corresponding Lie-group
    quotients, and hence this does NOT define an arbitrary manifold to be
    Wolf merely by giving it a label.

    The integer parameters in the three classical series encode
    quaternionic dimension n, i.e. real dimension 4n. -/
inductive WolfFamily where
  | quaternionicProjective (n : ℕ)    -- HP^n = Sp(n+1)/(Sp(n) Sp(1))
  | complexGrassmannianTwo (n : ℕ) -- Gr_2(C^(n+2))
  | orientedRealGrassmannianFour (n : ℕ) -- Gr^+_4(R^(n+4))
  | exceptionalG2   -- G2 / SO(4), quaternionic dimension 2
  | exceptionalF4   -- F4 / (Sp(3) Sp(1)), dimension 7
  | exceptionalE6   -- E6 / (SU(6) Sp(1)), dimension 10
  | exceptionalE7   -- E7 / (Spin(12) Sp(1)), dimension 16
  | exceptionalE8   -- E8 / (E7 Sp(1)), dimension 28
  deriving DecidableEq, Repr

/-- Quaternionic (not real) dimension associated with a Wolf-family
    label. The associated real dimension is four times this number. -/
def WolfFamily.quaternionicDimension : WolfFamily → ℕ
  | .quaternionicProjective n => n
  | .complexGrassmannianTwo n => n
  | .orientedRealGrassmannianFour n => n
  | .exceptionalG2 => 2
  | .exceptionalF4 => 7
  | .exceptionalE6 => 10
  | .exceptionalE7 => 16
  | .exceptionalE8 => 28

/-- Restrict the list to quaternionic dimension n >= 2 as in the main
    conjecture. Actual compact homogeneous metrics must still be built. -/
def WolfFamily.IsRelevantInDimension (W : WolfFamily) (n : ℕ) : Prop :=
  2 ≤ n ∧ W.quaternionicDimension = n

end LeBrunSalamon.PhaseFive

 
/-!
# Phase 6 -- projective exception, genuine real structures, and the twistor bridge

This phase organizes the reduction to the Wolf-space conclusion. It fixes three significant weaknesses
exposed by the mathematical audit:

* Contact lines of contact degree **one** do not exist on standard contact
  odd-dimensional projective space, where L = O(2). Their use must follow
  a projective-space/other-case distinction. No universal covering theorem
  by degree-one lines is assumed here.
* A semilinear map over an *arbitrary* involution of Spec(C) is not yet a
  real structure. We now use the Spec-morphism arising from the ACTUAL
  conjugation of complex numbers.
* Analytic points of a complex manifold correspond to C-VALUED points
  of its algebraic model, NOT to all scheme-theoretic points (which include
  generic points). A prospective twistor comparison respects this distinction.

The homogeneous Wolf models are compact group quotients G/H with their specific symmetric metrics; a
family label or an arbitrary abstract quotient G/H is not sufficient. The definitions below deliberately
call such models CANDIDATES until their groups and metrics are constructed.

No new theorem, proof, sorry, axiom, or classification result is added.
-/

namespace LeBrunSalamon.PhaseSix

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open LeBrunSalamon
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseFour
open LeBrunSalamon.PhaseFive

/-! ## 6A. The projective-space exception to contact-line constructions -/

/-- The actual algebraic projective space of dimension `2*n+1`, built
    from the homogeneous polynomial grading. A compatible standard
    morphism to `Spec(C)` and its twisting sheaves are separate tasks. -/
noncomputable abbrev OddProjectiveSpace (n : ℕ) : Scheme :=
  AlgebraicGeometry.Proj
    (MvPolynomial.homogeneousSubmodule (Fin (2 * n + 2)) ℂ)

/-- A *candidate* identification of a contact manifold with odd projective
    space, INCLUDING the contact-line bundle. The line model passed as
    `O2` must later be identified with the actual `O(2)`, and the contact
    distribution must be identified with the standard symplectic one.

    This is deliberately stronger than a mere isomorphism of schemes, but
    not yet a contact isomorphism: the contact differential is missing. -/
structure ProjectiveContactSpaceCase (n : ℕ) (X : ContactCandidate n)
    (projectiveStructureMap : OddProjectiveSpace n ⟶ ComplexBase)
    (O2 : LineBundle (OddProjectiveSpace n)) where
  schemeIso : X.variety.scheme ≅ OddProjectiveSpace n
  overC : schemeIso.hom ≫ projectiveStructureMap = X.variety.structureMap
  compatibleContactLine : Nonempty
    ((Scheme.Modules.pullback schemeIso.hom).obj O2.sheaf ≅
      X.contactSequence.line.sheaf)

/-- The covering-by-contact-lines input for the NON-projective branch.
    This says every C-valued point belongs to a rational curve of
    contact degree one; it is not automatically a consequence of
    `ContactCandidate` or of an arbitrary model for `O(1)`.

    In later proofs one may first establish it on a suitable dense open
    subset; that is a different, weaker predicate. -/
def HasCoveringFamilyOfContactLines
    (P : ProjectiveLineOverC) (n : ℕ) (X : ContactCandidate n)
    (O1 : LineBundle ProjectiveLine) : Prop :=
  ∀ x : ComplexPoint X.variety,
    ∃ ℓ : ContactLineCandidate P n X O1,
      PassesThrough P X.variety ℓ.curve x

/-!A general-point version of contact-line coverage still requires construction of the relevant Zariski-open
locus. It must not be conflated with the all-points predicate above.-/

/-! ## 6B. Genuine complex conjugation on the base scheme -/

/-- Complex conjugation on `Spec(C)` as an actual scheme morphism.
    It is NOT the identity morphism: although Spec(C) has one underlying
    topological point, the map acts nontrivially on its structure sheaf.
    The involution law follows from the corresponding identity for
    `Complex.conjAe`; its Lean proof is not supplied here. -/
noncomputable def conjugationOnComplexBase : ComplexBase ⟶ ComplexBase :=
  AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom
      ((Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toRingHom))

/-- A real structure on a complex scheme covering the ACTUAL complex
    conjugation morphism. Unlike the PhaseFive relative semilinear
    involution, the base map cannot silently be chosen as the identity. -/
structure ConjugationRealStructure {X : Scheme}
    (s : X ⟶ ComplexBase) where
  involution : SchemeAutomorphism X
  coversConjugation :
    involution.hom ≫ s = s ≫ conjugationOnComplexBase
  squaresToId : involution.hom ≫ involution.hom = 𝟙 X

/-- A genuine real structure has no fixed C-valued points, where the
    conjugate of `p` is `conj ≫ p ≫ tau`. It is incorrect to require
    absence of fixed arbitrary scheme points (e.g., a generic point). -/
def ConjugationRealStructure.HasNoFixedComplexPoints
    {X : Scheme} {s : X ⟶ ComplexBase}
    (τ : ConjugationRealStructure s) : Prop :=
  ∀ p : ComplexBase ⟶ X,
    p ≫ s = 𝟙 ComplexBase →
      conjugationOnComplexBase ≫ p ≫ τ.involution.hom ≠ p

/-! ## 6C. Analytic twistor points versus algebraic C-rational points -/

section PointCorrespondence

variable (n : ℕ) (M : Type*)
variable [EMetricSpace M] [ChartedSpace (Model n) M]
variable [IsManifold (model n) ∞ M]
variable [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
variable [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
  (fun x : M => TangentSpace (model n) x)]
variable [IsRiemannianManifold (model n) M]

/-- The POINT-SET comparison required by a twistor correspondence. The
    algebraic target consists of C-rational/closed points, rather than
    arbitrary scheme points. This is not yet a biholomorphism: neither
    the smooth/complex structure on `TwistorTotalSet` nor the analytic
    topology on the algebraic points is currently built.

    Compatibility with the real involution is expressed via the
    *concrete* conjugation morphism of `Spec(C)`. -/
structure TwistorPointCorrespondence
    (Q : QDistribution n M) (X : ContactCandidate n)
    (τ : ConjugationRealStructure X.variety.structureMap) where
  points : TwistorTotalSet n M Q ≃ ComplexPoint X.variety
  respectsAntipodes :
    ∀ z w : TwistorTotalSet n M Q,
      AreAntipodalTwistorPoints n M Q z w ↔
        conjugationOnComplexBase ≫ (points z).map ≫ τ.involution.hom =
          (points w).map

end PointCorrespondence

/-! ## 6D. Genuine underlying homogeneous quotients; NOT Wolf labels -/

/-- The underlying coset space `G/H`. Mathlib supports quotients by ANY
    subgroup here, not only normal subgroups: no group structure on G/H
    is required. -/
abbrev HomogeneousCosetSpace
    (G : Type*) [Group G] (H : Subgroup G) := G ⧸ H

/-- A supplied metric on an actual coset space G/H. An isometry-invariance
    property is defined separately. No Lie-group topology, symmetric
    metric, or quaternionic structure is silently inferred. -/
structure HomogeneousCosetMetric
    (G : Type*) [Group G] (H : Subgroup G) where
  metric : EMetricSpace (HomogeneousCosetSpace G H)

/-- Left translation acts by isometries of the specified metric. This
    definition compares actual quotient cosets and extended distances;
    it does NOT say the metric is the correct Wolf symmetric metric. -/
def HomogeneousCosetMetric.IsLeftInvariant
    {G : Type*} [Group G] {H : Subgroup G}
    (W : HomogeneousCosetMetric G H) : Prop :=
  letI : EMetricSpace (HomogeneousCosetSpace G H) := W.metric
  ∀ a x y : G,
    edist (((a * x : G) : HomogeneousCosetSpace G H))
          (((a * y : G) : HomogeneousCosetSpace G H)) =
      edist ((x : HomogeneousCosetSpace G H))
            ((y : HomogeneousCosetSpace G H))

/-- A Wolf-FAMILY-LABELLED homogeneous quotient with a supplied metric.
    The family and quaternionic dimension are correctly constrained,
    but we have NOT verified that G,H are the named compact Lie group
    and isotropy subgroup. Therefore the word `Candidate` is essential. -/
structure WolfQuotientCandidate
    (G : Type*) [Group G] (H : Subgroup G) (n : ℕ) where
  family : WolfFamily
  dimension : family.IsRelevantInDimension n
  metric : HomogeneousCosetMetric G H
  leftInvariant : metric.IsLeftInvariant

/-- The actual metric-homothety condition from a given metric space to
    the explicitly specified quotient. It says nothing about whether
    this quotient is a genuine Wolf space until the group, isotropy,
    and metric identifications are constructed. -/
def IsHomotheticToSpecifiedQuotient
    {G M : Type*} [Group G] [EMetricSpace M]
    {H : Subgroup G} {n : ℕ}
    (W : WolfQuotientCandidate G H n) : Prop :=
  letI : EMetricSpace (HomogeneousCosetSpace G H) := W.metric.metric
  Nonempty (MetricHomothety M (HomogeneousCosetSpace G H))

end LeBrunSalamon.PhaseSix

/-!
# Phase 7 -- further proof-oriented definitions and boundary repairs

These declarations add the remaining PROOF-LEVEL NOTIONS that can be stated with the existing mathlib
interfaces and the preceding phases. They do not claim to complete algebraic contact geometry, the moduli
of stable maps, positive line bundles, twistor integrability, or the Wolf classification.

Particularly important improvements:
* very freeness is encoded via simultaneous evaluation of GLOBAL SECTIONS
  at two distinct points of P^1; the equivalence with positivity of every
  Birkhoff--Grothendieck summand is an external theorem, not a definition;
* contact conics of L-degree 2 are not declared to be twistor fibres;
* the schematic compatibility of the projective-line base with the
  canonical Proj-to-Spec-of-degree-zero morphism is now expressible;
* a two-component gluing candidate is kept distinct from a **nodal** scheme;
* the leading-order diagonal symbol is represented by congruence modulo
  I^(k+1), without postulating unconstructed sheaf quotients;
* first-jet exactness is formulated with the ACTUAL principal-parts sheaf,
  and an explicit supplied model of Omega^1_X tensor L;
* global transitivity is phrased using a separately specified collection
  of genuine global tangent sections, which must later be shown to be
  precisely the infinitesimal contact automorphisms.

None of these declarations is an extra theorem, axiom, or sorry.
-/

namespace LeBrunSalamon.PhaseSeven

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open LeBrunSalamon
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseFour
open LeBrunSalamon.PhaseFive
open LeBrunSalamon.PhaseSix

/-! ## 7A. Canonical structure map now defined in PhaseTwo

The earlier `ProjectiveLineModel` wrapper has been removed: it was redundant and allowed two competing
choices of the degree-zero identification. The sole base morphism is now
`ProjectiveLineOverC.structureMap` from PhaseTwo, defined using `Proj.toSpecZero`. Its chosen degree-zero
isomorphism still requires identification with the one induced by constants.-/

/-! ## 7B. Two-point evaluation and very free rational curves -/

/-- Nonvacuity: the chosen complex model of P^1 has two distinct C-valued points. This is automatic for
the standard P^1_C, but is not formally proved by the current Proj construction. -/
def HasTwoDistinctComplexPoints (P : ProjectiveLineOverC) : Prop :=
  ∃ p q : ProjectiveLinePoint P, p.map ≠ q.map

/-- An O-module `E` on P^1 can interpolate arbitrary values at two
DISTINCT C-valued points using a SINGLE global section. This uses the
actual restriction maps from Phase 3 and *requires that such a pair of
points exists*, preventing a vacuous definition for a bad base map.

For a vector bundle on the standard P^1 it is equivalent to every
summand of its Birkhoff--Grothendieck splitting having degree at least
one. That comparison is not proved here. -/
noncomputable def IsTwoPointGloballyGenerated
    (P : ProjectiveLineOverC) (E : OModule ProjectiveLine) : Prop :=
  HasTwoDistinctComplexPoints P ∧
    ∀ p q : ProjectiveLinePoint P, p.map ≠ q.map →
      Function.Surjective
        (fun σ : AlgebraicSection E =>
          (restrictSection p.map σ, restrictSection q.map σ))

/-- The standard very-free condition on a rational curve, expressed
without a not-yet-constructed `O(-1)` or an arbitrary candidate for
`O(1)`: the pulled-back tangent sheaf separates two distinct points.

This agrees with `f^*T_X` being ample ONCE the supplied `TX` is identified
with the intrinsic tangent sheaf and standard facts about bundles on
P^1 are available. -/
noncomputable def IsVeryFreeRationalCurve
    (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d)
    (TX : AlgebraicVectorBundle X.scheme d)
    (f : RationalCurve P X) : Prop :=
  IsTwoPointGloballyGenerated P (pullbackModule f.map TX.sheaf)

/-- A genuinely two-marked rational map with very free pulled-back
tangent sheaf. The two markings are distinct by construction. -/
structure TwoPointedVeryFreeCurve
    (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d)
    (TX : AlgebraicVectorBundle X.scheme d) where
  marked : TwoPointedRationalCurve P X
  veryFree : IsVeryFreeRationalCurve P X TX marked.curve

/-- Two-point evaluation, without quotienting parametrized curves by `Aut(P^1)`. This is a pair of actual
scheme morphisms Spec(C) -> X; the fact they are C-points is entailed by the over-C conditions above. -/
def twoPointEvaluation
    (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d)
    (f : TwoPointedRationalCurve P X) :
    (ComplexBase ⟶ X.scheme) × (ComplexBase ⟶ X.scheme) :=
  (f.first.map ≫ f.curve.map, f.second.map ≫ f.curve.map)

/-- Every ordered pair of C-points is connected by a rational curve with two specified distinct preimages.
This is an honest incidence condition, and does NOT assume a moduli space of curves exists. -/
def IsTwoPointRationallyConnected
    (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) : Prop :=
  ∀ x y : ComplexPoint X,
    ∃ f : TwoPointedRationalCurve P X,
      f.first.map ≫ f.curve.map = x.map ∧
      f.second.map ≫ f.curve.map = y.map

/-- Stronger two-point connectedness by VERY FREE rational curves. This condition is often a consequence
of rational connectedness for smooth projective varieties in characteristic zero, but we do not use or
assert that nontrivial theorem here. -/
def IsTwoPointVeryFreeConnected
    (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d)
    (TX : AlgebraicVectorBundle X.scheme d) : Prop :=
  ∀ x y : ComplexPoint X,
    ∃ f : TwoPointedVeryFreeCurve P X TX,
      f.marked.first.map ≫ f.marked.curve.map = x.map ∧
      f.marked.second.map ≫ f.marked.curve.map = y.map

/-! ## 7C. Contact conics versus twistor lines -/

/-- A *rational contact-degree-two curve*, relative to a supplied model of `O_{P^1}(2)`. This is
intentionally neutral: such a curve may be a twistor line, a smoothing of two contact lines, or neither.
The term `conic` here refers to CONTACT DEGREE, not to an embedding into an unspecified ambient projective
space. -/
structure ContactDegreeTwoCurveCandidate
    (P : ProjectiveLineOverC) (n : ℕ)
    (X : ContactCandidate n)
    (O2 : LineBundle ProjectiveLine) where
  curve : RationalCurve P X.variety
  contactDegreeTwo :
    Nonempty (pullbackLineSheaf curve.map X.contactSequence.line ≅ O2.sheaf)

/-- A degree-two contact curve that is very free relative to the supplied tangent sheaf. Unlike a twistor
line, no real structure or normal-splitting property is required. -/
structure VeryFreeContactConicCandidate
    (P : ProjectiveLineOverC) (n : ℕ)
    (X : ContactCandidate n)
    (O2 : LineBundle ProjectiveLine) where
  conic : ContactDegreeTwoCurveCandidate P n X O2
  veryFree :
    IsVeryFreeRationalCurve P X.variety X.tangent conic.curve

/-- The affine contact velocity `theta(V)` is a nonzero element of A. On a reduced irreducible affine
variety this makes the vector field transverse on a dense open set, but nonzero need NOT imply pointwise
transversality on a nonreduced scheme. The pullback of the one-form along a rational curve still needs to
be constructed separately. -/
def HasNonzeroAffineContactVelocity
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (theta : AffineOneForm A) (V : AffineVectorFields A) : Prop :=
  theta V ≠ 0

/-- An everywhere-transverse affine derivation has an invertible Hamiltonian. This is stronger than
nonzero transversality at a generic point, and is not a definition of a transverse rational curve. -/
def IsAffineEverywhereContactTransverse
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (theta : AffineOneForm A) (V : AffineVectorFields A) : Prop :=
  IsUnit (theta V)

/-! ## 7D. A real gluing specification for two components -/

/-- A scheme-theoretic *candidate* realization of two P^1-components meeting at a marked C-point. The maps
and incidence equations are actual scheme morphisms. They do NOT force the source to be reduced,
connected, exactly nodal, or without additional embedded components. Those geometric properties require a
local-ring/node API. -/
structure GluedTwoComponentMapCandidate
    (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) where
  pair : TwoComponentCurve P X
  source : Scheme
  sourceToC : source ⟶ ComplexBase
  targetMap : source ⟶ X.scheme
  targetOverC : targetMap ≫ X.structureMap = sourceToC
  leftInclusion : ProjectiveLine ⟶ source
  rightInclusion : ProjectiveLine ⟶ source
  leftOverC : leftInclusion ≫ sourceToC = P.structureMap
  rightOverC : rightInclusion ≫ sourceToC = P.structureMap
  leftMap : leftInclusion ≫ targetMap = pair.left.map
  rightMap : rightInclusion ≫ targetMap = pair.right.map
  nodeGlue :
    pair.leftNode.map ≫ leftInclusion =
      pair.rightNode.map ≫ rightInclusion

/-- A chosen identification of the special fibre of a flat proper family with a specified two-component
*candidate*. The comparison really commutes with the map into X. This is not yet a genuine nodal smoothing
without a local node condition on the source and a theorem on arithmetic genus. -/
structure TwoComponentSmoothingCandidate
    (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) where
  family : SmoothGeneralFibreSetup X
  source : GluedTwoComponentMapCandidate P X
  fibreIso :
    fibreScheme family.setup.family family.setup.special ≅ source.source
  fibreMapAgreement :
    fibreIso.hom ≫ source.targetMap =
      fibreEvaluation family.setup.family family.setup.special

/-! ## 7E. Diagonal symbols, twisted jets and their exact sequence -/

/-- Two affine functions with vanishing order at least k have the SAME leading symbol in
I_Delta^k/I_Delta^(k+1) precisely when they differ by an element of I_Delta^(k+1). This defines congruence
WITHOUT postulating a quotient sheaf that mathlib may not yet construct. -/
def HaveSameAffineDiagonalSymbol
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (u v : AffineTwoPointRing A) (k : ℕ) : Prop :=
  AffineVanishesToOrder A u k ∧
  AffineVanishesToOrder A v k ∧
  u - v ∈ (affineDiagonalIdeal A) ^ (k + 1)

/-- The first nonzero diagonal order of an affine two-point function.
A zero function has no such order.  This is NOT a valuation in general. -/
def HasExactAffineDiagonalOrder
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (u : AffineTwoPointRing A) (k : ℕ) : Prop :=
  AffineVanishesToOrder A u k ∧
  ¬ AffineVanishesToOrder A u (k + 1)

/-- The sign-reversing tensor-factor symmetry of an ordinary affine two-point function. Both symmetry and
antisymmetry can be necessary in contact-geometric two-point constructions; they must not be conflated. -/
def IsAntisymmetricAffineTwoPointFunction
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (u : AffineTwoPointRing A) : Prop :=
  (TensorProduct.comm ℂ A A) u = -u

/-- The analogous alternating symmetry for an external square of a module over an affine algebra, prior to
constructing the global `L \boxtimes L` and its factor-interchange linearization. -/
def IsAntisymmetricAffineTwistedTwoPointSection
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (M : Type*) [AddCommGroup M] [Module A M]
    [Module ℂ M] [IsScalarTower ℂ A M]
    (u : AffineTwistedTwoPointModule A M) : Prop :=
  (TensorProduct.comm ℂ M M) u = -u

/-- The fundamental first-principal-parts sequence `0 -> Omega_X^1 tensor L -> P^1_X(L) -> L -> 0`, where
`cotangentTwisted` is a SUPPLIED module sheaf that still must be identified with the intrinsically
constructed `Omega_X^1 tensor L`. The first principal-parts term itself is NOT a placeholder. -/
structure FirstJetExactSequenceCandidate
    {X : Scheme} (s : X ⟶ ComplexBase)
    [AlgebraicGeometry.IsSeparated s]
    (L : LineBundle X)
    (cotangentTwisted : OModule X) where
  inclusion : cotangentTwisted ⟶ FirstJetSheaf s L.sheaf
  projection : FirstJetSheaf s L.sheaf ⟶ L.sheaf
  compZero : inclusion ≫ projection = 0
  shortExact :
    ({ X₁ := cotangentTwisted
       X₂ := FirstJetSheaf s L.sheaf
       X₃ := L.sheaf
       f := inclusion
       g := projection
       zero := compZero } : ShortComplex (OModule X)).ShortExact

/-! ## 7F. Global contact-field evaluation and Hamiltonian richness -/

/-- Every algebraic function on a trivialized affine contact chart comes from some *contact* derivation,
by the Hamiltonian map. On a genuine contact affine variety this is a standard contact identity; its proof
is NOT supplied here. -/
def IsAffineHamiltonianSurjective
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (theta : AffineOneForm A) : Prop :=
  ∀ h : A, IsAffineContactHamiltonian theta h

/-- A specified set of GLOBAL sections of the supplied tangent sheaf
spans tangent directions at every C-rational point when their
restrictions are surjective. This is significantly stronger than the
affine-chart-level transitivity notion in Phase 4.

The set `S` must later be IDENTIFIED WITH actual global contact vector
fields via the Lie derivative of the intrinsic distribution. Until that
point this definition must NOT be called contact homogeneity. -/
noncomputable def SpecifiedGlobalFieldsSpanEverywhere
    (n : ℕ) (X : ContactCandidate n)
    (S : Set (GlobalVectorField n X)) : Prop :=
  ∀ x : ComplexPoint X.variety,
    ∀ v :
      (Scheme.Modules.pullback x.map).obj
        (SheafOfModules.unit X.variety.scheme.ringCatSheaf) ⟶
      (Scheme.Modules.pullback x.map).obj X.tangent.sheaf,
      ∃ V : GlobalVectorField n X,
        V ∈ S ∧ restrictSection x.map V = v

/-- A contact Hamiltonian system consisting of a SPECIFIED set of global tangent sections and its ACTUAL
image under the contact quotient map. This does not identify the set with contact-preserving fields. -/
def IsHamiltonianImageFromSpecifiedFields
    (n : ℕ) (X : ContactCandidate n)
    (S : Set (GlobalVectorField n X))
    (h : AlgebraicSection X.contactSequence.line.sheaf) : Prop :=
  ∃ V : GlobalVectorField n X,
    V ∈ S ∧ globalHamiltonian n X V = h

/-- Surjectivity of the Hamiltonian quotient on the distinguished space of fields. For a genuine global
contact vector-field space and genuine contact manifold this is the standard Hamiltonian principle. This
is a PROPOSITION, not an axiom or an unproved theorem. -/
def IsSpecifiedHamiltonianMapSurjective
    (n : ℕ) (X : ContactCandidate n)
    (S : Set (GlobalVectorField n X)) : Prop :=
  ∀ h : AlgebraicSection X.contactSequence.line.sheaf,
    IsHamiltonianImageFromSpecifiedFields n X S h

/-! ## 7G. Lie simplicity and orbit conditions -/

/-- A simple complex Lie algebra is NONABELIAN and has no proper nonzero Lie ideals. Requiring merely that
`g != 0` would incorrectly classify the one-dimensional abelian Lie algebra as simple. No classification
of simple Lie algebras is assumed here. -/
def IsSimpleComplexLieAlgebra
    (g : Type*) [LieRing g] [LieAlgebra ℂ g] : Prop :=
  (∃ x y : g, ⁅x, y⁆ ≠ 0) ∧
    ∀ I : LieIdeal ℂ g, I = ⊥ ∨ I = ⊤

/-- Data of a simple Lie algebra together with an explicitly chosen nonzero nilpotent marked projective
orbit. Being nilpotent is NOT the same as being the *minimal* nilpotent orbit or highest-root orbit;
minimality and the algebraic scheme of this orbit remain unformalized. -/
structure NilpotentOrbitForSimpleLieAlgebra
    (G : Type*) [Group G]
    (g : Type*) [LieRing g] [LieAlgebra ℂ g] where
  simple : IsSimpleComplexLieAlgebra g
  finiteDimensional : Module.Finite ℂ g
  orbit : MarkedProjectiveLieOrbit G g
  nilpotent : orbit.IsNilpotent

/-! ## 7H. Projectivity as a concrete closed-immersion certificate -/

/-- Ordinary projective n-space as a bona fide `Proj` scheme over the
zero-degree part of C[X_0,...,X_n]. -/
noncomputable abbrev ComplexProjectiveSpace (N : ℕ) : Scheme :=
  AlgebraicGeometry.Proj
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ)

/-- Base of the canonical `Proj.toSpecZero` map on the polynomial ring with N+1 variables. -/
noncomputable abbrev ProjectiveDegreeZeroSpectrum (N : ℕ) : Scheme :=
  Spec (CommRingCat.of ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 0))

/-- A genuine projective embedding into a specified projective space:
`X -> P^N` is a CLOSED IMMERSION of schemes, not an arbitrary map.
Its composite with the Proj-to-degree-zero-then-Spec(C) map is required
to be the given complex structure map on X.

The required normalization of `zeroDegreeIso` by constant polynomials
remains a separate algebraic identification. -/
structure ProjectiveEmbeddingCertificate {d : ℕ}
    (X : SmoothProperComplexVariety d) where
  dimension : ℕ
  zeroDegreeIso :
    ProjectiveDegreeZeroSpectrum dimension ≅ ComplexBase
  embedding : X.scheme ⟶ ComplexProjectiveSpace dimension
  isClosed : AlgebraicGeometry.IsClosedImmersion embedding
  overComplexBase :
    embedding ≫
      ((AlgebraicGeometry.Proj.toSpecZero
        (MvPolynomial.homogeneousSubmodule (Fin (dimension + 1)) ℂ)) ≫
        zeroDegreeIso.hom) = X.structureMap

/-- The projectivity property, formulated by the existence of a specified closed immersion into algebraic
projective space. This is more meaningful than merely requiring properness. -/
def HasProjectiveEmbedding {d : ℕ}
    (X : SmoothProperComplexVariety d) : Prop :=
  Nonempty (ProjectiveEmbeddingCertificate X)

/-- Smooth proper complex geometry with a concrete projective embedding. This is still not a Fano or
contact manifold without canonical-bundle, positivity, tangent-sheaf and contact-Levi data. -/
structure SmoothProjectiveComplexVariety (d : ℕ) where
  variety : SmoothProperComplexVariety d
  projective : ProjectiveEmbeddingCertificate variety

/-- A contact-sequence CANDIDATE with a real projective embedding. Note
carefully that neither ampleness nor global Levi nondegeneracy is present. -/
structure ProjectiveContactCandidate (n : ℕ) where
  contact : ContactCandidate n
  projective : ProjectiveEmbeddingCertificate contact.variety

end LeBrunSalamon.PhaseSeven

/-!
# Phase 8 -- repaired proof interfaces: marked families, nodal pushouts,
# contact velocity, two-point symmetry, and affine test models

The goal of this section is to strengthen earlier *candidates* with actual mathematical conditions,
without turning open geometric assertions into `axiom`s. In particular, we now distinguish:

* a pair of curves with coincident images at marked points from its
  **categorical pushout** (a genuine scheme-theoretic gluing);
* an arbitrary smooth one-dimensional fibre from a fibre isomorphic to
  the **actual projective line**;
* a differential supplied with a normal sequence from the **canonical**
  differential (not yet constructed);
* an abstract involution on a twisted sheaf from a symmetry with an
  explicitly supplied exchange linearization;
* a finite-dimensional nonabelian simple Lie algebra from an arbitrary
  simple Lie algebra, before considering its nilpotent orbits.

None of the constructions below is a proof of their existence. In particular, neither the intrinsic
algebraic tangent/cotangent sheaf nor an ample invertible sheaf is manufactured by choosing an
unconstrained bundle and giving it a suggestive name.
-/

namespace LeBrunSalamon.PhaseEight

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseFour
open LeBrunSalamon.PhaseFive
open LeBrunSalamon.PhaseSix
open LeBrunSalamon.PhaseSeven

/-! ## 8A. Marked flat families and actual evaluation morphisms -/

/-- A **section of the family projection**, i.e. a moving marked point
    on every geometric fibre, rather than an arbitrary section of a
    sheaf or a point on a single fibre. -/
structure MarkedFamilyOfMaps {d : ℕ}
    {X : SmoothProperComplexVariety d}
    (F : ProperFlatFamilyOfMaps X) where
  mark : F.base ⟶ F.total
  sectionLaw : mark ≫ F.projection = 𝟙 F.base

/-- The actual evaluation map from the parameter scheme to the target
    induced by a moving marked point. -/
def MarkedFamilyOfMaps.evaluation {d : ℕ}
    {X : SmoothProperComplexVariety d}
    {F : ProperFlatFamilyOfMaps X}
    (m : MarkedFamilyOfMaps F) : F.base ⟶ X.scheme :=
  m.mark ≫ F.evaluation

/-- Two moving marked points in the *same* flat family.  They remain
    distinct on every ℂ-valued parameter.  Actual disjointness as closed
    subschemes of the total family would be a stronger requirement. -/
structure TwoMarkedFamilyOfMaps {d : ℕ}
    {X : SmoothProperComplexVariety d}
    (F : ProperFlatFamilyOfMaps X) where
  first : MarkedFamilyOfMaps F
  second : MarkedFamilyOfMaps F
  distinctOnComplexParameters :
    ∀ b : ParameterPoint F,
      b.map ≫ first.mark ≠ b.map ≫ second.mark

/-- Evaluation at both marked sections. The codomain is a pair of
    scheme morphisms (the pointwise shadow of an evaluation map to the
    fibre square over Spec ℂ). -/
def TwoMarkedFamilyOfMaps.evaluation {d : ℕ}
    {X : SmoothProperComplexVariety d}
    {F : ProperFlatFamilyOfMaps X}
    (m : TwoMarkedFamilyOfMaps F) :
    (F.base ⟶ X.scheme) × (F.base ⟶ X.scheme) :=
  (m.first.evaluation, m.second.evaluation)

/-! ## 8B. Actual two-component gluing (categorical universal property) -/

/-- The two maps from P¹ with their marked points define a diagram
      P¹ ← Spec ℂ → P¹.
    This property says that the specified source scheme and component
    maps constitute its **pushout in the category of schemes**.  Thus no
    extraneous component or nilpotent thickening may be inserted merely
    because the component maps agree at the chosen point.

    The gluing of two smooth P¹'s at reduced ℂ-points is nodal.  That
    identification with the completed local model ℂ[[u,v]]/(uv) is a
    separate theorem, not part of this definition. -/
def IsTwoComponentPushout
    (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d}
    (D : GluedTwoComponentMapCandidate P X) : Prop :=
  ∀ (Y : Scheme) (g h : ProjectiveLine ⟶ Y),
    D.pair.leftNode.map ≫ g = D.pair.rightNode.map ≫ h →
      ∃! u : D.source ⟶ Y,
        D.leftInclusion ≫ u = g ∧ D.rightInclusion ≫ u = h

/-- Upgraded two-component source: the same maps as in PhaseSeven,
    with the real universal property of the *glued* scheme.  It is
    deliberately not named a stable map: stability, deformation theory,
    and the standard node local equation still require separate proofs. -/
structure PushoutGluedRationalCurve
    (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) where
  source : GluedTwoComponentMapCandidate P X
  gluing : IsTwoComponentPushout P source

/-- A smooth specializable fibre that is genuinely P¹ over ℂ,
    not merely some smooth (possibly positive-genus) curve. -/
def IsProjectiveLineFibre
    (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d}
    (F : ProperFlatFamilyOfMaps X) (b : ParameterPoint F) : Prop :=
  ∃ e : fibreScheme F b ≅ ProjectiveLine,
    e.hom ≫ P.structureMap =
      pullback.snd F.projection b.map

/-- A proper flat family with special fibre the pushout of two P¹'s,
    and a separately identified smooth general fibre P¹.  Hence its
    **geometric** source condition is substantially stronger than the
    earlier `TwoComponentSmoothingCandidate`.

    No assertion about uniqueness or unobstructedness of the deformation
    is introduced. -/
structure GenuineTwoComponentRationalSmoothing
    (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) where
  setup : TwoComponentSmoothingCandidate P X
  /-- Prevents a disconnected base from carrying unrelated fibres on
      different connected components, which would NOT be a smoothing. -/
  baseIrreducible : IrreducibleSpace setup.family.setup.family.base
  /-- Needed for the standard openness theorem for smooth fibres. -/
  locallyFinitePresentation :
    AlgebraicGeometry.LocallyOfFinitePresentation
      setup.family.setup.family.projection
  pushout : IsTwoComponentPushout P setup.source
  generalIsP1 : IsProjectiveLineFibre P
      setup.family.setup.family setup.family.setup.general

/-- The contact-degree-one components of a proposed conic smoothing
    must agree with the two components of its special fibre. The
    agreement is imposed on actual P¹ → X morphisms. -/
structure ContactLineSmoothingCandidate
    (P : ProjectiveLineOverC) (n : ℕ)
    (X : ContactCandidate n)
    (O1 : LineBundle ProjectiveLine) where
  pair : TwoContactLines P n X O1
  family : GenuineTwoComponentRationalSmoothing P X.variety
  leftAgreement :
    family.setup.source.pair.left.map = pair.left.curve.map
  rightAgreement :
    family.setup.source.pair.right.map = pair.right.curve.map

/-! ## 8C. The contact velocity of an immersed-curve candidate -/

/-- The composite T_{P¹} → f* T_X → f* L obtained from an **actual
    morphism of O-modules** in the candidate normal sequence and the
    original contact quotient. The second arrow is mathlib's genuine
    sheaf pullback; only the identification of the first with `df`
    remains to be justified.

    Geometrically, if the first arrow is df, this is f*θ applied to df.
    In particular, contact-tangent curves have zero velocity. -/
noncomputable def contactVelocityCandidate
    (P : ProjectiveLineOverC) (n : ℕ)
    (X : ContactCandidate n)
    (f : ParametrizedCurve P X.variety)
    (TP1 : AlgebraicVectorBundle ProjectiveLine 1)
    (N : NormalSequenceCandidate P n X f TP1) :
    TP1.sheaf ⟶ pullbackModule f.map X.contactSequence.line.sheaf :=
  N.differential ≫
    (Scheme.Modules.pullback f.map).map X.contactSequence.form

/-- Relative to the supplied normal sequence, the contact velocity
    vanishes. After proving that `differential` is df, this says that
    the curve is everywhere tangent to the contact distribution. -/
def IsContactTangentCurveCandidate
    (P : ProjectiveLineOverC) (n : ℕ)
    (X : ContactCandidate n)
    (f : ParametrizedCurve P X.variety)
    (TP1 : AlgebraicVectorBundle ProjectiveLine 1)
    (N : NormalSequenceCandidate P n X f TP1) : Prop :=
  contactVelocityCandidate P n X f TP1 N = 0

/-- Relative to the supplied differential, a nonzero contact velocity.
    On an integral source, a nonzero map of line bundles is generically
    nonzero.  This is not the stronger everywhere-transverse condition. -/
def HasNonzeroContactVelocityCandidate
    (P : ProjectiveLineOverC) (n : ℕ)
    (X : ContactCandidate n)
    (f : ParametrizedCurve P X.variety)
    (TP1 : AlgebraicVectorBundle ProjectiveLine 1)
    (N : NormalSequenceCandidate P n X f TP1) : Prop :=
  contactVelocityCandidate P n X f TP1 N ≠ 0

/-! ## 8D. A coherent (but chosen) global two-point linearization -/

/-- A chosen way to identify a sheaf on X×X with its pullback under
    exchange of factors.  A genuine L⊠L carries a **canonical** such
    identification; this definition does not assert canonicity.
    The unit-sheaf identification is separately specified so that the
    symmetry equation has the correct domain (no implicit coercion from
    `swap* O` to `O`). -/
structure TwoPointExchangeIdentification {X : Scheme}
    (s : X ⟶ ComplexBase)
    (E : OModule (SelfProduct s)) where
  onSheaf :
    (Scheme.Modules.pullback (swapSelfProduct s)).obj E ≅ E
  onUnit :
    (Scheme.Modules.pullback (swapSelfProduct s)).obj
      (SheafOfModules.unit (SelfProduct s).ringCatSheaf) ≅
        SheafOfModules.unit (SelfProduct s).ringCatSheaf

/-- Transport a two-point global section across the selected
    exchange isomorphisms, with the correct unit-sheaf source. -/
noncomputable def TwoPointExchangeIdentification.swapSection
    {X : Scheme} {s : X ⟶ ComplexBase}
    {E : OModule (SelfProduct s)}
    (τ : TwoPointExchangeIdentification s E)
    (σ : AlgebraicSection E) : AlgebraicSection E :=
  τ.onUnit.inv ≫
    (Scheme.Modules.pullback (swapSelfProduct s)).map σ ≫
    τ.onSheaf.hom

/-- A bare chosen swap isomorphism need not have square one. Demand
    involutivity on ALL global sections before defining symmetric or
    antisymmetric sections. A future global construction should prove
    the stronger sheaf-level cocycle identity for L⊠L. -/
def TwoPointExchangeIdentification.IsInvolutiveOnGlobalSections
    {X : Scheme} {s : X ⟶ ComplexBase}
    {E : OModule (SelfProduct s)}
    (τ : TwoPointExchangeIdentification s E) : Prop :=
  ∀ σ : AlgebraicSection E, τ.swapSection (τ.swapSection σ) = σ

/-- Symmetry of an actual global section under an involutive
    factor-exchange operation on global sections.  Its linearization
    must still be identified with the canonical exchange of L⊠L. -/
def IsSymmetricUnderExchange {X : Scheme}
    (s : X ⟶ ComplexBase)
    (E : OModule (SelfProduct s))
    (σ : AlgebraicSection E)
    (τ : TwoPointExchangeIdentification s E) : Prop :=
  τ.IsInvolutiveOnGlobalSections ∧ τ.swapSection σ = σ

/-- The antisymmetric analogue, using the same involutive exchange. -/
def IsAntisymmetricUnderExchange {X : Scheme}
    (s : X ⟶ ComplexBase)
    (E : OModule (SelfProduct s))
    (σ : AlgebraicSection E)
    (τ : TwoPointExchangeIdentification s E) : Prop :=
  τ.IsInvolutiveOnGlobalSections ∧ τ.swapSection σ = -σ

/-! ## 8E. Fully algebraic local contact models -/

/-- A smooth affine contact-chart *candidate*: the entire tangent
    module is explicitly free of the correct rank and the one-form is
    contact in the precise, bracket-nondegenerate sense of PhaseOne.
    This is an honest algebraic condition on A and θ, independent of
    the intrinsic global tangent sheaf introduced in Phase 25. Smoothness of Spec(A) and
    the chart's compatibility with X must be supplied separately. -/
structure FreeAffineContactModel
    (n : ℕ) (A : Type*) [CommRing A] [Algebra ℂ A] where
  tangentFree :
    Nonempty (AffineVectorFields A ≃ₗ[A] (Fin (2 * n + 1) → A))
  form : AffineOneForm A
  nondegenerate : IsAffineContactForm form

/-- The underlying symplectic vector space of the standard affine
    contact model (coordinates x_i,y_i). -/
abbrev StandardContactHorizontal (n : ℕ) :=
  (Fin n → ℂ) × (Fin n → ℂ)

/-- The standard alternating symplectic form
      Σ_i (x_i y'_i - x'_i y_i).
    It is completely explicit and makes it possible to test that later
    abstract contact definitions are non-vacuous on familiar examples.
    Alternation and nondegeneracy have not yet been proved in Lean. -/
def standardContactLevi (n : ℕ)
    (u v : StandardContactHorizontal n) : ℂ :=
  ∑ i : Fin n, (u.1 i * v.2 i - v.1 i * u.2 i)

/-! ## 8F. Explicit dependency ledger for the next genuine completion -/

/-! Historical Phase-8 checkpoint. Intrinsic sheaves, positivity, external
products and their comparison obligations are supplied in Phases 25--35 below.
Their construction proofs, stable-map geometry and analytic twistor geometry
remain open; candidate names are retained solely for compatibility. -/

end LeBrunSalamon.PhaseEight

/-!
# Phase 9 -- statements for the affine contact and rational-curve arguments

This phase begins the proof-obligation layer. Lemmas below are genuine mathematical assertions about types
already constructed in Phases 1--8; nontrivial proofs are deliberately `sorry`. In particular, a `sorry`
is not evidence that an assertion has been checked by Lean.

The algebraic assertions refer to a TRIVIALIZED contact line on an affine chart. No claim is made that an
arbitrary global `ContactCandidate` has such an affine cover: constructing the intrinsic tangent sheaf and
gluing its contact forms are addressed intrinsically in Phases 25--27.
-/

namespace LeBrunSalamon.PhaseNine

open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseFour
open LeBrunSalamon.PhaseSeven
open LeBrunSalamon.PhaseEight

section AffineContact

variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (θ : AffineOneForm A)

noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseFour
variable {A : Type*} [CommRing A] [Algebra ℂ A]

namespace AffineContactProofCandidate

/-- Multiplication of a derivation by a function has the actual Leibniz correction. -/
theorem derivation_bracket_smul_left (a : A) (V W : AffineVectorFields A) :
    ⁅a • V, W⁆ = a • ⁅V, W⁆ - W a • V := by
  apply Derivation.ext
  intro x
  change a * V (W x) - W (a * V x) =
    a * (V (W x) - W (V x)) - W a * V x
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

/-- The corresponding Leibniz formula in the second argument. -/
theorem derivation_bracket_smul_right (a : A) (V W : AffineVectorFields A) :
    ⁅V, a • W⁆ = V a • W + a • ⁅V, W⁆ := by
  apply Derivation.ext
  intro x
  change V (a * W x) - a * W (V x) =
    V a * W x + a * (V (W x) - W (V x))
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

variable (θ : AffineOneForm A)

theorem affineLevi_self_zero_proved (u : AffineDistribution θ) :
    affineLeviValue θ u u = 0 := by
  change θ ⁅u.1, u.1⁆ = 0
  rw [lie_self, map_zero]

theorem affineLevi_skew_proved (u v : AffineDistribution θ) :
    affineLeviValue θ u v = -affineLeviValue θ v u := by
  change θ ⁅u.1, v.1⁆ = -θ ⁅v.1, u.1⁆
  rw [← lie_skew u.1 v.1, map_neg]

theorem affineLevi_smul_left_proved (a : A) (u v : AffineDistribution θ) :
    affineLeviValue θ (a • u) v = a * affineLeviValue θ u v := by
  have hu : θ u.1 = 0 := u.2
  change θ ⁅a • u.1, v.1⁆ = a * θ ⁅u.1, v.1⁆
  rw [derivation_bracket_smul_left]
  simp only [map_sub, map_smul, hu, smul_zero, sub_zero, smul_eq_mul, mul_zero]

theorem affineLevi_smul_right_proved (a : A) (u v : AffineDistribution θ) :
    affineLeviValue θ u (a • v) = a * affineLeviValue θ u v := by
  have hv : θ v.1 = 0 := v.2
  change θ ⁅u.1, a • v.1⁆ = a * θ ⁅u.1, v.1⁆
  rw [derivation_bracket_smul_right]
  simp only [map_add, map_smul, hv, smul_zero, zero_add, smul_eq_mul, mul_zero]

theorem contactVectorFields_bracket_closed_proved
    (V W : AffineVectorFields A)
    (hV : IsAffineContactVectorField θ V)
    (hW : IsAffineContactVectorField θ W) :
    IsAffineContactVectorField θ ⁅V, W⁆ := by
  intro u
  have hVW : θ ⁅V, ⁅W, u.1⁆⁆ = 0 := hV ⟨⁅W, u.1⁆, hW u⟩
  have hWV : θ ⁅W, ⁅V, u.1⁆⁆ = 0 := hW ⟨⁅V, u.1⁆, hV u⟩
  rw [lie_lie, map_sub, hVW, hWV, sub_self]

end AffineContactProofCandidate

end

/-- The Levi expression `θ([u,v])` is alternating for fields in `ker θ`.
This is true before imposing the contact nondegeneracy condition. -/
theorem affineLevi_self_zero (u : AffineDistribution θ) :
    affineLeviValue θ u u = 0 := by
  exact LeBrunSalamon.PhaseNine.AffineContactProofCandidate.affineLevi_self_zero_proved (A := A) (θ := θ) (u := u)

/-- The Levi expression is skew-symmetric. -/
theorem affineLevi_skew (u v : AffineDistribution θ) :
    affineLeviValue θ u v = -affineLeviValue θ v u := by
  exact LeBrunSalamon.PhaseNine.AffineContactProofCandidate.affineLevi_skew_proved (A := A) (θ := θ) (u := u) (v := v)

/-- The derivative term in `[a u,v]` disappears after applying `θ` to
sections `u,v` of its kernel.  This is the key module-linearity fact. -/
theorem affineLevi_smul_left (a : A) (u v : AffineDistribution θ) :
    affineLeviValue θ (a • u) v = a * affineLeviValue θ u v := by
  exact LeBrunSalamon.PhaseNine.AffineContactProofCandidate.affineLevi_smul_left_proved (A := A) (θ := θ) (a := a) (u := u) (v := v)

/-- Linearity of the Levi expression in its second argument. -/
theorem affineLevi_smul_right (a : A) (u v : AffineDistribution θ) :
    affineLeviValue θ u (a • v) = a * affineLeviValue θ u v := by
  exact LeBrunSalamon.PhaseNine.AffineContactProofCandidate.affineLevi_smul_right_proved (A := A) (θ := θ) (a := a) (u := u) (v := v)

/-- Contact vector fields are closed under their Lie bracket. -/
theorem contactVectorFields_bracket_closed
    (V W : AffineVectorFields A)
    (hV : IsAffineContactVectorField θ V)
    (hW : IsAffineContactVectorField θ W) :
    IsAffineContactVectorField θ ⁅V, W⁆ := by
  exact LeBrunSalamon.PhaseNine.AffineContactProofCandidate.contactVectorFields_bracket_closed_proved (A := A) (θ := θ) (V := V) (W := W) (hV := hV) (hW := hW)

noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseFour
variable {A : Type*} [CommRing A] [Algebra ℂ A]

namespace AffineHamiltonianProofCandidate

/-- The actual Leibniz correction for a function multiple in the second slot. -/
theorem derivation_bracket_smul_right (a : A) (V W : AffineVectorFields A) :
    ⁅V, a • W⁆ = V a • W + a • ⁅V, W⁆ := by
  apply Derivation.ext
  intro x
  change V (a * W x) - a * W (V x) =
    V a * W x + a * (V (W x) - W (V x))
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

/-- Failure of a field to preserve the actual kernel is linear in the kernel section. -/
def affineContactDefect (θ : AffineOneForm A) (V : AffineVectorFields A) :
    AffineDistribution θ →ₗ[A] A where
  toFun u := θ ⁅V, u.1⁆
  map_add' u w := by
    change θ ⁅V, u.1 + w.1⁆ = θ ⁅V, u.1⁆ + θ ⁅V, w.1⁆
    rw [lie_add, map_add]
  map_smul' a u := by
    have hu : θ u.1 = 0 := u.2
    change θ ⁅V, a • u.1⁆ = a • θ ⁅V, u.1⁆
    rw [derivation_bracket_smul_right]
    simp only [map_add, map_smul, hu, smul_zero, zero_add]

variable (θ : AffineOneForm A)

theorem contactHamiltonian_injective_proved
    (hθ : IsAffineContactForm θ)
    (V W : AffineContactVectorFields θ)
    (h : affineHamiltonian θ V.1 = affineHamiltonian θ W.1) :
    V = W := by
  obtain ⟨b, hperfect, hnormalize⟩ := hθ.2
  change θ V.1 = θ W.1 at h
  let u : AffineDistribution θ := ⟨V.1 - W.1, by
    change θ (V.1 - W.1) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr h⟩
  have hb : b u = 0 := by
    apply LinearMap.ext
    intro w
    change b u w = 0
    rw [hnormalize u w]
    change θ ⁅V.1 - W.1, w.1⁆ = 0
    rw [sub_lie, map_sub, V.2 w, W.2 w, sub_self]
  have hu0 : u = 0 := hperfect.2.1 (hb.trans (map_zero b).symm)
  have hvalues : V.1 - W.1 = 0 :=
    congrArg (fun z : AffineDistribution θ => z.1) hu0
  exact Subtype.ext (sub_eq_zero.mp hvalues)

theorem contactHamiltonian_surjective_proved
    (hθ : IsAffineContactForm θ) (f : A) :
    ∃ V : AffineContactVectorFields θ,
      affineHamiltonian θ V.1 = f := by
  obtain ⟨v, hv⟩ := hθ.1 f
  obtain ⟨b, hperfect, hnormalize⟩ := hθ.2
  obtain ⟨q, hq⟩ := hperfect.2.2 (affineContactDefect θ v)
  refine ⟨⟨v - q.1, ?_⟩, ?_⟩
  · intro u
    have hqu : θ ⁅q.1, u.1⁆ = θ ⁅v, u.1⁆ := by
      calc
        θ ⁅q.1, u.1⁆ = b q u := (hnormalize q u).symm
        _ = affineContactDefect θ v u :=
          congrArg (fun l : AffineDistribution θ →ₗ[A] A => l u) hq
        _ = θ ⁅v, u.1⁆ := rfl
    change θ ⁅v - q.1, u.1⁆ = 0
    rw [sub_lie, map_sub, hqu, sub_self]
  · have hq0 : θ q.1 = 0 := q.2
    change θ (v - q.1) = f
    rw [map_sub, hq0, sub_zero, hv]

end AffineHamiltonianProofCandidate

end

/-- On a genuine algebraic contact chart a contact vector field is uniquely determined by its Hamiltonian.
Perfection of the Levi pairing is indispensable in this statement. -/
theorem contactHamiltonian_injective
    (hθ : IsAffineContactForm θ)
    (V W : AffineContactVectorFields θ)
    (h : affineHamiltonian θ V.1 = affineHamiltonian θ W.1) :
    V = W := by
  exact LeBrunSalamon.PhaseNine.AffineHamiltonianProofCandidate.contactHamiltonian_injective_proved (A := A) (θ := θ) (hθ := hθ) (V := V) (W := W) (h := h)

/-- Every regular function on an affine contact chart is the Hamiltonian of a (necessarily unique) contact
vector field. This statement uses the actual surjectivity and perfectness conditions in
`IsAffineContactForm`. It must NOT be assumed for a pre-contact form. -/
theorem contactHamiltonian_surjective
    (hθ : IsAffineContactForm θ) (f : A) :
    ∃ V : AffineContactVectorFields θ,
      affineHamiltonian θ V.1 = f := by
  exact LeBrunSalamon.PhaseNine.AffineHamiltonianProofCandidate.contactHamiltonian_surjective_proved (A := A) (θ := θ) (hθ := hθ) (f := f)

/-- The two preceding lemmas identify affine contact fields with their
Hamiltonians.  This is an equivalence of sets, NOT of A-modules: contact
vector fields are not closed under multiplication by arbitrary functions. -/
noncomputable def contactHamiltonianEquiv
    (hθ : IsAffineContactForm θ) :
    AffineContactVectorFields θ ≃ A :=
  Equiv.ofBijective
    (fun V : AffineContactVectorFields θ => affineHamiltonian θ V.1)
    ⟨(fun V W h => contactHamiltonian_injective θ hθ V W h),
      (fun f => contactHamiltonian_surjective θ hθ f)⟩

/-- The contact (Jacobi) bracket of regular Hamiltonians. Its definition uses the above unique contact
vector field and the actual Lie bracket of derivations. The contact form fixes the normalization. -/
noncomputable def contactJacobiBracket
    (hθ : IsAffineContactForm θ) (f g : A) : A :=
  affineJacobiValue θ
    ((contactHamiltonianEquiv θ hθ).symm f)
    ((contactHamiltonianEquiv θ hθ).symm g)

noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseOne
open LeBrunSalamon.PhaseFour
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (θ : AffineOneForm A)

namespace AffineContactProofCandidate

theorem contactJacobiBracket_skew_proved
    (hθ : IsAffineContactForm θ) (f g : A) :
    contactJacobiBracket θ hθ f g =
      -contactJacobiBracket θ hθ g f := by
  let V : AffineContactVectorFields θ := (contactHamiltonianEquiv θ hθ).symm f
  let W : AffineContactVectorFields θ := (contactHamiltonianEquiv θ hθ).symm g
  change θ ⁅V.1, W.1⁆ = -θ ⁅W.1, V.1⁆
  rw [← lie_skew V.1 W.1, map_neg]

/-- The inverse of the original Hamiltonian equivalence preserves the actual bracket value. -/
theorem contactHamiltonianEquiv_symm_bracket_val
    (hθ : IsAffineContactForm θ) (f g : A) :
    ((contactHamiltonianEquiv θ hθ).symm (contactJacobiBracket θ hθ f g)).1 =
      ⁅((contactHamiltonianEquiv θ hθ).symm f).1,
        ((contactHamiltonianEquiv θ hθ).symm g).1⁆ := by
  let V : AffineContactVectorFields θ := (contactHamiltonianEquiv θ hθ).symm f
  let W : AffineContactVectorFields θ := (contactHamiltonianEquiv θ hθ).symm g
  let B : AffineContactVectorFields θ :=
    ⟨⁅V.1, W.1⁆,
      contactVectorFields_bracket_closed_proved θ V.1 W.1 V.2 W.2⟩
  have hB : contactHamiltonianEquiv θ hθ B = contactJacobiBracket θ hθ f g := rfl
  have hi : (contactHamiltonianEquiv θ hθ).symm
      (contactJacobiBracket θ hθ f g) = B := by
    rw [← hB]
    exact (contactHamiltonianEquiv θ hθ).symm_apply_apply B
  exact congrArg (fun Z : AffineContactVectorFields θ => Z.1) hi

theorem contactJacobiBracket_jacobi_proved
    (hθ : IsAffineContactForm θ) (f g h : A) :
    contactJacobiBracket θ hθ f (contactJacobiBracket θ hθ g h) +
    contactJacobiBracket θ hθ g (contactJacobiBracket θ hθ h f) +
    contactJacobiBracket θ hθ h (contactJacobiBracket θ hθ f g) = 0 := by
  let V : AffineContactVectorFields θ := (contactHamiltonianEquiv θ hθ).symm f
  let W : AffineContactVectorFields θ := (contactHamiltonianEquiv θ hθ).symm g
  let Z : AffineContactVectorFields θ := (contactHamiltonianEquiv θ hθ).symm h
  change
    θ ⁅V.1, ((contactHamiltonianEquiv θ hθ).symm
      (contactJacobiBracket θ hθ g h)).1⁆ +
    θ ⁅W.1, ((contactHamiltonianEquiv θ hθ).symm
      (contactJacobiBracket θ hθ h f)).1⁆ +
    θ ⁅Z.1, ((contactHamiltonianEquiv θ hθ).symm
      (contactJacobiBracket θ hθ f g)).1⁆ = 0
  rw [contactHamiltonianEquiv_symm_bracket_val θ hθ g h,
    contactHamiltonianEquiv_symm_bracket_val θ hθ h f,
    contactHamiltonianEquiv_symm_bracket_val θ hθ f g]
  have hj := congrArg (fun D : AffineVectorFields A => θ D)
    (lie_jacobi V.1 W.1 Z.1)
  simpa only [map_add, map_zero] using hj

end AffineContactProofCandidate

end

/-- The Jacobi bracket is skew-symmetric. -/
theorem contactJacobiBracket_skew
    (hθ : IsAffineContactForm θ) (f g : A) :
    contactJacobiBracket θ hθ f g =
      -contactJacobiBracket θ hθ g f := by
  exact LeBrunSalamon.PhaseNine.AffineContactProofCandidate.contactJacobiBracket_skew_proved (A := A) (θ := θ) (hθ := hθ) (f := f) (g := g)

/-- Jacobi identity for the Jacobi (not Poisson) bracket of contact
Hamiltonians.  Its proof reduces to the Lie bracket of contact fields. -/
theorem contactJacobiBracket_jacobi
    (hθ : IsAffineContactForm θ) (f g h : A) :
    contactJacobiBracket θ hθ f (contactJacobiBracket θ hθ g h) +
    contactJacobiBracket θ hθ g (contactJacobiBracket θ hθ h f) +
    contactJacobiBracket θ hθ h (contactJacobiBracket θ hθ f g) = 0 := by
  exact LeBrunSalamon.PhaseNine.AffineContactProofCandidate.contactJacobiBracket_jacobi_proved (A := A) (θ := θ) (hθ := hθ) (f := f) (g := g) (h := h)

/- Source-only Phase 3 integration: affine_hamiltonian_followups_1. -/
noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseNine
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (θ : AffineOneForm A)

namespace AffineFollowupProofCandidate

theorem inverse_value (hθ : IsAffineContactForm θ) (f : A) :
    θ ((contactHamiltonianEquiv θ hθ).symm f).1 = f := by
  change (contactHamiltonianEquiv θ hθ)
    ((contactHamiltonianEquiv θ hθ).symm f) = f
  exact (contactHamiltonianEquiv θ hθ).apply_symm_apply f

theorem inverse_eq (hθ : IsAffineContactForm θ) (f : A)
    (V : AffineVectorFields A) (hV : IsAffineContactVectorField θ V)
    (hvalue : θ V = f) :
    ((contactHamiltonianEquiv θ hθ).symm f).1 = V := by
  have h : (contactHamiltonianEquiv θ hθ).symm f =
      (⟨V, hV⟩ : AffineContactVectorFields θ) := by
    apply contactHamiltonian_injective θ hθ
    change θ ((contactHamiltonianEquiv θ hθ).symm f).1 = θ V
    exact (inverse_value θ hθ f).trans hvalue.symm
  exact congrArg (fun W : AffineContactVectorFields θ => W.1) h

theorem inverse_zero (hθ : IsAffineContactForm θ) :
    ((contactHamiltonianEquiv θ hθ).symm 0).1 = 0 := by
  apply inverse_eq θ hθ 0 0
  · intro u
    rw [zero_lie, map_zero]
  · exact map_zero θ

theorem inverse_add (hθ : IsAffineContactForm θ) (f g : A) :
    ((contactHamiltonianEquiv θ hθ).symm (f + g)).1 =
      ((contactHamiltonianEquiv θ hθ).symm f).1 +
      ((contactHamiltonianEquiv θ hθ).symm g).1 := by
  apply inverse_eq θ hθ (f + g)
    (((contactHamiltonianEquiv θ hθ).symm f).1 +
      ((contactHamiltonianEquiv θ hθ).symm g).1)
  · intro u
    rw [add_lie, map_add,
      ((contactHamiltonianEquiv θ hθ).symm f).2 u,
      ((contactHamiltonianEquiv θ hθ).symm g).2 u, add_zero]
  · rw [map_add, inverse_value θ hθ f, inverse_value θ hθ g]

theorem inverse_smul (hθ : IsAffineContactForm θ) (c : ℂ) (f : A) :
    ((contactHamiltonianEquiv θ hθ).symm (c • f)).1 =
      c • ((contactHamiltonianEquiv θ hθ).symm f).1 := by
  apply inverse_eq θ hθ (c • f)
    (c • ((contactHamiltonianEquiv θ hθ).symm f).1)
  · intro u
    rw [smul_lie]
    change (θ.restrictScalars ℂ)
      (c • ⁅((contactHamiltonianEquiv θ hθ).symm f).1, u.1⁆) = 0
    rw [map_smul]
    change c • θ ⁅((contactHamiltonianEquiv θ hθ).symm f).1, u.1⁆ = 0
    rw [((contactHamiltonianEquiv θ hθ).symm f).2 u, smul_zero]
  · change (θ.restrictScalars ℂ)
      (c • ((contactHamiltonianEquiv θ hθ).symm f).1) = c • f
    rw [map_smul]
    change c • θ ((contactHamiltonianEquiv θ hθ).symm f).1 = c • f
    rw [inverse_value θ hθ f]

theorem jacobi_action_formula (hθ : IsAffineContactForm θ) (f g : A) :
    contactJacobiBracket θ hθ f g =
      ((contactHamiltonianEquiv θ hθ).symm f).1 g +
        g * contactJacobiBracket θ hθ f 1 := by
  let V : AffineContactVectorFields θ := (contactHamiltonianEquiv θ hθ).symm f
  let W : AffineContactVectorFields θ := (contactHamiltonianEquiv θ hθ).symm g
  let E : AffineContactVectorFields θ := (contactHamiltonianEquiv θ hθ).symm 1
  have hW : θ W.1 = g := inverse_value θ hθ g
  have hE : θ E.1 = 1 := inverse_value θ hθ 1
  let u : AffineDistribution θ := ⟨W.1 - g • E.1, by
    change θ (W.1 - g • E.1) = 0
    rw [map_sub, map_smul, hW, hE]
    simp only [smul_eq_mul, mul_one, sub_self]⟩
  have h := V.2 u
  change θ ⁅V.1, W.1 - g • E.1⁆ = 0 at h
  simp only [lie_sub,
    AffineContactProofCandidate.derivation_bracket_smul_right,
    map_sub, map_add, map_smul, smul_eq_mul, hE, mul_one] at h
  change θ ⁅V.1, W.1⁆ = V.1 g + g * θ ⁅V.1, E.1⁆
  exact sub_eq_zero.mp h

theorem contactJacobiBracket_product_proved
    (hθ : IsAffineContactForm θ) (f g h : A) :
    contactJacobiBracket θ hθ f (g * h) =
      contactJacobiBracket θ hθ f g * h +
      g * contactJacobiBracket θ hθ f h -
      g * h * contactJacobiBracket θ hθ f 1 := by
  rw [jacobi_action_formula θ hθ f (g * h),
    jacobi_action_formula θ hθ f g,
    jacobi_action_formula θ hθ f h]
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

end AffineFollowupProofCandidate
end


/-- The contact bracket is a *Jacobi* bracket, not in general a Poisson bracket. In particular, the
ordinary Leibniz rule has the correction term involving `{f,1}`. -/
theorem contactJacobiBracket_product
    (hθ : IsAffineContactForm θ) (f g h : A) :
    contactJacobiBracket θ hθ f (g * h) =
      contactJacobiBracket θ hθ f g * h +
      g * contactJacobiBracket θ hθ f h -
      g * h * contactJacobiBracket θ hθ f 1 := by
  exact LeBrunSalamon.PhaseNine.AffineFollowupProofCandidate.contactJacobiBracket_product_proved (θ := θ) (hθ := hθ) (f := f) (g := g) (h := h)

end AffineContact

/-! ## 9B. A genuinely nondegenerate linear-algebraic test example -/

noncomputable section
set_option autoImplicit false
open LeBrunSalamon.PhaseEight

namespace StandardContactProof

theorem standardContactLevi_alternating
    (n : ℕ) (u : StandardContactHorizontal n) :
    standardContactLevi n u u = 0 := by
  simp [standardContactLevi]

theorem standardContactLevi_nondegenerate
    (n : ℕ) (u : StandardContactHorizontal n)
    (hu : ∀ v : StandardContactHorizontal n,
      standardContactLevi n u v = 0) :
    u = 0 := by
  apply Prod.ext
  · funext i
    simpa [standardContactLevi, Pi.single_apply, mul_ite] using
      hu (0, Pi.single i 1)
  · funext i
    simpa [standardContactLevi, Pi.single_apply, ite_mul] using
      hu (Pi.single i 1, 0)

theorem standardContactLevi_skew
    (n : ℕ) (u v : StandardContactHorizontal n) :
    standardContactLevi n u v = -standardContactLevi n v u := by
  unfold standardContactLevi
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end StandardContactProof

end

/-- Alternation of the explicit standard symplectic form. -/
theorem standardContactLevi_alternating
    (n : ℕ) (u : StandardContactHorizontal n) :
    standardContactLevi n u u = 0 := by
  exact LeBrunSalamon.PhaseNine.StandardContactProof.standardContactLevi_alternating (n := n) (u := u)

/-- Nondegeneracy, including the zero-dimensional case `n = 0`.
This theorem is a concrete sanity check for the local contact API. -/
theorem standardContactLevi_nondegenerate
    (n : ℕ) (u : StandardContactHorizontal n)
    (hu : ∀ v : StandardContactHorizontal n,
      standardContactLevi n u v = 0) :
    u = 0 := by
  exact LeBrunSalamon.PhaseNine.StandardContactProof.standardContactLevi_nondegenerate (n := n) (u := u) (hu := hu)

/-- The standard form is skew-symmetric. -/
theorem standardContactLevi_skew
    (n : ℕ) (u v : StandardContactHorizontal n) :
    standardContactLevi n u v = -standardContactLevi n v u := by
  exact LeBrunSalamon.PhaseNine.StandardContactProof.standardContactLevi_skew (n := n) (u := u) (v := v)

/-! ## 9C. Statements about rational curves and two-point evaluation -/

/-- Two-point very-free connectedness entails the weaker existence of
rational curves through every ordered pair of complex points.  This is
merely an unpacking of the definitions, not a deep geometry theorem. -/
theorem veryFreeConnected_implies_rationalConnected
    (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d)
    (TX : AlgebraicVectorBundle X.scheme d)
    (h : IsTwoPointVeryFreeConnected P X TX) :
    IsTwoPointRationallyConnected P X := by
  intro x y
  obtain ⟨f, hx, hy⟩ := h x y
  exact ⟨f.marked, hx, hy⟩

/- Source-only Phase 3 integration: closed_point_generation_support. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseSeven

namespace ClosedPointGenerationProof

def complexPointOfClosed {d : ℕ} (X : SmoothProperComplexVariety d)
    (x : X.scheme) (hx : IsClosed {x}) : ComplexPoint X where
  map := AlgebraicGeometry.pointOfClosedPoint X.structureMap x hx
  overC := AlgebraicGeometry.pointOfClosedPoint_comp X.structureMap x hx

theorem complexPointOfClosed_apply {d : ℕ} (X : SmoothProperComplexVariety d)
    (x : X.scheme) (hx : IsClosed {x}) (z : ComplexBase) :
    (complexPointOfClosed X x hx).map z = x :=
  AlgebraicGeometry.pointOfClosedPoint_apply X.structureMap x hx z

theorem open_eq_top_of_complexPoints {d : ℕ} (X : SmoothProperComplexVariety d)
    (U : X.scheme.Opens)
    (hU : ∀ x : ComplexPoint X, x.map (IsLocalRing.closedPoint ℂ) ∈ U) : U = ⊤ := by
  letI : JacobsonSpace X.scheme := LocallyOfFiniteType.jacobsonSpace X.structureMap
  apply eq_top_iff.mpr
  intro x hx
  by_contra hxU
  obtain ⟨y, hyU, hyclosed⟩ := nonempty_inter_closedPoints
    (Z := (U : Set X.scheme)ᶜ) ⟨x, hxU⟩ U.isOpen.isClosed_compl.isLocallyClosed
  have hy := hU (complexPointOfClosed X y hyclosed)
  rw [complexPointOfClosed_apply] at hy
  exact hyU hy

theorem twoPoint_evaluation_surjective (P : ProjectiveLineOverC)
    (E : OModule ProjectiveLine) (h : IsTwoPointGloballyGenerated P E)
    (p : ProjectiveLinePoint P) :
    Function.Surjective (fun a : AlgebraicSection E => restrictSection p.map a) := by
  obtain ⟨a, b, hab⟩ := h.1
  have hq : ∃ q : ProjectiveLinePoint P, p.map ≠ q.map := by
    by_cases hpa : p.map = a.map
    · exact ⟨b, fun hpb => hab (hpa.symm.trans hpb)⟩
    · exact ⟨a, hpa⟩
  obtain ⟨q, hpq⟩ := hq
  intro v
  obtain ⟨s, hs⟩ := h.2 p q hpq (v, 0)
  exact ⟨s, congrArg Prod.fst hs⟩

theorem hom_eq_of_locally_eq {X : Scheme} {E F : OModule X} (a b : E ⟶ F)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ a.over U = b.over U) : a = b := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  change a.app V.unop v = b.app V.unop v
  apply TopCat.Presheaf.IsSheaf.section_ext F.isSheaf
  intro x hxV
  obtain ⟨U, hxU, hU⟩ := h x
  let W := U ⊓ V.unop
  let iU : W ⟶ U := homOfLE inf_le_left
  let iV : W ⟶ V.unop := homOfLE inf_le_right
  refine ⟨W, inf_le_right, ⟨hxU, hxV⟩, ?_⟩
  have he := congrArg
    (fun k : E.over U ⟶ F.over U =>
      k.val.app (op (Over.mk iU)) (E.val.map iV.op v)) hU
  change a.val.app (op W) (E.val.map iV.op v) =
    b.val.app (op W) (E.val.map iV.op v) at he
  change F.val.map iV.op (a.val.app V v) = F.val.map iV.op (b.val.app V v)
  rw [← PresheafOfModules.naturality_apply a.val iV.op v,
    ← PresheafOfModules.naturality_apply b.val iV.op v]
  exact he

theorem globallyGenerated_of_locally_isIso_section {X : Scheme} (E : OModule X)
    (h : ∀ x : X, ∃ (U : X.Opens) (s : AlgebraicSection E),
      x ∈ U ∧ IsIso (s.over U)) : IsGloballyGenerated E := by
  let p : SheafOfModules.free (R := X.ringCatSheaf) (AlgebraicSection E) ⟶ E :=
    Sigma.desc (fun s : AlgebraicSection E => s)
  have hp (s : AlgebraicSection E) : SheafOfModules.ιFree s ≫ p = s :=
    Sigma.ι_comp_desc (fun s : AlgebraicSection E => s) s
  letI : Epi p := ⟨by
    intro F a b hab
    apply hom_eq_of_locally_eq a b
    intro x
    obtain ⟨U, s, hxU, hs⟩ := h x
    letI := hs
    refine ⟨U, hxU, ?_⟩
    apply (cancel_epi (s.over U)).1
    have hsa : s ≫ a = s ≫ b := by
      simpa only [← Category.assoc, hp] using
        congrArg (fun k => SheafOfModules.ιFree s ≫ k) hab
    exact congrArg (fun k => k.over U) hsa⟩
  refine ⟨{ I := AlgebraicSection E, s := E.freeHomEquiv p, epi := ?_ }⟩
  simpa only [Equiv.symm_apply_apply] using (inferInstance : Epi p)

end ClosedPointGenerationProof
end


/- Original veryFree_implies_free is proved later in RecompileTail. -/

end LeBrunSalamon.PhaseNine

end
