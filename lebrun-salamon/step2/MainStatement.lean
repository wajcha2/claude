import Mathlib

noncomputable section

set_option autoImplicit false

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

end Riemannian
end LeBrunSalamon

namespace LeBrunSalamon.AuditedStatement

open Bundle
open scoped Bundle ContDiff ENNReal

universe u

/-- A closed connected smooth Riemannian `4*n`-manifold, with the
Riemannian distance represented by the ambient extended metric.  The
boundaryless model `LeBrunSalamon.model n` makes "closed" mean compact
without boundary. -/
structure ClosedRiemannianSpace (n : ℕ) where
  carrier : Type u
  [metric : EMetricSpace carrier]
  [charts : ChartedSpace (Model n) carrier]
  [smooth : IsManifold (model n) ∞ carrier]
  [riemannian : RiemannianBundle (fun x : carrier => TangentSpace (model n) x)]
  [smoothMetric : IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (fun x : carrier => TangentSpace (model n) x)]
  [intrinsicDistance : IsRiemannianManifold (model n) carrier]
  [compact : CompactSpace carrier]
  [connected : ConnectedSpace carrier]
  [nonempty : Nonempty carrier]

attribute [instance] ClosedRiemannianSpace.metric ClosedRiemannianSpace.charts
  ClosedRiemannianSpace.smooth ClosedRiemannianSpace.riemannian
  ClosedRiemannianSpace.smoothMetric ClosedRiemannianSpace.intrinsicDistance
  ClosedRiemannianSpace.compact ClosedRiemannianSpace.connected
  ClosedRiemannianSpace.nonempty

/-- A positive constant metric homothety.  The equation says
`f* g_B = scale · g_A`; in particular `scale` multiplies the metric
tensor, not the distance. -/
structure SmoothMetricHomothety {n : ℕ}
    (A B : ClosedRiemannianSpace.{u} n) where
  equivalence : A.carrier ≃ B.carrier
  smooth : ContMDiff (model n) (model n) ∞ equivalence
  smoothInverse : ContMDiff (model n) (model n) ∞ equivalence.symm
  scale : ℝ
  scale_positive : 0 < scale
  metricEquation : ∀ (x : A.carrier) (v w : TangentSpace (model n) x),
    inner ℝ ((mfderiv (model n) (model n) equivalence x) v)
      ((mfderiv (model n) (model n) equivalence x) w) =
      scale * inner ℝ v w

/-- A global geodesic symmetry at a point: an involutive smooth
isometry fixing the point and having differential `-id` there. -/
structure PointSymmetry {n : ℕ}
    (A : ClosedRiemannianSpace.{u} n) (x : A.carrier) where
  isometry : SmoothMetricHomothety.{u} A A
  unitScale : isometry.scale = 1
  fixed : isometry.equivalence x = x
  involutive : Function.Involutive isometry.equivalence
  derivative : ∀ v : TangentSpace (model n) x,
    HEq ((mfderiv (model n) (model n) isometry.equivalence x) v) (-v)

/-- An intrinsic Wolf-space model: a compact connected simply connected
positive quaternionic-Kähler symmetric space of real dimension `4*n`.
This is the geometric class called the Wolf spaces; it is deliberately
not replaced by a bare family label. -/
structure WolfSpaceModel (n : ℕ) where
  space : ClosedRiemannianSpace.{u} n
  positive : IsPositiveQuaternionicKahler n space.carrier
  symmetries : ∀ x : space.carrier, Nonempty (PointSymmetry.{u} space x)
  simplyConnected : SimplyConnectedSpace space.carrier

/-- A homothety from a closed Riemannian space to an actual Wolf-space
model of the same quaternionic dimension. -/
structure WolfHomothety {n : ℕ} (A : ClosedRiemannianSpace.{u} n) where
  target : WolfSpaceModel.{u} n
  map : SmoothMetricHomothety.{u} A target.space

/-- Package an arbitrary manifold carrying the instances used by the
LeBrun--Salamon statement as a closed Riemannian space. -/
def closedRiemannianSpace (n : ℕ) (M : Type u)
    [EMetricSpace M] [ChartedSpace (Model n) M]
    [IsManifold (model n) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
    [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
      (fun x : M => TangentSpace (model n) x)]
    [IsRiemannianManifold (model n) M]
    [CompactSpace M] [ConnectedSpace M] [Nonempty M] :
    ClosedRiemannianSpace.{u} n where
  carrier := M
  metric := inferInstance
  charts := inferInstance
  smooth := inferInstance
  riemannian := inferInstance
  smoothMetric := inferInstance
  intrinsicDistance := inferInstance
  compact := inferInstance
  connected := inferInstance
  nonempty := inferInstance

/-- Exact higher-dimensional Riemannian LeBrun--Salamon statement used
by the pinned manuscript.

For real dimension `4*n ≥ 8`, every closed connected smooth positive
quaternionic-Kähler manifold has parallel Riemann curvature and is
homothetic to a compact symmetric positive quaternionic-Kähler Wolf
space.  The hypothesis is the intrinsic parallel quaternionic
three-plane formulation, equivalent in this dimension range to
holonomy contained in `Sp(n)Sp(1)`.

The four-dimensional convention is intentionally excluded: there the
standard quaternionic-Kähler definition is self-dual Einstein, and the
parallel three-plane formulation alone would not express that condition. -/
def LeBrunSalamonStatement (n : ℕ) (M : Type u)
    [EMetricSpace M] [ChartedSpace (Model n) M]
    [IsManifold (model n) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
    [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
      (fun x : M => TangentSpace (model n) x)]
    [IsRiemannianManifold (model n) M]
    [CompactSpace M] [ConnectedSpace M] [Nonempty M] : Prop :=
  2 ≤ n →
  IsPositiveQuaternionicKahler n M →
    IsLocallyRiemannianSymmetric n M ∧
      Nonempty (WolfHomothety (closedRiemannianSpace n M))

/-- The frozen statement unfolds to the advertised hypotheses and both
conclusions, with no project-specific proof input. -/
theorem leBrunSalamonStatement_iff (n : ℕ) (M : Type u)
    [EMetricSpace M] [ChartedSpace (Model n) M]
    [IsManifold (model n) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
    [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
      (fun x : M => TangentSpace (model n) x)]
    [IsRiemannianManifold (model n) M]
    [CompactSpace M] [ConnectedSpace M] [Nonempty M] :
    LeBrunSalamonStatement n M ↔
      (2 ≤ n →
       IsPositiveQuaternionicKahler n M →
         IsLocallyRiemannianSymmetric n M ∧
           Nonempty (WolfHomothety (closedRiemannianSpace n M))) :=
  Iff.rfl

/-- The new exact statement implies the former exported conclusion.
The converse is deliberately not asserted: parallel curvature alone
omits the Wolf-space homothety. -/
theorem exactStatement_implies_parallelCurvature (n : ℕ) (M : Type u)
    [EMetricSpace M] [ChartedSpace (Model n) M]
    [IsManifold (model n) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
    [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
      (fun x : M => TangentSpace (model n) x)]
    [IsRiemannianManifold (model n) M]
    [CompactSpace M] [ConnectedSpace M] [Nonempty M]
    (h : LeBrunSalamonStatement n M) (hn : 2 ≤ n)
    (hQK : IsPositiveQuaternionicKahler n M) :
    IsLocallyRiemannianSymmetric n M :=
  (h hn hQK).1

end LeBrunSalamon.AuditedStatement
