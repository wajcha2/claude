import RecompileBasePart01

/-!
# The frozen milestone statement in the project environment

The AuditedStatement block below is copied byte-for-byte from the frozen
`target/MainStatement.lean` (SHA-256
9afe9c5b2e63db17e8f217b71c821eaca83fe26c5cfbc2956fc1b92832d09296).
Its preceding Riemannian core agrees token-for-token with RecompileBasePart01,
which is imported here instead of redeclaring the same constants.

This file states the target and its definitional identities; it does not
assert a proof of the target. No theorem hypotheses have been strengthened.
-/

noncomputable section
set_option autoImplicit false

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

end
