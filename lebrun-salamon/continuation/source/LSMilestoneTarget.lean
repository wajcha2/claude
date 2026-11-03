import LSCompletedTargets
import LSMilestoneTopology

/-!
# Explicit transport from the constructed metric output to the frozen target

All metric data are transported by field constructors. The old and audited
structures have the same carriers, metrics, smooth structures and metric
scales; no classification or geometric conclusion is inserted by a transport.

The only additional hypothesis in the final conditional theorem is explicitly
named `PositiveQKSimpleConnectedness`. It is the remaining bridge to the
simply-connected target required by the frozen specification. Its mathematical
source is Salamon's simple-connectedness theorem, but the current operational
quaternionic-Kähler predicate must be identified with the published hypothesis
before that theorem may be installed as an allowed input. There is no admitted
constructor for this bridge in this file.
-/

noncomputable section
set_option autoImplicit false

open Bundle
open scoped Bundle ContDiff ENNReal BigOperators

namespace LeBrunSalamon.Milestone

universe u

/-- Copy the existing closed Riemannian data into the audited structure. -/
def toAuditedSpace {n : ℕ} (A : Skeleton.ClosedRiemannianSpace.{u} n) :
    AuditedStatement.ClosedRiemannianSpace.{u} n where
  carrier := A.carrier
  metric := A.metric
  charts := A.charts
  smooth := A.smooth
  riemannian := A.riemannian
  smoothMetric := A.smoothMetric
  intrinsicDistance := A.intrinsicDistance
  compact := A.compact
  connected := A.connected
  nonempty := A.nonempty

/-- The reverse transport, retaining the same metric and smooth structure. -/
def toSkeletonSpace {n : ℕ} (A : AuditedStatement.ClosedRiemannianSpace.{u} n) :
    Skeleton.ClosedRiemannianSpace.{u} n where
  carrier := A.carrier
  metric := A.metric
  charts := A.charts
  smooth := A.smooth
  riemannian := A.riemannian
  smoothMetric := A.smoothMetric
  intrinsicDistance := A.intrinsicDistance
  compact := A.compact
  connected := A.connected
  nonempty := A.nonempty

@[simp] theorem toAuditedSpace_toSkeletonSpace {n : ℕ}
    (A : AuditedStatement.ClosedRiemannianSpace.{u} n) :
    toAuditedSpace (toSkeletonSpace A) = A := by
  cases A
  rfl

@[simp] theorem toSkeletonSpace_toAuditedSpace {n : ℕ}
    (A : Skeleton.ClosedRiemannianSpace.{u} n) :
    toSkeletonSpace (toAuditedSpace A) = A := by
  cases A
  rfl

/-- A metric homothety is unchanged as a function or as a metric equation. -/
def toAuditedHomothety {n : ℕ} {A B : Skeleton.ClosedRiemannianSpace.{u} n}
    (f : Skeleton.SmoothMetricHomothety A B) :
    AuditedStatement.SmoothMetricHomothety (toAuditedSpace A) (toAuditedSpace B) where
  equivalence := f.equivalence
  smooth := f.smooth
  smoothInverse := f.smoothInverse
  scale := f.scale
  scale_positive := f.scale_positive
  metricEquation := f.metricEquation

@[simp] theorem toAuditedHomothety_scale {n : ℕ}
    {A B : Skeleton.ClosedRiemannianSpace.{u} n}
    (f : Skeleton.SmoothMetricHomothety A B) :
    (toAuditedHomothety f).scale = f.scale := rfl

@[simp] theorem toAuditedHomothety_equivalence {n : ℕ}
    {A B : Skeleton.ClosedRiemannianSpace.{u} n}
    (f : Skeleton.SmoothMetricHomothety A B) :
    (toAuditedHomothety f).equivalence = f.equivalence := rfl

/-- Point symmetries retain their actual maps, involutions and derivatives. -/
def toAuditedPointSymmetry {n : ℕ} (A : Skeleton.ClosedRiemannianSpace.{u} n)
    (x : A.carrier) (s : Skeleton.PointSymmetry A x) :
    AuditedStatement.PointSymmetry (toAuditedSpace A) x where
  isometry := toAuditedHomothety s.isometry
  unitScale := s.unitScale
  fixed := s.fixed
  involutive := s.involutive
  derivative := s.derivative

/-- The exact additional field separating the old target from a Wolf model. -/
def toWolfSpaceModel {n : ℕ} (S : Skeleton.SymmetricMetricModel.{u} n)
    (hSC : SimplyConnectedSpace S.space.carrier) :
    AuditedStatement.WolfSpaceModel.{u} n where
  space := toAuditedSpace S.space
  positive := S.positive
  symmetries := fun x =>
    (S.symmetries x).map (toAuditedPointSymmetry S.space x)
  simplyConnected := hSC

/-- Transport the full constructed homothety once simple connectedness is proved. -/
def toWolfHomothety {n : ℕ} {A : Skeleton.ClosedRiemannianSpace.{u} n}
    (S : Skeleton.SymmetricHomothety A)
    (hSC : SimplyConnectedSpace S.target.space.carrier) :
    AuditedStatement.WolfHomothety (toAuditedSpace A) where
  target := toWolfSpaceModel S.target hSC
  map := toAuditedHomothety S.map

@[simp] theorem toWolfHomothety_scale {n : ℕ}
    {A : Skeleton.ClosedRiemannianSpace.{u} n}
    (S : Skeleton.SymmetricHomothety A)
    (hSC : SimplyConnectedSpace S.target.space.carrier) :
    (toWolfHomothety S hSC).map.scale = S.map.scale := rfl

@[simp] theorem toWolfHomothety_target_carrier {n : ℕ}
    {A : Skeleton.ClosedRiemannianSpace.{u} n}
    (S : Skeleton.SymmetricHomothety A)
    (hSC : SimplyConnectedSpace S.target.space.carrier) :
    (toWolfHomothety S hSC).target.space.carrier = S.target.space.carrier := rfl

/-- A named outstanding classical bridge, without any admitted proof.

This is not an extra hypothesis in `AuditedStatement.LeBrunSalamonStatement`.
It is an explicit input to the conditional assembly theorem below. Its proof
requires the exact published simple-connectedness theorem and validation of
the operational quaternionic-Kähler definition. -/
def PositiveQKSimpleConnectedness : Prop :=
  ∀ {n : ℕ} (A : Skeleton.ClosedRiemannianSpace.{u} n),
    2 ≤ n → IsPositiveQuaternionicKahler n A.carrier →
      SimplyConnectedSpace A.carrier

section OriginalHypotheses

variable (n : ℕ) (M : Type u)
variable [EMetricSpace M] [ChartedSpace (Model n) M]
variable [IsManifold (model n) ∞ M]
variable [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
variable [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
  (fun x : M => TangentSpace (model n) x)]
variable [IsRiemannianManifold (model n) M]
variable [CompactSpace M] [ConnectedSpace M] [Nonempty M]

/-- Bundle the original hypotheses without adding any geometric assumption. -/
def positiveQKSpace (hn : 2 ≤ n) (hQK : IsPositiveQuaternionicKahler n M) :
    Skeleton.ClosedPositiveQK.{u} n where
  space := toSkeletonSpace (AuditedStatement.closedRiemannianSpace n M)
  dimensionAtLeastEight := hn
  positive := hQK

/-- Expose the stronger metric output already assembled by the proof source.
The theorem inherits exactly the current project's admitted dependencies. -/
theorem constructed_symmetricHomothety
    (hn : 2 ≤ n) (hQK : IsPositiveQuaternionicKahler n M) :
    Nonempty (Skeleton.SymmetricHomothety
      (toSkeletonSpace (AuditedStatement.closedRiemannianSpace n M))) := by
  exact Construction.project_symmetricHomothety
    Construction.constructedProjectInputs (positiveQKSpace n M hn hQK)

/-- The existing geometric construction leaves exactly source simple
connectedness to obtain the frozen conclusion. The forward implication is
pure topology of the actual homothety; the reverse implication uses the
existing project construction and transports simple connectedness along its
actual smooth equivalence. Neither implication introduces an admission. -/
theorem leBrunSalamonStatement_iff_sourceSimpleConnectedness :
    AuditedStatement.LeBrunSalamonStatement n M ↔
      (2 ≤ n → IsPositiveQuaternionicKahler n M → SimplyConnectedSpace M) := by
  constructor
  · intro h hn hQK
    obtain ⟨H⟩ := (h hn hQK).2
    exact H.source_simplyConnected
  · intro hSC hn hQK
    refine ⟨LeBrunSalamon.leBrunSalamon n M hn hQK, ?_⟩
    obtain ⟨S⟩ := constructed_symmetricHomothety n M hn hQK
    have htarget : SimplyConnectedSpace S.target.space.carrier :=
      (toAuditedHomothety S.map).target_simplyConnected (hSC hn hQK)
    simpa only [toAuditedSpace_toSkeletonSpace] using
      (Nonempty.intro (toWolfHomothety S htarget))

/-- The exact frozen endpoint follows once the outstanding classical
simple-connectedness bridge is discharged. Every data transport is explicit;
the conclusion is the unmodified audited statement. -/
theorem leBrunSalamonStatement_of_simpleConnectedness
    (hSC : PositiveQKSimpleConnectedness.{u}) :
    AuditedStatement.LeBrunSalamonStatement n M := by
  apply (leBrunSalamonStatement_iff_sourceSimpleConnectedness n M).mpr
  intro hn hQK
  exact hSC (toSkeletonSpace (AuditedStatement.closedRiemannianSpace n M)) hn hQK

end OriginalHypotheses
end LeBrunSalamon.Milestone

end

#check LeBrunSalamon.AuditedStatement.LeBrunSalamonStatement
#check LeBrunSalamon.Milestone.constructed_symmetricHomothety
#check LeBrunSalamon.Milestone.leBrunSalamonStatement_iff_sourceSimpleConnectedness
#check LeBrunSalamon.Milestone.leBrunSalamonStatement_of_simpleConnectedness
#print axioms LeBrunSalamon.Milestone.leBrunSalamonStatement_of_simpleConnectedness
