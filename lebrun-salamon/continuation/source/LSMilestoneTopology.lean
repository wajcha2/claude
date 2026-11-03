import LSMilestoneStatement

/-!
# Topological consequences of the actual metric homothety

The frozen homothety data already contain a smooth equivalence and smooth
inverse. They therefore give an actual homeomorphism, and mathlib's homotopy
equivalence API transports simple connectedness in both directions. These
proofs do not use quaternionic geometry, classification, or a published-input
admission. In particular, the frozen Wolf-homothety conclusion already forces
the source to be simply connected; adding that fact to the source hypotheses
would change the target theorem.
-/

noncomputable section
set_option autoImplicit false

open Bundle
open scoped Bundle ContDiff

namespace LeBrunSalamon.AuditedStatement

universe u

namespace SmoothMetricHomothety

/-- The frozen smooth equivalence is an actual mathlib diffeomorphism. -/
def toDiffeomorph {n : ℕ} {A B : ClosedRiemannianSpace.{u} n}
    (f : SmoothMetricHomothety A B) :
    Diffeomorph (model n) (model n) A.carrier B.carrier ∞ where
  toEquiv := f.equivalence
  contMDiff_toFun := f.smooth
  contMDiff_invFun := f.smoothInverse

/-- The homeomorphism carried by a metric homothety uses its actual maps. -/
def toHomeomorph {n : ℕ} {A B : ClosedRiemannianSpace.{u} n}
    (f : SmoothMetricHomothety A B) : A.carrier ≃ₜ B.carrier :=
  f.toDiffeomorph.toHomeomorph

@[simp] theorem toHomeomorph_apply {n : ℕ}
    {A B : ClosedRiemannianSpace.{u} n}
    (f : SmoothMetricHomothety A B) (x : A.carrier) :
    f.toHomeomorph x = f.equivalence x := rfl

@[simp] theorem toHomeomorph_symm_apply {n : ℕ}
    {A B : ClosedRiemannianSpace.{u} n}
    (f : SmoothMetricHomothety A B) (y : B.carrier) :
    f.toHomeomorph.symm y = f.equivalence.symm y := rfl

/-- A smooth metric homothety preserves simple connectedness in both directions. -/
theorem simplyConnectedSpace_iff {n : ℕ}
    {A B : ClosedRiemannianSpace.{u} n}
    (f : SmoothMetricHomothety A B) :
    SimplyConnectedSpace A.carrier ↔ SimplyConnectedSpace B.carrier :=
  f.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace_iff

theorem source_simplyConnected {n : ℕ}
    {A B : ClosedRiemannianSpace.{u} n}
    (f : SmoothMetricHomothety A B)
    (hB : SimplyConnectedSpace B.carrier) : SimplyConnectedSpace A.carrier :=
  f.simplyConnectedSpace_iff.mpr hB

theorem target_simplyConnected {n : ℕ}
    {A B : ClosedRiemannianSpace.{u} n}
    (f : SmoothMetricHomothety A B)
    (hA : SimplyConnectedSpace A.carrier) : SimplyConnectedSpace B.carrier :=
  f.simplyConnectedSpace_iff.mp hA

end SmoothMetricHomothety

/-- A point symmetry is an involution of the actual underlying topological space. -/
theorem PointSymmetry.homeomorph_involutive {n : ℕ}
    {A : ClosedRiemannianSpace.{u} n} {x : A.carrier} (s : PointSymmetry A x) :
    Function.Involutive s.isometry.toHomeomorph :=
  s.involutive

/-- The differential of the point symmetry preserves the actual tangent metric
at every point, by the recorded unit scale; no new notion of isometry is used. -/
theorem PointSymmetry.inner_mfderiv {n : ℕ}
    {A : ClosedRiemannianSpace.{u} n} {x : A.carrier} (s : PointSymmetry A x)
    (y : A.carrier) (v w : TangentSpace (model n) y) :
    inner ℝ ((mfderiv (model n) (model n) s.isometry.equivalence y) v)
      ((mfderiv (model n) (model n) s.isometry.equivalence y) w) = inner ℝ v w := by
  simpa only [s.unitScale, one_mul] using s.isometry.metricEquation y v w

/-- The frozen Wolf-homothety conclusion implies simple connectedness of its source. -/
theorem WolfHomothety.source_simplyConnected {n : ℕ}
    {A : ClosedRiemannianSpace.{u} n} (H : WolfHomothety A) :
    SimplyConnectedSpace A.carrier :=
  H.map.source_simplyConnected H.target.simplyConnected

end LeBrunSalamon.AuditedStatement

end

#check LeBrunSalamon.AuditedStatement.SmoothMetricHomothety.simplyConnectedSpace_iff
#print axioms LeBrunSalamon.AuditedStatement.WolfHomothety.source_simplyConnected
