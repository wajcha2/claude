import RecompileBasePart01

noncomputable section
set_option autoImplicit false
set_option profiler true
set_option stderrAsMessages false
set_option maxErrors 1

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne

universe u

/-!
Read-only planning prototype for OBL057.  All three proposed generic published
inputs are explicit proof parameters.  This file supplies no new admitted
input, does not use the original OBL057 theorem, and grants no acceptance.
Only the composition and actual base-change/type translations are tested.
-/

namespace LeBrunSalamon.Next3i.IntegralityComposition

/-- Literal normal-scheme property of Stacks Definition 28.7.1, tag 033I. -/
def NormalStalks (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
    IsIntegrallyClosed (X.presheaf.stalk x)

/-- The in-particular equivalence of Stacks Lemma 33.7.6, tag 0363. -/
abbrev ConnectedFieldCriterion : Prop :=
  ∀ (K : Type u) [Field K] [IsSepClosed K] (X : Scheme.{u})
    (sX : X ⟶ Spec (CommRingCat.of K)),
    GeometricallyConnected sX ↔ ConnectedSpace X

/-- The normality conclusion for the original field in Stacks 056T. -/
abbrev SmoothNormalCriterion : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u})
    (sX : X ⟶ Spec (CommRingCat.of K)), Smooth sX → NormalStalks X

/-- Stacks Remark 28.7.8, tag 033O, with normality expanded by 033I. -/
abbrev NormalConnectedCriterion : Prop :=
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X],
    NormalStalks X → (IsIntegral X ↔ ConnectedSpace X)

/-- The pinned library has the transport theorem but no registered instance. -/
local instance integralClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u})
      AlgebraicGeometry.IsIntegral :=
  ⟨fun e hX => by
    letI := hX
    exact AlgebraicGeometry.IsIntegral.of_isIso e.hom⟩

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "INTEGRALITY_STAGE ENTER_FIELD_COMPOSITION"
  err.flush

theorem smooth_connected_geometricallyIntegral
    (hconnected : ConnectedFieldCriterion.{u})
    (hnormal : SmoothNormalCriterion.{u})
    (hintegral : NormalConnectedCriterion.{u})
    (K : Type u) [Field K] [IsSepClosed K] (X : Scheme.{u})
    (sX : X ⟶ Spec (CommRingCat.of K)) [Smooth sX] [ConnectedSpace X] :
    GeometricallyIntegral sX := by
  letI : GeometricallyConnected sX := (hconnected K X sX).mpr inferInstance
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := AlgebraicGeometry.IsIntegral) (R := K) (f := sX)).mpr
  intro L _ _
  let g : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  haveI : Smooth (pullback.snd sX g) := inferInstance
  haveI : IsLocallyNoetherian (pullback sX g) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd sX g)
  haveI : ConnectedSpace (pullback sX g : Scheme.{u}) := inferInstance
  exact (hintegral (pullback sX g)
    (hnormal L (pullback sX g) (pullback.snd sX g) inferInstance)).mpr inferInstance

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "INTEGRALITY_STAGE EXIT_FIELD_COMPOSITION"
  err.putStrLn "INTEGRALITY_STAGE ENTER_COMPLEX_SPECIALIZATION"
  err.flush

/-- Same actual geometric hypotheses as original OBL057; three conditional
generic inputs remain explicit and are not asserted by this prototype. -/
theorem complex_specialization
    (hconnected : ConnectedFieldCriterion.{0})
    (hnormal : SmoothNormalCriterion.{0})
    (hintegral : NormalConnectedCriterion.{0})
    {Y : Scheme} (sY : Y ⟶ ComplexBase) [Smooth sY] [ConnectedSpace Y] :
    GeometricallyIntegral sY := by
  exact smooth_connected_geometricallyIntegral hconnected hnormal hintegral ℂ Y sY

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "INTEGRALITY_STAGE EXIT_COMPLEX_SPECIALIZATION"
  err.putStrLn "INTEGRALITY_STAGE ENTER_TARGET_SQUARE"
  err.flush

/-- The exact intrinsic square requires no fourth geometric input. -/
theorem complex_selfProduct_integral
    (hconnected : ConnectedFieldCriterion.{0})
    (hnormal : SmoothNormalCriterion.{0})
    (hintegral : NormalConnectedCriterion.{0})
    {Y : Scheme} (sY : Y ⟶ ComplexBase) [Smooth sY] [ConnectedSpace Y] :
    IsIntegral (pullback sY sY) := by
  letI : GeometricallyIntegral sY :=
    complex_specialization hconnected hnormal hintegral sY
  letI : IsIntegral Y := GeometricallyIntegral.isIntegral_of_subsingleton sY
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  infer_instance

theorem complex_selfProduct_irreducible
    (hconnected : ConnectedFieldCriterion.{0})
    (hnormal : SmoothNormalCriterion.{0})
    (hintegral : NormalConnectedCriterion.{0})
    {Y : Scheme} (sY : Y ⟶ ComplexBase) [Smooth sY] [ConnectedSpace Y] :
    IrreducibleSpace (pullback sY sY : Scheme) := by
  letI : IsIntegral (pullback sY sY) :=
    complex_selfProduct_integral hconnected hnormal hintegral sY
  infer_instance

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "INTEGRALITY_STAGE EXIT_TARGET_SQUARE"
  err.putStrLn "INTEGRALITY_COMPLETE"
  err.flush

#print axioms smooth_connected_geometricallyIntegral
#print axioms complex_specialization
#print axioms complex_selfProduct_integral
#print axioms complex_selfProduct_irreducible

end LeBrunSalamon.Next3i.IntegralityComposition
end
