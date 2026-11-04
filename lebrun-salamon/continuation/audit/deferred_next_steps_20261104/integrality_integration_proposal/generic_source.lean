import RecompileBasePart01

/-!
Geometric integrality from three separate generic published inputs.
The field-extension construction, local-Noetherian instances, complex
specialization, and intrinsic self-product consequences are proved below.
No properness, separatedness, quasi-compactness, or projectivity is added.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseThree

universe u

namespace LeBrunSalamon.GeometricIntegrality

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

namespace Proof

/-- The pinned library has the transport theorem but no registered instance. -/
local instance integralClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u})
      AlgebraicGeometry.IsIntegral :=
  ⟨fun e hX => by
    letI := hX
    exact AlgebraicGeometry.IsIntegral.of_isIso e.hom⟩

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

/-- Complex specialization of the conditional composition. -/
theorem complex_specialization
    (hconnected : ConnectedFieldCriterion.{0})
    (hnormal : SmoothNormalCriterion.{0})
    (hintegral : NormalConnectedCriterion.{0})
    {Y : Scheme} (sY : Y ⟶ ComplexBase) [Smooth sY] [ConnectedSpace Y] :
    GeometricallyIntegral sY := by
  exact smooth_connected_geometricallyIntegral hconnected hnormal hintegral ℂ Y sY

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

end Proof

end LeBrunSalamon.GeometricIntegrality

namespace LeBrunSalamon.PublishedInputs.GeometricIntegrality

/-- **Published input (exact):** Stacks Project, Lemma 33.7.6, tag 0363,
its geometric-connectedness equivalence over a separably closed field.
The statement applies to every scheme over that field, with no finiteness,
separatedness, or properness premise.
https://stacks.math.columbia.edu/tag/0363 -/
theorem geometricallyConnected_iff_connected
    (K : Type u) [Field K] [IsSepClosed K] (X : Scheme.{u})
    (sX : X ⟶ Spec (CommRingCat.of K)) :
    GeometricallyConnected sX ↔ ConnectedSpace X := by
  sorry

/-- **Published input (normality consequence):** Stacks Project, Lemma
33.25.4, tag 056T, gives geometric normality for a scheme smooth over a
field, and hence normality over the original field. The conclusion here
is literally Definition 28.7.1, tag 033I: each structure-sheaf stalk is an
integrally closed domain.
https://stacks.math.columbia.edu/tag/056T
https://stacks.math.columbia.edu/tag/033I -/
theorem smooth_normal_stalks
    (K : Type u) [Field K] (X : Scheme.{u})
    (sX : X ⟶ Spec (CommRingCat.of K)) (hX : Smooth sX) :
    ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x) := by
  sorry

/-- **Published input (exact):** Stacks Project, Remark 28.7.8, tag 033O,
using Lemma 28.7.7, tag 033N. Local Noetherianity is retained explicitly;
normality is expanded using Definition 28.7.1, tag 033I. No connectedness
or integrality is assumed in advance of the equivalence.
https://stacks.math.columbia.edu/tag/033O
https://stacks.math.columbia.edu/tag/033N
https://stacks.math.columbia.edu/tag/033I -/
theorem normal_integral_iff_connected
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIntegral X ↔ ConnectedSpace X := by
  sorry

end LeBrunSalamon.PublishedInputs.GeometricIntegrality

namespace LeBrunSalamon.GeometricIntegrality

/-- The generic field-extension composition with the three exact inputs supplied. -/
theorem smooth_connected_geometricallyIntegral
    (K : Type u) [Field K] [IsSepClosed K] (X : Scheme.{u})
    (sX : X ⟶ Spec (CommRingCat.of K)) [Smooth sX] [ConnectedSpace X] :
    GeometricallyIntegral sX := by
  exact Proof.smooth_connected_geometricallyIntegral
    @PublishedInputs.GeometricIntegrality.geometricallyConnected_iff_connected
    @PublishedInputs.GeometricIntegrality.smooth_normal_stalks
    @PublishedInputs.GeometricIntegrality.normal_integral_iff_connected K X sX

/-- The exact geometric hypotheses of original OBL057. -/
theorem complex_specialization
    {Y : Scheme} (sY : Y ⟶ ComplexBase) [Smooth sY] [ConnectedSpace Y] :
    GeometricallyIntegral sY := by
  exact Proof.complex_specialization
    @PublishedInputs.GeometricIntegrality.geometricallyConnected_iff_connected
    @PublishedInputs.GeometricIntegrality.smooth_normal_stalks
    @PublishedInputs.GeometricIntegrality.normal_integral_iff_connected sY

/-- The actual self-product is integral, without a further published input. -/
theorem complex_selfProduct_integral
    {Y : Scheme} (sY : Y ⟶ ComplexBase) [Smooth sY] [ConnectedSpace Y] :
    IsIntegral (SelfProduct sY) := by
  exact Proof.complex_selfProduct_integral
    @PublishedInputs.GeometricIntegrality.geometricallyConnected_iff_connected
    @PublishedInputs.GeometricIntegrality.smooth_normal_stalks
    @PublishedInputs.GeometricIntegrality.normal_integral_iff_connected sY

/-- Stable target-square API for the actual two-point evaluation argument. -/
theorem complex_selfProduct_irreducible
    {Y : Scheme} (sY : Y ⟶ ComplexBase) [Smooth sY] [ConnectedSpace Y] :
    IrreducibleSpace (SelfProduct sY : Scheme) := by
  exact Proof.complex_selfProduct_irreducible
    @PublishedInputs.GeometricIntegrality.geometricallyConnected_iff_connected
    @PublishedInputs.GeometricIntegrality.smooth_normal_stalks
    @PublishedInputs.GeometricIntegrality.normal_integral_iff_connected sY

end LeBrunSalamon.GeometricIntegrality
end
