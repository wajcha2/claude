import LSTangentComparison
import LSContactVelocityTarget

/-!
## The actual Hom velocity value is the original df-vector

The regular velocity map was built from the first jet of the original
universal family. Here its value at the parameter of a fixed free line is
identified with the canonical chart evaluation of the original node
differential on the normalized nonzero source vector. The proof compares
actual family maps over Spec(C), then their coefficients on actual local
target functions. Contact-plane membership is a consequence of original
contact tangency, not a range hypothesis on a replacement map.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirty
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.HomVelocityValue

open FamilyVariation LocalVelocityComparison SourceTangent IntrinsicTangent

/-- Read an actual scheme point of the affine tangent scheme through the
canonical Γ–Spec map and the original representing-algebra equivalence. -/
def tangentValue {A : Type} [CommRing A] [Algebra ℂ A] (p : A →ₐ[ℂ] ℂ)
    (q : ComplexBase ⟶ AffineVelocity.tangentScheme p)
    (hq : q ≫ AffineVelocity.tangentSchemeToC p = 𝟙 ComplexBase) :
    Infinitesimal.Tangent A p :=
  AffineVelocity.tangentPointEquiv p (GlobalVelocity.specPoint q hq)

theorem tangentValue_coordinate {A : Type} [CommRing A] [Algebra ℂ A]
    (p : A →ₐ[ℂ] ℂ) (q : ComplexBase ⟶ AffineVelocity.tangentScheme p)
    (hq : q ≫ AffineVelocity.tangentSchemeToC p = 𝟙 ComplexBase) (a : A) :
    (tangentValue p q hq).val a =
      baseScalar (q.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (AffineVelocity.CoordinateRing p))).inv
          (AffineVelocity.coordinate p a))) := rfl

/-- This comparison depends on the actual scheme map, not its chosen
proof of the over-C equation. -/
theorem tangentValue_congr {A : Type} [CommRing A] [Algebra ℂ A]
    (p : A →ₐ[ℂ] ℂ) {q r : ComplexBase ⟶ AffineVelocity.tangentScheme p}
    (hq : q ≫ AffineVelocity.tangentSchemeToC p = 𝟙 ComplexBase)
    (hr : r ≫ AffineVelocity.tangentSchemeToC p = 𝟙 ComplexBase)
    (h : q = r) : tangentValue p q hq = tangentValue p r hr := by
  subst r
  rfl

/-- Retain the exact central map convention used by the existing global
velocity construction. Only an identity-composition equality is transported. -/
def pointFamily {d : ℕ} {X : SmoothProperComplexVariety d} {x : ComplexPoint X}
    (τ : Infinitesimal.PointLift X.scheme X.structureMap ⟨x.map, x.overC⟩) :
    Deformation (𝟙 ComplexBase) X.structureMap ((𝟙 ComplexBase) ≫ x.map) :=
  GlobalVelocity.recenter (pointDeformation τ) (Category.id_comp x.map).symm

/-- The velocity value of an actual infinitesimal target point. -/
def pointValue {d : ℕ} {X : SmoothProperComplexVariety d} {x : ComplexPoint X}
    (C : GlobalVelocity.TargetChart X x)
    (τ : Infinitesimal.PointLift X.scheme X.structureMap ⟨x.map, x.overC⟩) :
    Infinitesimal.Tangent C.Ring C.evaluation :=
  tangentValue C.evaluation (C.velocity (pointFamily τ)) (C.velocity_overC (pointFamily τ))

/-- Each coordinate is the actual local source-jet derivative. The chart
function is the inverse of the open immersion's genuine function map. -/
theorem pointValue_coordinate {d : ℕ} {X : SmoothProperComplexVariety d}
    {x : ComplexPoint X} (C : GlobalVelocity.TargetChart X x)
    (τ : Infinitesimal.PointLift X.scheme X.structureMap ⟨x.map, x.overC⟩)
    (hτ : ⊤ ≤ τ.map ⁻¹ᵁ chartOpen C) (a : C.Ring) :
    (pointValue C τ).val a =
      derivativeAlong τ.map τ.overC (chartOpen C) hτ (chartFunctions C a) := by
  rw [pointValue, tangentValue_coordinate]
  conv_lhs => rw [← chartFunctions_coordinate C a]
  rw [C.velocity_original_localFunction]
  change baseScalar (GlobalVelocity.localCoefficient (pointDeformation τ)
      (chartOpen C) (chartOpen_point C) (chartFunctions C a)) = _
  rw [GlobalVelocity.localCoefficient_onFunction]
  exact pointDeformation_onFunction τ (chartOpen C) (chartOpen_point C) hτ (chartFunctions C a)

/-- The represented affine value of an actual infinitesimal point is
precisely the canonical evaluation of its original tangent-fiber vector. -/
theorem pointValue_eq_chartEvaluation {d : ℕ} {X : SmoothProperComplexVariety d}
    {x : ComplexPoint X} (C : GlobalVelocity.TargetChart X x)
    (τ : Infinitesimal.PointLift X.scheme X.structureMap ⟨x.map, x.overC⟩) :
    pointValue C τ = chartEvaluation C (pointVector X x τ) := by
  have hτ : ⊤ ≤ τ.map ⁻¹ᵁ chartOpen C := by
    apply pointLift_top_le_preimage τ
    rintro _ ⟨c, rfl⟩
    exact chartOpen_point C trivial
  apply Subtype.ext
  ext a
  rw [pointValue_coordinate C τ hτ a, chartEvaluation_apply]
  exact (pointVector_local_pairing X x τ (chartOpen C) (chartOpen_point C) hτ
    (chartFunctions C a)).symm

section ActualFamily

variable {d : ℕ} {X : SmoothProperComplexVariety d}
variable (H : HomSpacePresentation P X) (x : ComplexPoint X)

/-- The exact source first jet used by the fixed-node velocity map,
composed with the actual curve represented by a complex Hom point. -/
def targetLift
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x)) :
    Infinitesimal.PointLift X.scheme X.structureMap ⟨x.map, x.overC⟩ :=
  Charts.AffineTangentLift.push (HomDeformation.curveAt P H marking x t)
    (HomDeformation.curveAt_overC P H marking x t)
    (HomDeformation.curveAt_marking P H marking x t)
    (PolynomialSourceLift.atMarking marking)

/-- The global first-jet family restricted to a complex parameter point
is exactly the point family of the original curve's source lift. -/
theorem firstJet_atPoint
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x)) :
    GlobalVelocity.recenter
      ((HomFirstJet.deformation P marking H x (PolynomialSourceLift.atMarking marking)).pullback
        t.val t.property) (by rw [← Category.assoc, t.property]) =
      pointFamily (targetLift H x t) := by
  apply Deformation.ext
  exact HomFirstJet.deformation_atPoint P marking H x
    (PolynomialSourceLift.atMarking marking) t

/-- The value is read from the actual global velocity scheme morphism. -/
def value (C : GlobalVelocity.TargetChart X x)
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x)) :
    Infinitesimal.Tangent C.Ring C.evaluation :=
  tangentValue C.evaluation
    (t.val ≫ GlobalVelocity.homVelocity P marking H x (PolynomialSourceLift.atMarking marking) C)
    (by rw [Category.assoc, GlobalVelocity.homVelocity_overC, t.property])

/-- The entire original global scheme map is used in this scalar formula. -/
theorem value_coordinate (C : GlobalVelocity.TargetChart X x)
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x))
    (a : C.Ring) :
    (value H x C t).val a =
      baseScalar (t.val.appTop
        ((GlobalVelocity.homVelocity P marking H x (PolynomialSourceLift.atMarking marking) C).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (AffineVelocity.CoordinateRing C.evaluation))).inv
            (AffineVelocity.coordinate C.evaluation a)))) := rfl

/-- Parameter restriction identifies two actual scheme maps before any
coordinates are taken. -/
theorem value_eq_pointValue (C : GlobalVelocity.TargetChart X x)
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x)) :
    value H x C t = pointValue C (targetLift H x t) := by
  apply tangentValue_congr
  rw [GlobalVelocity.homVelocity_parameterChange, firstJet_atPoint]

/-- At every actual Hom point the represented velocity is the canonical
chart evaluation of the actual original tangent vector of the source jet. -/
theorem value_eq_chartEvaluation (C : GlobalVelocity.TargetChart X x)
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x)) :
    value H x C t = chartEvaluation C (pointVector X x (targetLift H x t)) := by
  rw [value_eq_pointValue, pointValue_eq_chartEvaluation]

end ActualFamily

section FreeLines

variable {n : ℕ} {X : ContactFanoManifold n}
variable (H : HomSpacePresentation P X.variety) (f : FreeLine X)
variable (x : ComplexPoint X.variety) (hx : marking.map ≫ f.curve.map = x.map)
variable (C : GlobalVelocity.TargetChart X.variety x)

/-- The full Hom universal property recovers the given free line itself,
so its target lift is the actual source lift followed by that same curve. -/
theorem targetLift_fixedCenter :
    targetLift H x (HomDeformation.fixedCenter P H marking x
      f.curve.map f.curve.overC hx) =
      Charts.AffineTangentLift.push f.curve.map f.curve.overC hx
        (PolynomialSourceLift.atMarking marking) := by
  unfold targetLift
  simp only [HomDeformation.curveAt_fixedCenter]

/-- Main normalization: the actual global velocity at the fixed free line
is the canonical chart image of the ORIGINAL node differential applied to
the normalized nonzero original source tangent vector. -/
theorem value_fixedCenter :
    value H x C (HomDeformation.fixedCenter P H marking x
      f.curve.map f.curve.overC hx) =
      chartEvaluation C (nodeDifferential f x hx (sourceVector marking)) := by
  rw [value_eq_chartEvaluation, targetLift_fixedCenter,
    ← nodeDifferential_sourceVector_eq_pointVector]

/-- Pointwise contact containment for the actual velocity scheme morphism.
The canonical chart image of the original contact plane is the target;
no surjectivity onto the full tangent space is claimed. -/
theorem value_fixedCenter_mem_contactImage :
    value H x C (HomDeformation.fixedCenter P H marking x
      f.curve.map f.curve.overC hx) ∈
      (contactPlane X x).map (chartEvaluation C) := by
  rw [value_fixedCenter]
  exact Submodule.mem_map.mpr
    ⟨nodeDifferential f x hx (sourceVector marking),
      nodeDifferential_mem_contactPlane f x hx (sourceVector marking), rfl⟩

/-- A parameter point identified by its actual universal curve inherits
the same normalization. Only its represented curve, not a desired velocity
or tangent-space equality, appears in the premise. -/
theorem value_eq_of_curveAt
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x))
    (ht : HomDeformation.curveAt P H marking x t = f.curve.map) :
    value H x C t = chartEvaluation C (nodeDifferential f x hx (sourceVector marking)) := by
  rw [value_eq_chartEvaluation]
  have hl : targetLift H x t =
      Charts.AffineTangentLift.push f.curve.map f.curve.overC hx
        (PolynomialSourceLift.atMarking marking) := by
    unfold targetLift
    simp only [ht]
  rw [hl, ← nodeDifferential_sourceVector_eq_pointVector]

/-- The actual velocity at any parameter point representing this free
line belongs to the original contact-plane image. -/
theorem value_mem_contactImage_of_curveAt
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x))
    (ht : HomDeformation.curveAt P H marking x t = f.curve.map) :
    value H x C t ∈ (contactPlane X x).map (chartEvaluation C) := by
  have hx : marking.map ≫ f.curve.map = x.map := by
    simpa only [ht] using (HomDeformation.curveAt_marking P H marking x t)
  rw [value_eq_of_curveAt H f x hx C t ht]
  exact Submodule.mem_map.mpr
    ⟨nodeDifferential f x hx (sourceVector marking),
      nodeDifferential_mem_contactPlane f x hx (sourceVector marking), rfl⟩

end FreeLines

end LeBrunSalamon.Construction.Lines.HomVelocityValue

end

/-!
## The actual velocity differential has the original positive range

This is the comparison in the final paragraph of `lines:suitable-pair`.
The two mixed derivatives are already identified on actual local functions.
The canonical fiber comparison now transports that scalar identity to the
ORIGINAL tangent fiber and its ORIGINAL positive node subspace. The source
direction is the explicitly normalized polynomial lift at the actual marking.
The parameter may be any actual affine scheme mapping to fixed-node Hom.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.P1Charts

namespace LeBrunSalamon.Construction.Lines.IntrinsicVelocityRange

open FamilyVariation LocalVelocityComparison PositiveVelocityPairing

section PointwisePositiveVector

variable {n : ℕ} {X : ContactFanoManifold n}
variable (H : HomSpacePresentation P X.variety) (f : FreeLine X)
variable (x : ComplexPoint X.variety) (hx : marking.map ≫ f.curve.map = x.map)

/-- The actual derivative of the node-zero positive variation, first
included into the original pulled-back tangent bundle and then transported
to the original target fiber. -/
def positiveVector (v : HomDeformation.FixedLineLift H f x hx) :
    TangentFiber X.variety x :=
  PositiveFrame.nodeSectionDerivative f x hx
    (PolynomialSourceLift.markingChart marking).index
    (PolynomialSourceLift.markingChart marking).coordinate
    (PolynomialSourceLift.markingChart marking).identifies
    (PolynomialSourceLift.derivation (PolynomialSourceLift.markingChart marking).coordinate)
    (HomDeformation.fixedLineVariation H f x hx v)

theorem positiveVector_mem (v : HomDeformation.FixedLineLift H f x hx) :
    positiveVector H f x hx v ∈ positiveNodeSpace f x hx :=
  PositiveFrame.fixedLineVariation_derivative_mem H f x hx
    (PolynomialSourceLift.markingChart marking).index
    (PolynomialSourceLift.markingChart marking).coordinate
    (PolynomialSourceLift.markingChart marking).identifies
    (PolynomialSourceLift.derivation (PolynomialSourceLift.markingChart marking).coordinate) v

/-- The same vector in terms of the actual positive fiber inclusion.
The equality follows from the zero value of the original variation. -/
theorem positiveVector_inclusion (v : HomDeformation.FixedLineLift H f x hx) :
    positiveVector H f x hx v =
      fiberComposition f.curve.map marking.map x.map hx
        (tangentSheaf X.variety.structureMap)
        (fiberMap (PositivePart.freeLinePositiveInclusion f) marking.map
          (PositiveFrame.positiveDerivative f
            (PolynomialSourceLift.markingChart marking).index
            (PolynomialSourceLift.markingChart marking).coordinate
            (PolynomialSourceLift.markingChart marking).identifies
            (PolynomialSourceLift.derivation
              (PolynomialSourceLift.markingChart marking).coordinate)
            (HomDeformation.fixedLinePositiveVariation H f x hx v))) := by
  unfold positiveVector PositiveFrame.nodeSectionDerivative
  change fiberComposition f.curve.map marking.map x.map hx
      (tangentSheaf X.variety.structureMap)
      (PositiveFrame.ambientDerivative f _ _ _ _
        (HomDeformation.fixedLineVariation H f x hx v)) = _
  rw [← HomDeformation.fixedLinePositiveVariation_inclusion H f x hx v,
    PositiveFrame.positiveDerivative_inclusion]
  exact HomDeformation.fixedLinePositiveVariation_node_zero H f x hx v

include hx in
/-- The center lies in the preimage of every actual target neighborhood. -/
theorem marking_preimage (V : X.variety.scheme.Opens) (hV : Set.range x.map ⊆ V) :
    ⊤ ≤ marking.map ⁻¹ᵁ (f.curve.map ⁻¹ᵁ V) := by
  intro z _
  have hz := congrArg (fun k : ComplexBase ⟶ X.variety.scheme => k z) hx
  change f.curve.map (marking.map z) ∈ V
  rw [show f.curve.map (marking.map z) = x.map z from hz]
  exact hV ⟨z, rfl⟩

/-- The mixed scalar pairing in the previous checkpoint is exactly the
evaluation of the actual original tangent vector on da. -/
theorem positiveVector_localAction
    (v : HomDeformation.FixedLineLift H f x hx)
    (V : X.variety.scheme.Opens) (hV : Set.range x.map ⊆ V)
    (hxV : ⊤ ≤ x.map ⁻¹ᵁ V) (a : RingSections X.variety.scheme V)
    (U : ProjectiveLine.Opens) (hUV : U ≤ f.curve.map ⁻¹ᵁ V)
    (hmark : ⊤ ≤ marking.map ⁻¹ᵁ U) :
    IntrinsicTangent.localAction X.variety.structureMap x.map V hxV a
        (positiveVector H f x hx v) =
      PositiveFrame.localScalarPairing marking.map (positiveEvaluation f) U hmark
        (localDifferential f V a U hUV)
        (PositiveFrame.positiveDerivative f
          (PolynomialSourceLift.markingChart marking).index
          (PolynomialSourceLift.markingChart marking).coordinate
          (PolynomialSourceLift.markingChart marking).identifies
          (PolynomialSourceLift.derivation
            (PolynomialSourceLift.markingChart marking).coordinate)
          (HomDeformation.fixedLinePositiveVariation H f x hx v)) := by
  rw [positiveVector_inclusion]
  unfold IntrinsicTangent.localAction
  rw [SourceTangent.localScalarPairing_composition f.curve.map marking.map x.map hx
    (dualEvaluation (cotangentSheaf X.variety.structureMap)) V
    (marking_preimage f x hx V hV) hxV]
  have hp := SourceTangent.localScalarPairing_precompose marking.map
    (pulledEvaluation f.curve.map X.variety.structureMap)
    (PositivePart.freeLinePositiveInclusion f)
    (𝟙 (pullbackModule f.curve.map (cotangentSheaf X.variety.structureMap)))
    (f.curve.map ⁻¹ᵁ V) (marking_preimage f x hx V hV)
    (pullLocalSection f.curve.map (cotangentSheaf X.variety.structureMap) V
      ((cotangentPresentation X.variety.structureMap).differential.apply V a))
    (PositiveFrame.positiveDerivative f
      (PolynomialSourceLift.markingChart marking).index
      (PolynomialSourceLift.markingChart marking).coordinate
      (PolynomialSourceLift.markingChart marking).identifies
      (PolynomialSourceLift.derivation (PolynomialSourceLift.markingChart marking).coordinate)
      (HomDeformation.fixedLinePositiveVariation H f x hx v))
  change PositiveFrame.localScalarPairing marking.map (positiveEvaluation f)
    (f.curve.map ⁻¹ᵁ V) (marking_preimage f x hx V hV) _ _ = _ at hp
  simp only [Scheme.Modules.Hom.id_app, AddCommGrpCat.id_apply] at hp
  dsimp only [pulledEvaluation] at hp
  exact hp.symm.trans
    (SourceTangent.localScalarPairing_restrict marking.map (positiveEvaluation f)
      hUV hmark (marking_preimage f x hx V hV)
      (pullLocalSection f.curve.map (cotangentSheaf X.variety.structureMap) V
        ((cotangentPresentation X.variety.structureMap).differential.apply V a)) _).symm

/-- A genuine common open for the source frame and target function is
constructed as their intersection; it is not an additional geometric input. -/
def commonOpen (V : X.variety.scheme.Opens) : ProjectiveLine.Opens :=
  chartOpen (PolynomialSourceLift.markingChart marking).index ⊓ f.curve.map ⁻¹ᵁ V

include hx in
theorem commonOpen_marking (V : X.variety.scheme.Opens)
    (hV : Set.range x.map ⊆ V) : ⊤ ≤ marking.map ⁻¹ᵁ commonOpen f V := by
  have hc : ⊤ ≤ marking.map ⁻¹ᵁ
      chartOpen (PolynomialSourceLift.markingChart marking).index := by
    rw [← (PolynomialSourceLift.markingChart marking).identifies]
    exact PolynomialSourceLift.point_top_le_chart (PolynomialSourceLift.markingChart marking).index
      (PolynomialSourceLift.markingChart marking).coordinate
  intro z hz
  exact ⟨hc hz, marking_preimage f x hx V hV hz⟩

/-- The actual mixed parameter derivative equals the original tangent
vector on every local target function around x. This removes the unresolved
fiber-normalization premise from the preceding scalar theorem. -/
theorem mixedDerivative_original_fiber
    (v : HomDeformation.FixedLineLift H f x hx)
    (V : X.variety.scheme.Opens) (hV : Set.range x.map ⊆ V)
    (hxV : ⊤ ≤ x.map ⁻¹ᵁ V) (a : RingSections X.variety.scheme V) :
    derivativeAlong v.map v.overC
        ((FixedNodeHom.toC P marking H x ≫ x.map) ⁻¹ᵁ V)
        (parameterLift_top_le_preimage v x.map V hV)
        ((HomFirstJet.deformation P marking H x
          (PolynomialSourceLift.atMarking marking)).onFunction V a) =
      IntrinsicTangent.localAction X.variety.structureMap x.map V hxV a
        (positiveVector H f x hx v) := by
  rw [mixedDerivative_positive_fiber_pairing H f x hx v V hV a
    (commonOpen f V) inf_le_left inf_le_right (commonOpen_marking f x hx V hV)]
  exact (positiveVector_localAction H f x hx v V hV hxV a (commonOpen f V)
    inf_le_right (commonOpen_marking f x hx V hV)).symm

end PointwisePositiveVector

section ActualSchemeDifferential

variable {R : Type} [CommRing R] [Algebra ℂ R]

/-- The comorphism of a genuine map from a pointed affine scheme to
Spec(R), with its scalar structure proved from the original base equation. -/
def schemeComorphism (A : Charts.PointedAffine)
    (g : A.scheme ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ DirectionCones.affineBaseMap R = A.toC) : R →ₐ[ℂ] A.Ring where
  toRingHom := g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  commutes' := by
    intro c
    change g.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (algebraMap ℂ R c)) =
      complexConstants A.toC c
    rw [GlobalVelocity.specFunction_constant]
    exact complexConstants_naturality g A.toC (DirectionCones.affineBaseMap R) hg c

theorem schemeComorphism_apply (A : Charts.PointedAffine)
    (g : A.scheme ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ DirectionCones.affineBaseMap R = A.toC) (a : R) :
    schemeComorphism A g hg a =
      g.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) := rfl

/-- The normalized affine source lift computes the differential of the
actual composite map on every global target function. -/
theorem affineLift_composite_derivative {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (A : Charts.PointedAffine) (g : A.scheme ⟶ Y)
    (hg : g ≫ sY = A.toC) (D : A.Tangent) (a : RingSections Y ⊤) :
    derivativeAlong ((Charts.AffineTangentLift.lift A D).map ≫ g)
        (by rw [Category.assoc, hg]; exact (Charts.AffineTangentLift.lift A D).overC)
        ⊤ (by simp) a = D.val (g.appTop a) := by
  have hm := Scheme.Hom.comp_appLE
    (Charts.AffineTangentLift.lift A D).map g ⊤ ⊤ (by simp)
  have hv := congrArg
    (fun k : Γ(Y, ⊤) ⟶ Γ(Infinitesimal.DualScheme, ⊤) =>
      MixedJet.dualCoefficient (DualMixedBridge.dualGlobalEquiv (k a))) hm
  exact hv.trans (derivativeAlong_affineLift A D (g.appTop a))

end ActualSchemeDifferential

section ParameterDifferential

variable {n : ℕ} {X : ContactFanoManifold n}
variable (H : HomSpacePresentation P X.variety)
variable (x : ComplexPoint X.variety)
variable (C : GlobalVelocity.TargetChart X.variety x)
variable (A : Charts.PointedAffine)
variable (g : PointsOver A.scheme A.toC
  (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x))

/-- The map being differentiated is the previously constructed GLOBAL
velocity morphism, restricted along the actual parameter chart. -/
def chartVelocity : A.scheme ⟶ AffineVelocity.tangentScheme C.evaluation :=
  g.val ≫ GlobalVelocity.homVelocity P marking H x
    (PolynomialSourceLift.atMarking marking) C

theorem chartVelocity_overC :
    chartVelocity H x C A g ≫ AffineVelocity.tangentSchemeToC C.evaluation = A.toC := by
  rw [chartVelocity, Category.assoc, GlobalVelocity.homVelocity_overC]
  exact g.property

def velocityFunctions : AffineVelocity.CoordinateRing C.evaluation →ₐ[ℂ] A.Ring :=
  schemeComorphism A (chartVelocity H x C A g) (chartVelocity_overC H x C A g)

/-- The actual affine scheme differential followed by the canonical
tangent trivialization of the represented vector space. -/
def parameterDifferential : A.Tangent →ₗ[ℂ] Infinitesimal.Tangent C.Ring C.evaluation :=
  (AffineVelocity.tangentTrivialization C.evaluation
    (A.evaluation.comp (velocityFunctions H x C A g))).comp
      (Infinitesimal.tangentMap (velocityFunctions H x C A g) A.evaluation)

theorem parameterDifferential_coordinate (D : A.Tangent) (a : C.Ring) :
    (parameterDifferential H x C A g D).val a =
      D.val (velocityFunctions H x C A g (AffineVelocity.coordinate C.evaluation a)) := rfl

/-- On an actual target-open function the velocity comorphism is the
original universal-family coefficient, pulled back along g. -/
theorem velocityFunctions_localCoordinate
    (V : X.variety.scheme.Opens)
    (hV : (⊤ : (Spec (CommRingCat.of C.Ring)).Opens) ≤ C.inclusion ⁻¹ᵁ V)
    (a : RingSections X.variety.scheme V) :
    velocityFunctions H x C A g
        (AffineVelocity.coordinate C.evaluation (C.localCoordinate V hV a)) =
      g.val.appTop
        (GlobalVelocity.localCoefficient
          (HomFirstJet.deformation P marking H x (PolynomialSourceLift.atMarking marking))
          V (C.centre_preimage (FixedNodeHom.toC P marking H x) V hV) a) := by
  change (g.val ≫ GlobalVelocity.homVelocity P marking H x
      (PolynomialSourceLift.atMarking marking) C).appTop _ = _
  rw [Scheme.Hom.comp_appTop]
  exact congrArg g.val.appTop (C.velocity_original_localFunction
    (HomFirstJet.deformation P marking H x (PolynomialSourceLift.atMarking marking)) V hV a)

variable (f : FreeLine X) (hx : marking.map ≫ f.curve.map = x.map)
variable (hat : A.point.val ≫ g.val =
  (HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hx).val)

/-- The affine derivative reads the same actual Hom point lift as the
mixed-derivative theorem. No section-map linearity is postulated here. -/
theorem parameterDifferential_localCoordinate
    (D : A.Tangent) (V : X.variety.scheme.Opens)
    (hV : (⊤ : (Spec (CommRingCat.of C.Ring)).Opens) ≤ C.inclusion ⁻¹ᵁ V)
    (hnode : Set.range x.map ⊆ V) (a : RingSections X.variety.scheme V) :
    (parameterDifferential H x C A g D).val (C.localCoordinate V hV a) =
      derivativeAlong
        (AffineParameterVariation.pointLift H f x hx A g hat D).map
        (AffineParameterVariation.pointLift H f x hx A g hat D).overC
        ((FixedNodeHom.toC P marking H x ≫ x.map) ⁻¹ᵁ V)
        (parameterLift_top_le_preimage
          (AffineParameterVariation.pointLift H f x hx A g hat D) x.map V hnode)
        ((HomFirstJet.deformation P marking H x
          (PolynomialSourceLift.atMarking marking)).onFunction V a) := by
  rw [parameterDifferential_coordinate, velocityFunctions_localCoordinate,
    GlobalVelocity.localCoefficient_onFunction]
  rw [← affineLift_composite_derivative A g.val g.property D]
  exact derivativeAlong_restrict
    (AffineParameterVariation.pointLift H f x hx A g hat D).map
    (AffineParameterVariation.pointLift H f x hx A g hat D).overC
    (homOfLE (C.centre_preimage (FixedNodeHom.toC P marking H x) V hV))
    (by simp) _ _

/-- The actual chart velocity differential is the canonical evaluation of
the actual original positive vector. This is the manuscript's missing
intrinsic range comparison, with both objects independently constructed. -/
theorem parameterDifferential_eq_chartEvaluation (D : A.Tangent) :
    parameterDifferential H x C A g D =
      IntrinsicTangent.chartEvaluation C
        (positiveVector H f x hx (AffineParameterVariation.pointLift H f x hx A g hat D)) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro a
  have hnode : Set.range x.map ⊆ IntrinsicTangent.chartOpen C := by
    rintro _ ⟨z, rfl⟩
    exact IntrinsicTangent.chartOpen_point C (show z ∈ (⊤ : ComplexBase.Opens) by trivial)
  rw [← IntrinsicTangent.chartFunctions_coordinate C a,
    parameterDifferential_localCoordinate H x C A g f hx hat D
      (IntrinsicTangent.chartOpen C) (IntrinsicTangent.chartOpen_source C) hnode]
  rw [mixedDerivative_original_fiber H f x hx
    (AffineParameterVariation.pointLift H f x hx A g hat D)
    (IntrinsicTangent.chartOpen C) hnode (IntrinsicTangent.chartOpen_point C)]
  rw [IntrinsicTangent.chartEvaluation_localCoordinate C
    (IntrinsicTangent.chartOpen C) (IntrinsicTangent.chartOpen_source C)
    (IntrinsicTangent.chartOpen_point C)]

include hat in
/-- Pointwise membership in the ORIGINAL positive node space is now a
theorem about the actual global velocity differential. -/
theorem parameterDifferential_mem_positiveImage (D : A.Tangent) :
    parameterDifferential H x C A g D ∈
      (positiveNodeSpace f x hx).map (IntrinsicTangent.chartEvaluation C) := by
  rw [parameterDifferential_eq_chartEvaluation H x C A g f hx hat D]
  exact ⟨_, positiveVector_mem H f x hx _, rfl⟩

include hat in
theorem parameterDifferential_range_le_positiveImage :
    LinearMap.range (parameterDifferential H x C A g) ≤
      (positiveNodeSpace f x hx).map (IntrinsicTangent.chartEvaluation C) := by
  rintro _ ⟨D, rfl⟩
  exact parameterDifferential_mem_positiveImage H x C A g f hx hat D

include C in
/-- Injectivity of the canonical comparison derives additivity of the
actual original positive vector. It is not an extra linearity assumption
on the deformation-to-section construction. -/
theorem positiveVector_add (D E : A.Tangent) :
    positiveVector H f x hx (AffineParameterVariation.pointLift H f x hx A g hat (D+E)) =
      positiveVector H f x hx (AffineParameterVariation.pointLift H f x hx A g hat D) +
      positiveVector H f x hx (AffineParameterVariation.pointLift H f x hx A g hat E) := by
  apply IntrinsicTangent.chartEvaluation_injective C
  rw [map_add, ← parameterDifferential_eq_chartEvaluation H x C A g f hx hat,
    ← parameterDifferential_eq_chartEvaluation H x C A g f hx hat,
    ← parameterDifferential_eq_chartEvaluation H x C A g f hx hat, map_add]

include C in
theorem positiveVector_smul (c : ℂ) (D : A.Tangent) :
    positiveVector H f x hx (AffineParameterVariation.pointLift H f x hx A g hat (c • D)) =
      c • positiveVector H f x hx (AffineParameterVariation.pointLift H f x hx A g hat D) := by
  apply IntrinsicTangent.chartEvaluation_injective C
  rw [map_smul, ← parameterDifferential_eq_chartEvaluation H x C A g f hx hat,
    ← parameterDifferential_eq_chartEvaluation H x C A g f hx hat, map_smul]

include C in
/-- The original-fiber derivative of the actual velocity is a constructed
linear map. Its value is the derivative of the actual Hom variation. -/
def originalDifferential : A.Tangent →ₗ[ℂ] TangentFiber X.variety x where
  toFun D := positiveVector H f x hx (AffineParameterVariation.pointLift H f x hx A g hat D)
  map_add' := positiveVector_add H x C A g f hx hat
  map_smul' := positiveVector_smul H x C A g f hx hat

theorem originalDifferential_evaluation :
    (IntrinsicTangent.chartEvaluation C).comp (originalDifferential H x C A g f hx hat) =
      parameterDifferential H x C A g := by
  apply LinearMap.ext
  intro D
  exact (parameterDifferential_eq_chartEvaluation H x C A g f hx hat D).symm

theorem originalDifferential_mem_positive (D : A.Tangent) :
    originalDifferential H x C A g f hx hat D ∈ positiveNodeSpace f x hx :=
  positiveVector_mem H f x hx _

theorem originalDifferential_range_le_positive :
    LinearMap.range (originalDifferential H x C A g f hx hat) ≤ positiveNodeSpace f x hx := by
  rintro _ ⟨D, rfl⟩
  exact originalDifferential_mem_positive H x C A g f hx hat D

/-- The source construction of the original vector contains no target
chart. The target chart was used only to prove its linearity. -/
theorem originalDifferential_chart_independent
    (C' : GlobalVelocity.TargetChart X.variety x) :
    originalDifferential H x C A g f hx hat = originalDifferential H x C' A g f hx hat := by
  apply LinearMap.ext
  intro D
  rfl

end ParameterDifferential

end LeBrunSalamon.Construction.Lines.IntrinsicVelocityRange

end

/-!
## Actual parameter-chart naturality of the intrinsic velocity differential

The velocity differential is obtained from the actual global scheme map.
Its restriction to an affine parameter chart obeys the ordinary chain rule,
and the original positive vector is the same actual Hom variation after
chart change. For open parameter charts the differential is proved bijective
by factoring actual dual-number points through the open immersion. This
distinguishes genuine atlas restriction from arbitrary locally closed
parameter maps, for which only the chain rule is asserted.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirty
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.VelocityChartNaturality

open IntrinsicVelocityRange

/-! ### Pointed affine charts and their actual differential -/

/-- Composition keeps the actual scheme maps and original centers. -/
def composeCharts {A B C : Charts.PointedAffine}
    (h : Charts.Hom A B) (k : Charts.Hom B C) : Charts.Hom A C where
  map := h.map ≫ k.map
  overC := by rw [Category.assoc, k.overC, h.overC]
  atCentre := by rw [← Category.assoc, h.atCentre, k.atCentre]

theorem composeCharts_differential {A B C : Charts.PointedAffine}
    (h : Charts.Hom A B) (k : Charts.Hom B C) :
    (composeCharts h k).differential = k.differential.comp h.differential := by
  ext D a
  change D.val ((h.map ≫ k.map).appTop a) = D.val (h.map.appTop (k.map.appTop a))
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- Equality of actual dual-number maps determines an infinitesimal
point, since its remaining fields are proofs of the fixed equations. -/
theorem pointLift_ext {Y : Scheme} {sY : Y ⟶ ComplexBase}
    {y : PointsOver ComplexBase (𝟙 ComplexBase) Y sY}
    {v w : Infinitesimal.PointLift Y sY y} (h : v.map = w.map) : v = w := by
  cases v
  cases w
  cases h
  rfl

/-- A point lift centered in the chart has its entire topological image
in the chart. The actual nilpotent lift is not replaced by its center map. -/
theorem openChart_lift_range {A B : Charts.PointedAffine}
    (h : Charts.Hom B A) [IsOpenImmersion h.map]
    (v : Infinitesimal.PointLift A.scheme A.toC A.point) :
    Set.range v.map ⊆ Set.range h.map := by
  rw [LocalVelocityComparison.pointLift_range v]
  rintro _ ⟨c, rfl⟩
  refine ⟨B.point.val c, ?_⟩
  exact congrArg (fun k : ComplexBase ⟶ A.scheme => k c) h.atCentre

/-- Factor the actual dual-number point into the actual open parameter
chart. Both its base equation and its original center follow from the
open-immersion factorization; no tangent surjectivity is assumed. -/
def openChartLift {A B : Charts.PointedAffine}
    (h : Charts.Hom B A) [IsOpenImmersion h.map]
    (v : Infinitesimal.PointLift A.scheme A.toC A.point) :
    Infinitesimal.PointLift B.scheme B.toC B.point where
  map := IsOpenImmersion.lift h.map v.map (openChart_lift_range h v)
  overC := by
    rw [← h.overC, ← Category.assoc, IsOpenImmersion.lift_fac, v.overC]
  reduces := by
    apply (cancel_mono h.map).mp
    rw [Category.assoc, IsOpenImmersion.lift_fac, v.reduces, h.atCentre]

theorem openChartLift_map {A B : Charts.PointedAffine}
    (h : Charts.Hom B A) [IsOpenImmersion h.map]
    (v : Infinitesimal.PointLift A.scheme A.toC A.point) :
    (openChartLift h v).map ≫ h.map = v.map :=
  IsOpenImmersion.lift_fac _ _ _

/-- For any monomorphism of pointed affine schemes, its actual tangent
map is injective. This applies to locally closed parameter immersions as
well as open chart restrictions. -/
theorem differential_injective_of_mono {A B : Charts.PointedAffine}
    (h : Charts.Hom B A) [Mono h.map] : Function.Injective h.differential := by
  intro D E hDE
  apply Charts.AffineTangentLift.lift_injective B
  apply pointLift_ext
  apply (cancel_mono h.map).mp
  rw [Charts.AffineTangentLift.lift_natural,
    Charts.AffineTangentLift.lift_natural, hDE]

/-- Every actual tangent direction has an actual lift to an open chart
containing its center. This is proved with the explicit affine tangent
lift equivalence and the open immersion itself. -/
theorem differential_surjective_of_openImmersion {A B : Charts.PointedAffine}
    (h : Charts.Hom B A) [IsOpenImmersion h.map] :
    Function.Surjective h.differential := by
  intro D
  obtain ⟨E, hE⟩ := Charts.AffineTangentLift.lift_surjective B
    (openChartLift h (Charts.AffineTangentLift.lift A D))
  refine ⟨E, ?_⟩
  apply Charts.AffineTangentLift.lift_injective A
  apply pointLift_ext
  rw [← Charts.AffineTangentLift.lift_natural, hE, openChartLift_map]

theorem differential_bijective_of_openImmersion {A B : Charts.PointedAffine}
    (h : Charts.Hom B A) [IsOpenImmersion h.map] :
    Function.Bijective h.differential :=
  ⟨differential_injective_of_mono h, differential_surjective_of_openImmersion h⟩

/-- The tangent equivalence of an open atlas restriction is the actual
scheme differential, rather than a supplied equal-rank isomorphism. -/
def openChartTangentEquiv {A B : Charts.PointedAffine}
    (h : Charts.Hom B A) [IsOpenImmersion h.map] : B.Tangent ≃ₗ[ℂ] A.Tangent :=
  LinearEquiv.ofBijective h.differential (differential_bijective_of_openImmersion h)

/-! ### Restriction of the actual fixed-node parameter morphism -/

variable {n : ℕ} {X : ContactFanoManifold n}
variable (H : HomSpacePresentation P X.variety) (x : ComplexPoint X.variety)
variable (C : GlobalVelocity.TargetChart X.variety x)
variable (A B : Charts.PointedAffine) (h : Charts.Hom B A)
variable (g : PointsOver A.scheme A.toC
  (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x))

/-- The restricted parameter is the actual composite into fixed-node Hom. -/
def restrictParameter : PointsOver B.scheme B.toC
    (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x) :=
  ⟨h.map ≫ g.val, by rw [Category.assoc, g.property, h.overC]⟩

theorem restrictParameter_map : (restrictParameter H x A B h g).val = h.map ≫ g.val := rfl

/-- Atlas restriction is equality of the actual velocity scheme maps,
prior to taking any tangent spaces or local coordinates. -/
theorem chartVelocity_restrict :
    chartVelocity H x C B (restrictParameter H x A B h g) =
      h.map ≫ chartVelocity H x C A g :=
  Category.assoc _ _ _

/-- The comorphism of that actual restricted map is the original
comorphism followed by the actual chart map on global functions. -/
theorem velocityFunctions_restrict :
    velocityFunctions H x C B (restrictParameter H x A B h g) =
      h.onFunctions.comp (velocityFunctions H x C A g) := by
  apply AlgHom.ext
  intro a
  change (chartVelocity H x C B (restrictParameter H x A B h g)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (AffineVelocity.CoordinateRing C.evaluation))).inv a) =
    h.map.appTop ((chartVelocity H x C A g).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (AffineVelocity.CoordinateRing C.evaluation))).inv a))
  rw [chartVelocity_restrict, Scheme.Hom.comp_appTop]
  rfl

/-- The ordinary chain rule for the actual global velocity map, on any
actual affine parameter morphism. No smoothness premise is needed. -/
theorem parameterDifferential_restrict_apply (D : B.Tangent) :
    parameterDifferential H x C B (restrictParameter H x A B h g) D =
      parameterDifferential H x C A g (h.differential D) := by
  apply Subtype.ext
  ext a
  rw [parameterDifferential_coordinate, parameterDifferential_coordinate,
    velocityFunctions_restrict]
  rfl

theorem parameterDifferential_restrict :
    parameterDifferential H x C B (restrictParameter H x A B h g) =
      (parameterDifferential H x C A g).comp h.differential := by
  apply LinearMap.ext
  intro D
  exact parameterDifferential_restrict_apply H x C A B h g D

/-- A smaller parameter locus contributes only tangent directions
already contributed by its ambient parameter. -/
theorem parameterDifferential_range_restrict_le :
    LinearMap.range (parameterDifferential H x C B (restrictParameter H x A B h g)) ≤
      LinearMap.range (parameterDifferential H x C A g) := by
  rintro _ ⟨D, rfl⟩
  exact ⟨h.differential D, (parameterDifferential_restrict_apply H x C A B h g D).symm⟩

/-- For a genuine open chart, the velocity differential has exactly the
same range. Surjectivity of the chart differential is proved above. -/
theorem parameterDifferential_range_openRestriction [IsOpenImmersion h.map] :
    LinearMap.range (parameterDifferential H x C B (restrictParameter H x A B h g)) =
      LinearMap.range (parameterDifferential H x C A g) := by
  apply le_antisymm
  · exact parameterDifferential_range_restrict_le H x C A B h g
  · rintro _ ⟨D, rfl⟩
    obtain ⟨E, rfl⟩ := differential_surjective_of_openImmersion h D
    exact ⟨E, parameterDifferential_restrict_apply H x C A B h g E⟩

variable (f : FreeLine X) (hx : marking.map ≫ f.curve.map = x.map)
variable (hat : A.point.val ≫ g.val =
  (HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hx).val)

include hat in
/-- The restricted parameter has the same actual universal central curve. -/
theorem restrictParameter_atCentre :
    B.point.val ≫ (restrictParameter H x A B h g).val =
      (HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hx).val := by
  change B.point.val ≫ (h.map ≫ g.val) = _
  rw [← Category.assoc, h.atCentre, hat]

/-- The actual infinitesimal Hom point is unchanged by first applying
the parameter differential and then taking the original chart lift. -/
theorem pointLift_restrict (D : B.Tangent) :
    AffineParameterVariation.pointLift H f x hx B (restrictParameter H x A B h g)
        (restrictParameter_atCentre H x A B h g f hx hat) D =
      AffineParameterVariation.pointLift H f x hx A g hat (h.differential D) := by
  apply pointLift_ext
  rw [AffineParameterVariation.pointLift_chartChange H f x hx A g hat B h D]
  rfl

/-- The actual original pulled-back tangent section commutes with
parameter-chart restriction; there is no extra section-naturality premise. -/
theorem variation_restrict (D : B.Tangent) :
    AffineParameterVariation.variation H f x hx B (restrictParameter H x A B h g)
        (restrictParameter_atCentre H x A B h g f hx hat) D =
      AffineParameterVariation.variation H f x hx A g hat (h.differential D) := by
  unfold AffineParameterVariation.variation AffineParameterVariation.deformation
  rw [pointLift_restrict]

/-- The intrinsic derivative built from the actual positive variation
obeys the same ordinary chain rule as the actual velocity morphism. -/
theorem originalDifferential_restrict_apply (D : B.Tangent) :
    originalDifferential H x C B (restrictParameter H x A B h g) f hx
        (restrictParameter_atCentre H x A B h g f hx hat) D =
      originalDifferential H x C A g f hx hat (h.differential D) := by
  change positiveVector H f x hx
      (AffineParameterVariation.pointLift H f x hx B (restrictParameter H x A B h g)
        (restrictParameter_atCentre H x A B h g f hx hat) D) = _
  rw [pointLift_restrict]
  rfl

theorem originalDifferential_restrict :
    originalDifferential H x C B (restrictParameter H x A B h g) f hx
        (restrictParameter_atCentre H x A B h g f hx hat) =
      (originalDifferential H x C A g f hx hat).comp h.differential := by
  apply LinearMap.ext
  intro D
  exact originalDifferential_restrict_apply H x C A B h g f hx hat D

theorem originalDifferential_range_restrict_le :
    LinearMap.range (originalDifferential H x C B (restrictParameter H x A B h g) f hx
      (restrictParameter_atCentre H x A B h g f hx hat)) ≤
      LinearMap.range (originalDifferential H x C A g f hx hat) := by
  rintro _ ⟨D, rfl⟩
  exact ⟨h.differential D, (originalDifferential_restrict_apply H x C A B h g f hx hat D).symm⟩

/-- Replacing a parameter by a genuine open neighborhood leaves its
intrinsic velocity derivative range in the original tangent fiber unchanged. -/
theorem originalDifferential_range_openRestriction [IsOpenImmersion h.map] :
    LinearMap.range (originalDifferential H x C B (restrictParameter H x A B h g) f hx
      (restrictParameter_atCentre H x A B h g f hx hat)) =
      LinearMap.range (originalDifferential H x C A g f hx hat) := by
  apply le_antisymm
  · exact originalDifferential_range_restrict_le H x C A B h g f hx hat
  · rintro _ ⟨D, rfl⟩
    obtain ⟨E, rfl⟩ := differential_surjective_of_openImmersion h D
    exact ⟨E, originalDifferential_restrict_apply H x C A B h g f hx hat E⟩

/-! ### Canonical target-chart transition -/

variable (C' : GlobalVelocity.TargetChart X.variety x)

include f hx hat in
/-- The same actual global velocity differential, expressed in a second
actual target chart, is obtained by the canonical transition through the
original tangent fiber. Both coordinate maps were independently constructed. -/
theorem parameterDifferential_targetChange (D : A.Tangent) :
    IntrinsicTangent.chartTransition C C' (parameterDifferential H x C A g D) =
      parameterDifferential H x C' A g D := by
  rw [parameterDifferential_eq_chartEvaluation H x C A g f hx hat D,
    IntrinsicTangent.chartTransition_evaluation,
    parameterDifferential_eq_chartEvaluation H x C' A g f hx hat D]

include f hx hat in
theorem parameterDifferential_targetChange_linear :
    (IntrinsicTangent.chartTransition C C').toLinearMap.comp
        (parameterDifferential H x C A g) = parameterDifferential H x C' A g := by
  apply LinearMap.ext
  intro D
  exact parameterDifferential_targetChange H x C A g f hx hat C' D

include f hx hat in
/-- The kernel of the actual velocity differential does not depend on
which target chart is used to read its local coordinates. -/
theorem parameterDifferential_kernel_targetChange :
    LinearMap.ker (parameterDifferential H x C A g) =
      LinearMap.ker (parameterDifferential H x C' A g) := by
  have hzero : IntrinsicTangent.chartTransition C C'
      (0 : Infinitesimal.Tangent C.Ring C.evaluation) =
      (0 : Infinitesimal.Tangent C'.Ring C'.evaluation) :=
    (IntrinsicTangent.chartTransition C C').toLinearMap.map_zero
  ext D
  change parameterDifferential H x C A g D = 0 ↔ parameterDifferential H x C' A g D = 0
  constructor
  · intro hD
    rw [← parameterDifferential_targetChange H x C A g f hx hat C' D, hD, hzero]
  · intro hD
    apply (IntrinsicTangent.chartTransition C C').injective
    rw [hzero, parameterDifferential_targetChange H x C A g f hx hat C' D, hD]

include f hx hat in
/-- Parameter and target chart changes commute on the actual derivative,
which is the compatibility needed when shrinking to smooth atlas charts. -/
theorem parameterDifferential_doubleChange (D : B.Tangent) :
    IntrinsicTangent.chartTransition C C'
      (parameterDifferential H x C B (restrictParameter H x A B h g) D) =
        parameterDifferential H x C' A g (h.differential D) := by
  rw [parameterDifferential_restrict_apply,
    parameterDifferential_targetChange H x C A g f hx hat C']

/-- The actual original tangent vector is recovered by the normalized
inverse chart equivalence, so its definition has no residual coordinate
dependence when later geometric arguments are stated in affine models. -/
theorem originalDifferential_eq_chartInverse (D : A.Tangent) :
    originalDifferential H x C A g f hx hat D =
      (IntrinsicTangent.chartEquivalence C).symm (parameterDifferential H x C A g D) := by
  apply (IntrinsicTangent.chartEquivalence C).injective
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg (fun k : A.Tangent →ₗ[ℂ]
      Infinitesimal.Tangent C.Ring C.evaluation => k D)
    (originalDifferential_evaluation H x C A g f hx hat)

end LeBrunSalamon.Construction.Lines.VelocityChartNaturality

end

/-!
## Restricting the actual velocity to the original contact target

The differential into the actual closed contact target is normalized by its
closed immersion. The pointwise original positive vector then determines it
uniquely. For an actual reduced finite-type affine parameter whose points
represent free contact lines through x, the scheme factorization is proved
from those curves, the normalized source tangent, and complex-point detection.
Existence of the required bounded parameter spaces is a separate obligation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.ContactVelocityFactorization

open IntrinsicVelocityRange

section OriginalDifferential

variable {n : ℕ} {X : ContactFanoManifold n}
variable (H : HomSpacePresentation P X.variety) (x : ComplexPoint X.variety)
variable (C : GlobalVelocity.TargetChart X.variety x)
variable (A : Charts.PointedAffine)
variable (g : PointsOver A.scheme A.toC
  (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x))
variable (f : FreeLine X) (hx : marking.map ≫ f.curve.map = x.map)
variable (hat : A.point.val ≫ g.val =
  (HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hx).val)

/-- Horizontality is inherited from the proved positive-node theorem,
not from its historical admitted version. -/
theorem originalDifferential_mem_contact (D : A.Tangent) :
    originalDifferential H x C A g f hx hat D ∈ contactPlane X x :=
  ContactPositive.positiveNodeSpace_horizontal f x hx
    (originalDifferential_mem_positive H x C A g f hx hat D)

def originalContactDifferential : A.Tangent →ₗ[ℂ] contactPlane X x :=
  (originalDifferential H x C A g f hx hat).codRestrict (contactPlane X x)
    (originalDifferential_mem_contact H x C A g f hx hat)

theorem originalContactDifferential_positive (D : A.Tangent) :
    (originalContactDifferential H x C A g f hx hat D).val ∈ positiveNodeSpace f x hx :=
  originalDifferential_mem_positive H x C A g f hx hat D

theorem originalContactDifferential_evaluation (D : A.Tangent) :
    IntrinsicTangent.chartEvaluation C
        (originalContactDifferential H x C A g f hx hat D).val =
      parameterDifferential H x C A g D :=
  LinearMap.congr_fun (originalDifferential_evaluation H x C A g f hx hat) D

include hat in
/-- The canonical evaluation carries the actual velocity differential
into the actual contact image as a consequence of the positive-range proof. -/
theorem parameterDifferential_mem_contactImage (D : A.Tangent) :
    parameterDifferential H x C A g D ∈ ContactVelocityTarget.image X x C := by
  rw [← originalContactDifferential_evaluation H x C A g f hx hat D]
  exact ⟨_, (originalContactDifferential H x C A g f hx hat D).property, rfl⟩

end OriginalDifferential

section ActualFactors

variable {n : ℕ} {X : ContactFanoManifold n}
variable (H : HomSpacePresentation P X.variety) (x : ComplexPoint X.variety)
variable (C : GlobalVelocity.TargetChart X.variety x) (A : Charts.PointedAffine)
variable (g : PointsOver A.scheme A.toC
  (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x))

/-- The ordinary tangent map of a specified comorphism into the actual
contact target, expressed in its proved original-fiber tangent coordinates. -/
def differentialOfFactor
    (ψ : ContactVelocityTarget.CoordinateAlgebra X x C →ₐ[ℂ] A.Ring) :
    A.Tangent →ₗ[ℂ] contactPlane X x :=
  (ContactVelocityTarget.tangentEquiv X x C (A.evaluation.comp ψ)).toLinearMap.comp
    (Infinitesimal.tangentMap ψ A.evaluation)

/-- The factorization equation on actual functions identifies this map
with the already constructed ambient velocity differential. -/
theorem differentialOfFactor_evaluation
    (ψ : ContactVelocityTarget.CoordinateAlgebra X x C →ₐ[ℂ] A.Ring)
    (hψ : ψ.comp (LinearVelocityTarget.quotientMap C.evaluation
      (ContactVelocityTarget.image X x C)) = velocityFunctions H x C A g)
    (D : A.Tangent) :
    IntrinsicTangent.chartEvaluation C (differentialOfFactor x C A ψ D).val =
      parameterDifferential H x C A g D := by
  change IntrinsicTangent.chartEvaluation C
    (ContactVelocityTarget.tangentEquiv X x C (A.evaluation.comp ψ)
      (Infinitesimal.tangentMap ψ A.evaluation D)).val = _
  rw [ContactVelocityTarget.tangentEquiv_normalized]
  apply Subtype.ext
  ext a
  change D.val (ψ (LinearVelocityTarget.quotientMap C.evaluation
    (ContactVelocityTarget.image X x C) (AffineVelocity.coordinate C.evaluation a))) =
      D.val (velocityFunctions H x C A g (AffineVelocity.coordinate C.evaluation a))
  exact congrArg D.val (AlgHom.congr_fun hψ (AffineVelocity.coordinate C.evaluation a))

/-- The differential of the actual scheme factor is the independently
constructed derivative of the original Hom variation. -/
theorem differentialOfFactor_eq_original
    (f : FreeLine X) (hx : marking.map ≫ f.curve.map = x.map)
    (hat : A.point.val ≫ g.val =
      (HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hx).val)
    (ψ : ContactVelocityTarget.CoordinateAlgebra X x C →ₐ[ℂ] A.Ring)
    (hψ : ψ.comp (LinearVelocityTarget.quotientMap C.evaluation
      (ContactVelocityTarget.image X x C)) = velocityFunctions H x C A g) :
    differentialOfFactor x C A ψ = originalContactDifferential H x C A g f hx hat := by
  apply LinearMap.ext
  intro D
  apply Subtype.ext
  apply IntrinsicTangent.chartEvaluation_injective C
  rw [differentialOfFactor_evaluation H x C A g ψ hψ,
    originalContactDifferential_evaluation H x C A g f hx hat]

theorem differentialOfFactor_positive
    (f : FreeLine X) (hx : marking.map ≫ f.curve.map = x.map)
    (hat : A.point.val ≫ g.val =
      (HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hx).val)
    (ψ : ContactVelocityTarget.CoordinateAlgebra X x C →ₐ[ℂ] A.Ring)
    (hψ : ψ.comp (LinearVelocityTarget.quotientMap C.evaluation
      (ContactVelocityTarget.image X x C)) = velocityFunctions H x C A g)
    (D : A.Tangent) : (differentialOfFactor x C A ψ D).val ∈ positiveNodeSpace f x hx := by
  rw [differentialOfFactor_eq_original H x C A g f hx hat ψ hψ]
  exact originalContactDifferential_positive H x C A g f hx hat D

/-- Surjectivity here is exactly surjectivity of the genuine scheme
differential into the closed target, because its tangent comparison is an
equivalence. This supplies the normalization needed by generic smoothness. -/
theorem differentialOfFactor_surjective_iff
    (ψ : ContactVelocityTarget.CoordinateAlgebra X x C →ₐ[ℂ] A.Ring) :
    Function.Surjective (differentialOfFactor x C A ψ) ↔
      Function.Surjective (Infinitesimal.tangentMap ψ A.evaluation) := by
  constructor
  · intro h D
    obtain ⟨v, hv⟩ := h (ContactVelocityTarget.tangentEquiv X x C (A.evaluation.comp ψ) D)
    exact ⟨v, (ContactVelocityTarget.tangentEquiv X x C (A.evaluation.comp ψ)).injective hv⟩
  · intro h
    exact (ContactVelocityTarget.tangentEquiv X x C (A.evaluation.comp ψ)).surjective.comp h

end ActualFactors

section ParameterPoints

/-- Every algebra point of the actual affine parameter ring is realized
as an actual scheme point by the canonical affine isomorphism. -/
def pointOfAlgebra (A : Charts.PointedAffine) (s : A.Ring →ₐ[ℂ] ℂ) :
    PointsOver ComplexBase (𝟙 ComplexBase) A.scheme A.toC := by
  refine ⟨Charts.AffineTangentLift.fromFunctions A.scheme s.toRingHom, ?_⟩
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  ext c
  change (Charts.AffineTangentLift.fromFunctions A.scheme s.toRingHom).appTop
    (A.toC.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c
  rw [← complexConstants_apply_top, Charts.AffineTangentLift.fromFunctions_apply]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv (s (algebraMap ℂ A.Ring c)) = _
  rw [s.commutes]
  rfl

theorem pointOfAlgebra_function (A : Charts.PointedAffine) (s : A.Ring →ₐ[ℂ] ℂ)
    (a : A.Ring) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((pointOfAlgebra A s).val.appTop a) = s a := by
  rw [show (pointOfAlgebra A s).val =
    Charts.AffineTangentLift.fromFunctions A.scheme s.toRingHom from rfl,
    Charts.AffineTangentLift.fromFunctions_apply]
  exact Iso.inv_hom_id_apply _ _

/-- The ring point of the selected chart center is its original scheme point. -/
theorem pointOfAlgebra_evaluation (A : Charts.PointedAffine) :
    pointOfAlgebra A A.evaluation = A.point := by
  apply Subtype.ext
  apply ext_of_isAffine
  apply CommRingCat.hom_ext
  ext a
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1
  rw [pointOfAlgebra_function]
  rfl

variable {n : ℕ} {X : ContactFanoManifold n}
variable (H : HomSpacePresentation P X.variety) (x : ComplexPoint X.variety)
variable (C : GlobalVelocity.TargetChart X.variety x) (A : Charts.PointedAffine)
variable (g : PointsOver A.scheme A.toC
  (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x))

def homPointOfAlgebra (s : A.Ring →ₐ[ℂ] ℂ) :
    PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x) :=
  ⟨(pointOfAlgebra A s).val ≫ g.val, by
    rw [Category.assoc, g.property]; exact (pointOfAlgebra A s).property⟩

/-- Evaluation of the actual parameter comorphism agrees with the actual
global velocity value at the corresponding Hom point. -/
theorem velocityFunctions_point (s : A.Ring →ₐ[ℂ] ℂ) :
    AffineVelocity.tangentPointEquiv C.evaluation (s.comp (velocityFunctions H x C A g)) =
      HomVelocityValue.value H x C (homPointOfAlgebra H x A g s) := by
  apply Subtype.ext
  ext a
  change s (velocityFunctions H x C A g (AffineVelocity.coordinate C.evaluation a)) =
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (((pointOfAlgebra A s).val ≫ g.val ≫
        GlobalVelocity.homVelocity P marking H x (PolynomialSourceLift.atMarking marking) C).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (AffineVelocity.CoordinateRing C.evaluation))).inv
            (AffineVelocity.coordinate C.evaluation a)))
  rw [Scheme.Hom.comp_appTop]
  exact (pointOfAlgebra_function A s
    (velocityFunctions H x C A g (AffineVelocity.coordinate C.evaluation a))).symm

/-- The parameter condition specifies only the actual represented curves.
Contact membership of velocity is proved from their actual differentials. -/
theorem velocityFunctions_points_mem
    (hfree : ∀ t : PointsOver ComplexBase (𝟙 ComplexBase) A.scheme A.toC,
      ∃ (f : FreeLine X) (hf : marking.map ≫ f.curve.map = x.map),
        t.val ≫ g.val =
          (HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hf).val)
    (s : A.Ring →ₐ[ℂ] ℂ) :
    AffineVelocity.tangentPointEquiv C.evaluation (s.comp (velocityFunctions H x C A g)) ∈
      ContactVelocityTarget.image X x C := by
  rw [velocityFunctions_point]
  obtain ⟨f, hf, ht⟩ := hfree (pointOfAlgebra A s)
  have hp : homPointOfAlgebra H x A g s =
      HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hf := Subtype.ext ht
  rw [hp]
  exact HomVelocityValue.value_fixedCenter_mem_contactImage H f x hf C

end ParameterPoints

section ReducedFreeParameters

variable {n : ℕ} {X : ContactFanoManifold n}
variable (H : HomSpacePresentation P X.variety) (x : ComplexPoint X.variety)
variable (C : GlobalVelocity.TargetChart X.variety x) (A : Charts.PointedAffine)
variable (g : PointsOver A.scheme A.toC
  (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x))
variable [Algebra.FiniteType ℂ A.Ring] [IsReduced A.Ring]
variable (hfree : ∀ t : PointsOver ComplexBase (𝟙 ComplexBase) A.scheme A.toC,
  ∃ (f : FreeLine X) (hf : marking.map ≫ f.curve.map = x.map),
    t.val ≫ g.val =
      (HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hf).val)

/-- The regular-function factorization is constructed from the actual
curve-valued parameter and reduced finite-type point detection. -/
def contactFunctions : ContactVelocityTarget.CoordinateAlgebra X x C →ₐ[ℂ] A.Ring :=
  LinearVelocityTarget.factorOfPoints C.evaluation (ContactVelocityTarget.image X x C)
    (velocityFunctions H x C A g) (velocityFunctions_points_mem H x C A g hfree)

theorem contactFunctions_factorization :
    (contactFunctions H x C A g hfree).comp
        (LinearVelocityTarget.quotientMap C.evaluation (ContactVelocityTarget.image X x C)) =
      velocityFunctions H x C A g :=
  LinearVelocityTarget.factorOfPoints_comp C.evaluation (ContactVelocityTarget.image X x C)
    (velocityFunctions H x C A g) (velocityFunctions_points_mem H x C A g hfree)

/-- The same actual section ring with its declared complex scalar structure. -/
def contactGlobalFunctions :
    ContactVelocityTarget.CoordinateAlgebra X x C →ₐ[ℂ] SectionAlgebra.Functions A.toC ⊤ where
  toRingHom := (contactFunctions H x C A g hfree).toRingHom
  commutes' := (contactFunctions H x C A g hfree).commutes

def contactMorphism : A.scheme ⟶ ContactVelocityTarget.scheme X x C :=
  GlobalVelocity.toSpec (contactGlobalFunctions H x C A g hfree)

theorem contactMorphism_overC :
    contactMorphism H x C A g hfree ≫ ContactVelocityTarget.toC X x C = A.toC :=
  GlobalVelocity.toSpec_overC (contactGlobalFunctions H x C A g hfree)

theorem contactMorphism_function (a : ContactVelocityTarget.CoordinateAlgebra X x C) :
    (contactMorphism H x C A g hfree).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (ContactVelocityTarget.CoordinateAlgebra X x C))).inv a) =
      contactFunctions H x C A g hfree a :=
  GlobalVelocity.toSpec_function (contactGlobalFunctions H x C A g hfree) a

/-- The scheme factor is the original restricted velocity after its actual
closed immersion, proved on complete regular-function algebras. -/
theorem contactMorphism_inclusion :
    contactMorphism H x C A g hfree ≫ ContactVelocityTarget.inclusion X x C =
      chartVelocity H x C A g := by
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  ext a
  change (contactMorphism H x C A g hfree).appTop
      ((ContactVelocityTarget.inclusion X x C).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (AffineVelocity.CoordinateRing C.evaluation))).inv a)) =
    velocityFunctions H x C A g a
  have hn := congrArg (fun k : CommRingCat.of (AffineVelocity.CoordinateRing C.evaluation) ⟶
      (ContactVelocityTarget.scheme X x C).presheaf.obj (op ⊤) => k a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (LinearVelocityTarget.quotientMap C.evaluation
        (ContactVelocityTarget.image X x C)).toRingHom))
  simp only [CommRingCat.comp_apply] at hn
  change
    (Scheme.ΓSpecIso
      (CommRingCat.of (ContactVelocityTarget.CoordinateAlgebra X x C))).inv
        (LinearVelocityTarget.quotientMap C.evaluation
          (ContactVelocityTarget.image X x C) a) =
      (ContactVelocityTarget.inclusion X x C).appTop
        ((Scheme.ΓSpecIso
          (CommRingCat.of (AffineVelocity.CoordinateRing C.evaluation))).inv a) at hn
  exact (congrArg (fun u : (ContactVelocityTarget.scheme X x C).presheaf.obj (op ⊤) =>
      (contactMorphism H x C A g hfree).appTop u) hn.symm).trans
    ((contactMorphism_function H x C A g hfree
      (LinearVelocityTarget.quotientMap C.evaluation
        (ContactVelocityTarget.image X x C) a)).trans
      (AlgHom.congr_fun (contactFunctions_factorization H x C A g hfree) a))

/-- Since the inclusion is a closed immersion, this factor is unique. -/
theorem contactMorphism_unique (k : A.scheme ⟶ ContactVelocityTarget.scheme X x C)
    (hk : k ≫ ContactVelocityTarget.inclusion X x C = chartVelocity H x C A g) :
    k = contactMorphism H x C A g hfree := by
  apply (cancel_mono (ContactVelocityTarget.inclusion X x C)).mp
  exact hk.trans (contactMorphism_inclusion H x C A g hfree).symm

/-- The derivative of the constructed scheme factor has the proved
original positive range at every represented free line. -/
theorem contactMorphism_differential_positive
    (f : FreeLine X) (hf : marking.map ≫ f.curve.map = x.map)
    (hat : A.point.val ≫ g.val =
      (HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hf).val)
    (D : A.Tangent) :
    (differentialOfFactor x C A (contactFunctions H x C A g hfree) D).val ∈
      positiveNodeSpace f x hf :=
  differentialOfFactor_positive H x C A g f hf hat
    (contactFunctions H x C A g hfree) (contactFunctions_factorization H x C A g hfree) D

end ReducedFreeParameters

end LeBrunSalamon.Construction.Lines.ContactVelocityFactorization

end

/-!
## Suitable pairs from the actual contact-velocity differentials

This closes the linear-algebra conclusion of the manuscript once its
geometric dominance/generic-smoothness step has supplied surjectivity for
the actual derivative sum. The input maps below are the actual parameter
maps and their actual velocity factors. Positive-range containment, the
original-fiber comparisons, and the original source tangent are constructed
in the preceding arguments, rather than provided as desired conclusions.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.ActualVelocitySuitablePair

open IntrinsicVelocityRange ContactVelocityFactorization

variable {n : ℕ} {X : ContactFanoManifold n}
variable (H : HomSpacePresentation P X.variety) (x : ComplexPoint X.variety)
variable (C : GlobalVelocity.TargetChart X.variety x)
variable (A B : Charts.PointedAffine)
variable (gA : PointsOver A.scheme A.toC
  (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x))
variable (gB : PointsOver B.scheme B.toC
  (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x))
variable (f₁ f₂ : FreeLine X)
variable (h₁ : marking.map ≫ f₁.curve.map = x.map)
variable (h₂ : marking.map ≫ f₂.curve.map = x.map)
variable (hat₁ : A.point.val ≫ gA.val =
  (HomDeformation.fixedCenter P H marking x f₁.curve.map f₁.curve.overC h₁).val)
variable (hat₂ : B.point.val ≫ gB.val =
  (HomDeformation.fixedCenter P H marking x f₂.curve.map f₂.curve.overC h₂).val)
variable (ψ₁ : ContactVelocityTarget.CoordinateAlgebra X x C →ₐ[ℂ] A.Ring)
variable (ψ₂ : ContactVelocityTarget.CoordinateAlgebra X x C →ₐ[ℂ] B.Ring)
variable (hψ₁ : ψ₁.comp (LinearVelocityTarget.quotientMap C.evaluation
  (ContactVelocityTarget.image X x C)) = velocityFunctions H x C A gA)
variable (hψ₂ : ψ₂.comp (LinearVelocityTarget.quotientMap C.evaluation
  (ContactVelocityTarget.image X x C)) = velocityFunctions H x C B gB)

/-- The source tangent vectors and the original positive subspace conditions
are no longer caller-supplied. The only geometric conclusions still needed
are nonorthogonality of the actual curve velocities and surjectivity of
the actual two factor differentials. -/
def from_actual_factor_differentials
    (htrans : NonzeroLeviPair X x
      (nodeDifferential f₁ x h₁ (SourceTangent.sourceVector marking))
      (nodeDifferential f₂ x h₂ (SourceTangent.sourceVector marking)))
    (hsurj : Function.Surjective
      ((differentialOfFactor x C A ψ₁).coprod (differentialOfFactor x C B ψ₂))) :
    SuitablePair X :=
  ContactPositive.suitablePair_of_surjective_variation x f₁ f₂ h₁ h₂
    (SourceTangent.sourceVector marking) (SourceTangent.sourceVector marking) htrans
    (differentialOfFactor x C A ψ₁) (differentialOfFactor x C B ψ₂)
    (differentialOfFactor_positive H x C A gA f₁ h₁ hat₁ ψ₁ hψ₁)
    (differentialOfFactor_positive H x C B gB f₂ h₂ hat₂ ψ₂ hψ₂) hsurj

include hat₁ hat₂ hψ₁ hψ₂ in
/-- The resulting spanning identity is in the manuscript's original
contact plane, not in an unspecified isomorphic vector space. -/
theorem positive_spaces_span_of_actual_differentials
    (htrans : NonzeroLeviPair X x
      (nodeDifferential f₁ x h₁ (SourceTangent.sourceVector marking))
      (nodeDifferential f₂ x h₂ (SourceTangent.sourceVector marking)))
    (hsurj : Function.Surjective
      ((differentialOfFactor x C A ψ₁).coprod (differentialOfFactor x C B ψ₂))) :
    positiveNodeSpace f₁ x h₁ ⊔ positiveNodeSpace f₂ x h₂ = contactPlane X x :=
  (from_actual_factor_differentials H x C A B gA gB f₁ f₂ h₁ h₂ hat₁ hat₂
    ψ₁ ψ₂ hψ₁ hψ₂ htrans hsurj).spans

include hat₁ hat₂ hψ₁ hψ₂ in
/-- The manuscript's dimension and complementarity conclusions now
follow from the already proved contact isotropy bounds. -/
theorem positive_spaces_complementary_of_actual_differentials
    (htrans : NonzeroLeviPair X x
      (nodeDifferential f₁ x h₁ (SourceTangent.sourceVector marking))
      (nodeDifferential f₂ x h₂ (SourceTangent.sourceVector marking)))
    (hsurj : Function.Surjective
      ((differentialOfFactor x C A ψ₁).coprod (differentialOfFactor x C B ψ₂))) :
    Disjoint (positiveNodeSpace f₁ x h₁) (positiveNodeSpace f₂ x h₂) ∧
      Module.finrank ℂ (positiveNodeSpace f₁ x h₁) = n ∧
      Module.finrank ℂ (positiveNodeSpace f₂ x h₂) = n := by
  let D := from_actual_factor_differentials H x C A B gA gB f₁ f₂ h₁ h₂ hat₁ hat₂
    ψ₁ ψ₂ hψ₁ hψ₂ htrans hsurj
  exact ⟨ContactPositive.suitablePair_complementary D,
    ContactPositive.suitablePair_positive_dimensions D⟩

/-! ### The actual derivative-sum morphism on the actual parameter product -/

/-- The tangent comparison for each actual factor commutes with the
canonical contact-plane image equivalence. -/
theorem factorDifferential_image
    (ψ : ContactVelocityTarget.CoordinateAlgebra X x C →ₐ[ℂ] A.Ring)
    (D : A.Tangent) :
    ContactVelocityTarget.imageEquiv X x C (differentialOfFactor x C A ψ D) =
      LinearVelocityAddition.differential C.evaluation
        (ContactVelocityTarget.image X x C) ψ A.evaluation D := by
  change ContactVelocityTarget.imageEquiv X x C
    ((ContactVelocityTarget.imageEquiv X x C).symm
      (LinearVelocityAddition.differential C.evaluation
        (ContactVelocityTarget.image X x C) ψ A.evaluation D)) = _
  exact (ContactVelocityTarget.imageEquiv X x C).apply_symm_apply _

/-- The canonical contact image transports the coproduct of the two
original-fiber derivatives to the actual sum differential coordinates. -/
theorem factorCoproduct_image (D : A.Tangent × B.Tangent) :
    ContactVelocityTarget.imageEquiv X x C
        (((differentialOfFactor x C A ψ₁).coprod
          (differentialOfFactor x C B ψ₂)) D) =
      LinearVelocityAddition.sumDifferentials C.evaluation
        (ContactVelocityTarget.image X x C) ψ₁ ψ₂ A.evaluation B.evaluation D := by
  change ContactVelocityTarget.imageEquiv X x C
    (differentialOfFactor x C A ψ₁ D.1 + differentialOfFactor x C B ψ₂ D.2) = _
  rw [map_add, factorDifferential_image x C A, factorDifferential_image x C B]
  rfl

/-- Generic smoothness must provide surjectivity for this actual scheme
differential on Spec(A ⊗ B). The theorem proves that this is precisely the
surjectivity required by the original suitable-pair construction. -/
theorem factorCoproduct_surjective_iff_actual_sum :
    Function.Surjective ((differentialOfFactor x C A ψ₁).coprod
      (differentialOfFactor x C B ψ₂)) ↔
      Function.Surjective (Infinitesimal.tangentMap
        (LinearVelocityAddition.parameterSum C.evaluation
          (ContactVelocityTarget.image X x C) ψ₁ ψ₂)
        (LinearVelocityAddition.tensorPoint A.evaluation B.evaluation)) := by
  rw [← LinearVelocityAddition.sumDifferentials_surjective_iff_actual
    C.evaluation (ContactVelocityTarget.image X x C) ψ₁ ψ₂ A.evaluation B.evaluation]
  constructor
  · intro h w
    obtain ⟨D, hD⟩ := h ((ContactVelocityTarget.imageEquiv X x C).symm w)
    refine ⟨D, ?_⟩
    rw [← factorCoproduct_image x C A B ψ₁ ψ₂, hD, LinearEquiv.apply_symm_apply]
  · intro h w
    obtain ⟨D, hD⟩ := h (ContactVelocityTarget.imageEquiv X x C w)
    refine ⟨D, (ContactVelocityTarget.imageEquiv X x C).injective ?_⟩
    rw [factorCoproduct_image x C A B ψ₁ ψ₂]
    exact hD

/-- The final positive-space inference in `lines:suitable-pair`, now
starting from the differential of the actual product-parameter sum map.
Its dominance and generic-smoothness hypotheses must still be established
on the appropriate actual geometric parameter spaces. -/
def from_actual_sum_differential
    (htrans : NonzeroLeviPair X x
      (nodeDifferential f₁ x h₁ (SourceTangent.sourceVector marking))
      (nodeDifferential f₂ x h₂ (SourceTangent.sourceVector marking)))
    (hsurj : Function.Surjective (Infinitesimal.tangentMap
      (LinearVelocityAddition.parameterSum C.evaluation
        (ContactVelocityTarget.image X x C) ψ₁ ψ₂)
      (LinearVelocityAddition.tensorPoint A.evaluation B.evaluation))) : SuitablePair X :=
  from_actual_factor_differentials H x C A B gA gB f₁ f₂ h₁ h₂ hat₁ hat₂
    ψ₁ ψ₂ hψ₁ hψ₂ htrans
    ((factorCoproduct_surjective_iff_actual_sum x C A B ψ₁ ψ₂).mpr hsurj)

include hat₁ hat₂ hψ₁ hψ₂ in
/-- The two actual positive spaces are consequently complementary
n-dimensional subspaces of the original contact plane. -/
theorem positive_spaces_of_actual_sum
    (htrans : NonzeroLeviPair X x
      (nodeDifferential f₁ x h₁ (SourceTangent.sourceVector marking))
      (nodeDifferential f₂ x h₂ (SourceTangent.sourceVector marking)))
    (hsurj : Function.Surjective (Infinitesimal.tangentMap
      (LinearVelocityAddition.parameterSum C.evaluation
        (ContactVelocityTarget.image X x C) ψ₁ ψ₂)
      (LinearVelocityAddition.tensorPoint A.evaluation B.evaluation))) :
    positiveNodeSpace f₁ x h₁ ⊔ positiveNodeSpace f₂ x h₂ = contactPlane X x ∧
      Disjoint (positiveNodeSpace f₁ x h₁) (positiveNodeSpace f₂ x h₂) ∧
      Module.finrank ℂ (positiveNodeSpace f₁ x h₁) = n ∧
      Module.finrank ℂ (positiveNodeSpace f₂ x h₂) = n := by
  let D := from_actual_sum_differential H x C A B gA gB f₁ f₂ h₁ h₂ hat₁ hat₂
    ψ₁ ψ₂ hψ₁ hψ₂ htrans hsurj
  exact ⟨D.spans, ContactPositive.suitablePair_complementary D,
    ContactPositive.suitablePair_positive_dimensions D⟩

end LeBrunSalamon.Construction.Lines.ActualVelocitySuitablePair

end
