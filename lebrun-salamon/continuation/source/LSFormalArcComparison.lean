import LSGenericFamilyComparison
import LSFormalArcFamilyComparison
import LSArcParametrization
import LSModelGenericComparison
import LSRationalOpenTransport
import LSFormalArcModelTransport

/-!
# Regularity of the descended moving pair on every actual formal arc

Both complete source normal forms carry regular model sections.  Their
whole generic squares agree with the original parametrized tensors.
The arbitrary-field comparison identifies those tensors with the
descended smooth-family sections; the actual two marked points then
identify their generic values.  Finally the actual-open transport
theorem gives regularity in the original `FormalArcs.Regular` sense.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction.FormalArcComparison

local notation "Model" => LeBrunSalamon.Construction.StableMaps.FormalArcs.Model

open StableMaps StableMaps.FormalArcs StableMaps.TraitPullback
open FamilyBivectors FormalArcSections TraitContact

variable {n : ℕ} {X : ContactFanoManifold n}

section Regularity

variable {g : VeryFreeContactConic Lines.P Lines.marking X}
variable {N : FullConicNeighborhood Lines.P Lines.marking X g}
variable {F : ProjectiveNodalFamily Lines.P Lines.marking
  X.variety X.contact.sequence.line 2}
variable (Q : FullHomComparison Lines.P Lines.marking X.variety N.homSpace N.neighborhood
  X.contact.sequence.line 2 F)
variable (gamma : PointsOver Trait toC F.Square (F.squareToBase ≫ F.toC))

theorem smooth_regular
    (u : Source F (baseArc F gamma) ≅ SmoothModel)
    (hu : u.hom ≫ smoothProjection = parameter F (baseArc F gamma))
    (hU : Dense (gamma.val ⁻¹ᵁ F.smoothSquareOpen : Set Trait)) :
    Regular (SmoothFamily.rationalPair Q).leftRational gamma.val ∧
      Regular (SmoothFamily.rationalPair Q).rightRational gamma.val := by
  constructor
  · exact left_regular_of_model Q gamma smoothProjection u hu smoothGenericParametrization
      smoothGenericParametrization_isPullback hU _ (smooth_model_left F gamma u hu)
  · exact right_regular_of_model Q gamma smoothProjection u hu smoothGenericParametrization
      smoothGenericParametrization_isPullback hU _ (smooth_model_right F gamma u hu)

theorem nodal_regular (S : Smoothing.StandardSource) (a : Coefficients) (ha : a ≠ 0)
    (u : Source F (baseArc F gamma) ≅ Model S a)
    (hu : u.hom ≫ modelProjection S a = parameter F (baseArc F gamma))
    (ell : (TraitPullback.line F (baseArc F gamma)).sheaf ≅
      pullbackModule u.hom (modelLine S a).sheaf)
    (hU : Dense (gamma.val ⁻¹ᵁ F.smoothSquareOpen : Set Trait)) :
    Regular (SmoothFamily.rationalPair Q).leftRational gamma.val ∧
      Regular (SmoothFamily.rationalPair Q).rightRational gamma.val := by
  obtain ⟨c, hc, _⟩ := Nodal.common_exists F gamma S a u hu ell ha
  let k := ModelGenericComparison.genericParametrization S a ha
  let hk := ModelGenericComparison.genericParametrization_isPullback S a ha
  constructor
  · apply left_regular_of_model Q gamma (modelProjection S a) u hu k hk hU
      (RegularModel.leftSection X S a (Transport.evaluation F gamma u)
        (Transport.evaluation_overC F gamma (modelProjection S a) u hu)
        (Transport.line F gamma u ell) c)
    simpa only [Generic.toModelSquare, ModelGenericComparison.parametrizedToModelSquare,
      genericEvaluationSquare, genericEvaluation, ModelGenericComparison.genericEvaluation,
      ModelGenericComparison.genericBase, k] using
      ModelGenericComparison.leftSection_generic S a X (Transport.evaluation F gamma u)
        (Transport.evaluation_overC F gamma (modelProjection S a) u hu)
        (Transport.line F gamma u ell) c hc ha
  · apply right_regular_of_model Q gamma (modelProjection S a) u hu k hk hU
      (RegularModel.rightSection X S a (Transport.evaluation F gamma u)
        (Transport.evaluation_overC F gamma (modelProjection S a) u hu)
        (Transport.line F gamma u ell) c)
    simpa only [Generic.toModelSquare, ModelGenericComparison.parametrizedToModelSquare,
      genericEvaluationSquare, genericEvaluation, ModelGenericComparison.genericEvaluation,
      ModelGenericComparison.genericBase, k] using
      ModelGenericComparison.rightSection_generic S a X (Transport.evaluation F gamma u)
        (Transport.evaluation_overC F gamma (modelProjection S a) u hu)
        (Transport.line F gamma u ell) c hc ha

/-- Both original rational sections are regular on every actual arc
meeting their original smooth domain densely.  The degree-two source
classification supplies exactly the two complete model alternatives. -/
theorem regular (S : Smoothing.StandardSource)
    (hU : Dense (gamma.val ⁻¹ᵁ F.smoothSquareOpen : Set Trait)) :
    Regular (SmoothFamily.rationalPair Q).leftRational gamma.val ∧
      Regular (SmoothFamily.rationalPair Q).rightRational gamma.val := by
  rcases degreeTwo_lineNormalForm S F (baseArc F gamma) (baseArc_dense F gamma hU) with h | h
  · obtain ⟨u, hu, _⟩ := h
    exact smooth_regular Q gamma u hu hU
  · obtain ⟨a, ha, _, u, hu, ⟨ell⟩⟩ := h
    exact nodal_regular Q gamma S a ha u hu ell hU

end Regularity

variable {g : VeryFreeContactConic Lines.P Lines.marking X}
variable {N : FullConicNeighborhood Lines.P Lines.marking X g}
variable {F : ProjectiveNodalFamily Lines.P Lines.marking
  X.variety X.contact.sequence.line 2}
variable (Q : FullHomComparison Lines.P Lines.marking X.variety N.homSpace N.neighborhood
  X.contact.sequence.line 2 F)

/-- The actual left moving-pair section has no pole on a formal arc. -/
theorem left_regular (S : Smoothing.StandardSource)
    (gamma : PointsOver Trait toC F.Square (F.squareToBase ≫ F.toC))
    (hU : Dense (gamma.val ⁻¹ᵁ F.smoothSquareOpen : Set Trait)) :
    Regular (SmoothFamily.rationalPair Q).leftRational gamma.val :=
  (regular Q gamma S hU).1

/-- The actual right moving-pair section has no pole on a formal arc. -/
theorem right_regular (S : Smoothing.StandardSource)
    (gamma : PointsOver Trait toC F.Square (F.squareToBase ≫ F.toC))
    (hU : Dense (gamma.val ⁻¹ᵁ F.smoothSquareOpen : Set Trait)) :
    Regular (SmoothFamily.rationalPair Q).rightRational gamma.val :=
  (regular Q gamma S hU).2

end LeBrunSalamon.Construction.FormalArcComparison

end
