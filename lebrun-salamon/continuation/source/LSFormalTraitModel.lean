import LSFormalTraitParameters

/-!
# Actual models over the complex power-series trait

The maps below retain the coefficient inclusion, residue evaluation,
and actual homogeneous conic coordinates. Generic classical source
normal forms are reviewed separately before their insertion here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseTwentyNine
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFour LeBrunSalamon.Skeleton

namespace LeBrunSalamon.StandardInputs

open LeBrunSalamon.Construction
open LeBrunSalamon.Construction.StableMaps
open LeBrunSalamon.Construction.StableMaps.FormalArcs

section FormalTraitModelName

-- Resolve this source model before the ambient Euclidean model with the same name.
local notation "Model" =>
  LeBrunSalamon.Construction.StableMaps.FormalArcs.Model

/-- Classical complete-trait form of a two-component genus-zero family:
choose two disjoint smooth sections through each special component,
use the fine moduli space Mbar_0,4 and its universal family, and use
triviality of a degree-zero line on a tree to identify the line bundle.
The actual smoothing element is retained, including its unit factor. -/
theorem _root_.LeBrunSalamon.PublishedInputs.Step3f.formalTrait_twoComponent_lineNormalForm
    (F : Smoothing.StandardSource) {C : Scheme} (pi : C ⟶ Trait)
    [IsProper pi] [Flat pi] [LocallyOfFinitePresentation pi]
    (hnodal : IsNodalCurve pi) (hprojective : IsProjectiveOver pi toC)
    (hsmooth : SmoothOfRelativeDimension 1 (pullback.snd pi genericPoint))
    (hgeom : GeometricallyIntegral (pullback.snd pi genericPoint))
    (L : LineBundle C)
    (i j : ProjectiveLine ⟶ pullback pi closedPoint)
    (p q : ProjectiveLinePoint Lines.P)
    (hi : IsClosedImmersion i) (hj : IsClosedImmersion j)
    (hiover : i ≫ pullback.snd pi closedPoint = Lines.P.structureMap)
    (hjover : j ≫ pullback.snd pi closedPoint = Lines.P.structureMap)
    (hpushout : IsPushout p.map q.map i j)
    (hidegree : projectiveLineDegree Lines.P Lines.marking
      (pullbackLine (i ≫ pullback.fst pi closedPoint) L) = 1)
    (hjdegree : projectiveLineDegree Lines.P Lines.marking
      (pullbackLine (j ≫ pullback.fst pi closedPoint) L) = 1) :
    ∃ a : Coefficients, a ≠ 0 ∧ PowerSeries.constantCoeff a = 0 ∧
      ∃ e : C ≅ Model F a,
        e.hom ≫ modelProjection F a = pi ∧
          Nonempty (L.sheaf ≅ pullbackModule e.hom (modelLine F a).sheaf) := by
  sorry

/-- Project-facing alias of the quarantined published complete-trait normal form. -/
theorem formalTrait_twoComponent_lineNormalForm
    (F : Smoothing.StandardSource) {C : Scheme} (pi : C ⟶ Trait)
    [IsProper pi] [Flat pi] [LocallyOfFinitePresentation pi]
    (hnodal : IsNodalCurve pi) (hprojective : IsProjectiveOver pi toC)
    (hsmooth : SmoothOfRelativeDimension 1 (pullback.snd pi genericPoint))
    (hgeom : GeometricallyIntegral (pullback.snd pi genericPoint))
    (L : LineBundle C)
    (i j : ProjectiveLine ⟶ pullback pi closedPoint)
    (p q : ProjectiveLinePoint Lines.P)
    (hi : IsClosedImmersion i) (hj : IsClosedImmersion j)
    (hiover : i ≫ pullback.snd pi closedPoint = Lines.P.structureMap)
    (hjover : j ≫ pullback.snd pi closedPoint = Lines.P.structureMap)
    (hpushout : IsPushout p.map q.map i j)
    (hidegree : projectiveLineDegree Lines.P Lines.marking
      (pullbackLine (i ≫ pullback.fst pi closedPoint) L) = 1)
    (hjdegree : projectiveLineDegree Lines.P Lines.marking
      (pullbackLine (j ≫ pullback.fst pi closedPoint) L) = 1) :
    ∃ a : Coefficients, a ≠ 0 ∧ PowerSeries.constantCoeff a = 0 ∧
      ∃ e : C ≅ Model F a,
        e.hom ≫ modelProjection F a = pi ∧
          Nonempty (L.sheaf ≅ pullbackModule e.hom (modelLine F a).sheaf) := by
  exact LeBrunSalamon.PublishedInputs.Step3f.formalTrait_twoComponent_lineNormalForm
    F pi hnodal hprojective hsmooth hgeom L i j p q hi hj hiover hjover hpushout
      hidegree hjdegree

end FormalTraitModelName

/-- The smooth special-fibre case: three disjoint smooth sections
trivialize the actual genus-zero family over the complete trait; the
line of degree two is the pullback of the actual O(2) tensor line. -/
theorem _root_.LeBrunSalamon.PublishedInputs.Step3f.formalTrait_smooth_lineNormalForm
    {C : Scheme} (pi : C ⟶ Trait)
    [IsProper pi] [Flat pi] [LocallyOfFinitePresentation pi]
    (hnodal : IsNodalCurve pi) (hprojective : IsProjectiveOver pi toC)
    (hsmooth : SmoothOfRelativeDimension 1 (pullback.snd pi genericPoint))
    (hgeom : GeometricallyIntegral (pullback.snd pi genericPoint))
    (L : LineBundle C)
    (i : ProjectiveLine ≅ pullback pi closedPoint)
    (hiover : i.hom ≫ pullback.snd pi closedPoint = Lines.P.structureMap)
    (hidegree : projectiveLineDegree Lines.P Lines.marking
      (pullbackLine (i.hom ≫ pullback.fst pi closedPoint) L) = 2) :
    ∃ e : C ≅ SmoothModel,
      e.hom ≫ smoothProjection = pi ∧
        Nonempty (L.sheaf ≅ pullbackModule e.hom smoothLine.sheaf) := by
  sorry

/-- Project-facing alias of the quarantined published smooth-trait normal form. -/
theorem formalTrait_smooth_lineNormalForm
    {C : Scheme} (pi : C ⟶ Trait)
    [IsProper pi] [Flat pi] [LocallyOfFinitePresentation pi]
    (hnodal : IsNodalCurve pi) (hprojective : IsProjectiveOver pi toC)
    (hsmooth : SmoothOfRelativeDimension 1 (pullback.snd pi genericPoint))
    (hgeom : GeometricallyIntegral (pullback.snd pi genericPoint))
    (L : LineBundle C)
    (i : ProjectiveLine ≅ pullback pi closedPoint)
    (hiover : i.hom ≫ pullback.snd pi closedPoint = Lines.P.structureMap)
    (hidegree : projectiveLineDegree Lines.P Lines.marking
      (pullbackLine (i.hom ≫ pullback.fst pi closedPoint) L) = 2) :
    ∃ e : C ≅ SmoothModel,
      e.hom ≫ smoothProjection = pi ∧
        Nonempty (L.sheaf ≅ pullbackModule e.hom smoothLine.sheaf) := by
  exact LeBrunSalamon.PublishedInputs.Step3f.formalTrait_smooth_lineNormalForm
    pi hnodal hprojective hsmooth hgeom L i hiover hidegree

end LeBrunSalamon.StandardInputs

end
