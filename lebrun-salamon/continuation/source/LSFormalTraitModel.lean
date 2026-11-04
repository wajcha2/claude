import LSFormalTraitParameters
import LSSmoothTraitNormalForm
import LSNodalTraitNormalForm

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

/-- The actual two-component trait normal form. The original chosen line
constructs a relative plane conic; the precise generic quadratic normal
form and explicit coordinate changes identify the given standard model.
The complete smoothing element, including its unit factor, is retained. -/
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
  letI : IsClosedImmersion i := hi
  letI : IsClosedImmersion j := hj
  letI : SmoothOfRelativeDimension 1 (pullback.snd pi genericPoint) := hsmooth
  letI : Smooth (pullback.snd pi genericPoint) :=
    SmoothOfRelativeDimension.smooth (n := 1) _
  exact LeBrunSalamon.NodalTraitNormalForm.exists_model
    F pi L i j p q hiover hjover hpushout hidegree hjdegree

/-- Project-facing alias of the constructed two-component trait normal form. -/
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

/-- The smooth special-fibre case, proved by constructing the primitive
relative quadratic, normalizing its actual coefficients, and transporting
the original degree-two line through the polarized Veronese comparison. -/
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
  exact LeBrunSalamon.SmoothTraitNormalForm.exists_model pi L i hiover hidegree

/-- Project-facing alias of the constructed smooth-trait normal form. -/
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
