import LSStableMapFamily

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

namespace LeBrunSalamon.Construction.StableMaps.FormalArcs

abbrev Coefficients := PowerSeries ℂ
abbrev GenericPoint : Scheme := Spec (CommRingCat.of (FractionRing Coefficients))

def genericPoint : GenericPoint ⟶ Trait :=
  Spec.map (CommRingCat.ofHom (algebraMap Coefficients (FractionRing Coefficients)))

def parameterMap (a : Coefficients) : Trait ⟶ Smoothing.AffineLine :=
  Spec.map (CommRingCat.ofHom
    (Polynomial.eval₂RingHom (PowerSeries.C : ℂ →+* Coefficients) a))

abbrev Model (F : Smoothing.StandardSource) (a : Coefficients) :=
  Smoothing.SourceOver F (parameterMap a)

def modelProjection (F : Smoothing.StandardSource) (a : Coefficients) :
    Model F a ⟶ Trait := pullback.snd F.parameter (parameterMap a)

def modelLeft (F : Smoothing.StandardSource) (a : Coefficients) :
    Model F a ⟶ ProjectiveLine :=
  pullback.fst F.parameter (parameterMap a) ≫ F.left

def modelRight (F : Smoothing.StandardSource) (a : Coefficients) :
    Model F a ⟶ ProjectiveLine :=
  pullback.fst F.parameter (parameterMap a) ≫ F.right

def modelLine (F : Smoothing.StandardSource) (a : Coefficients) :
    LineBundle (Model F a) :=
  tensorLine
    (pullbackLine (modelLeft F a) (projectiveCoordinates 1).hyperplane)
    (pullbackLine (modelRight F a) (projectiveCoordinates 1).hyperplane)

abbrev SmoothModel := RationalSourceOver Lines.P Trait toC

def smoothProjection : SmoothModel ⟶ Trait :=
  pullback.snd Lines.P.structureMap toC

def smoothLine : LineBundle SmoothModel :=
  pullbackLine (pullback.fst Lines.P.structureMap toC)
    (tensorLine (projectiveCoordinates 1).hyperplane
      (projectiveCoordinates 1).hyperplane)

end LeBrunSalamon.Construction.StableMaps.FormalArcs

namespace LeBrunSalamon.Construction.StableMaps.FormalArcs

@[reassoc] theorem parameterMap_toC (a : Coefficients) :
    parameterMap a ≫ Smoothing.affineLineToC = toC := by
  rw [parameterMap, Smoothing.affineLineToC, toC, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext c
  simp

@[reassoc] theorem closedPoint_parameterMap (a : Coefficients) :
    closedPoint ≫ parameterMap a =
      Smoothing.scalarPoint (PowerSeries.constantCoeff a) := by
  rw [closedPoint, parameterMap, Smoothing.scalarPoint, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    simp
  · simp

def coefficientSection (a : Coefficients) : RingSections Trait ⊤ :=
  (Scheme.ΓSpecIso (CommRingCat.of Coefficients)).inv a

theorem parameterMap_parameter (a : Coefficients) :
    (parameterMap a).appTop Smoothing.parameterFunction = coefficientSection a := by
  let phi : CommRingCat.of (Polynomial ℂ) ⟶ CommRingCat.of Coefficients :=
    CommRingCat.ofHom
      (Polynomial.eval₂RingHom (PowerSeries.C : ℂ →+* Coefficients) a)
  have h := (congrArg
    (fun k : CommRingCat.of (Polynomial ℂ) ⟶
      Trait.presheaf.obj (Opposite.op ⊤) => k Polynomial.X)
    (Scheme.ΓSpecIso_inv_naturality phi)).symm
  change (parameterMap a).appTop Smoothing.parameterFunction =
    (Scheme.ΓSpecIso (CommRingCat.of Coefficients)).inv (phi Polynomial.X) at h
  simpa [phi, coefficientSection] using h

@[reassoc] theorem modelLeft_toC (F : Smoothing.StandardSource) (a : Coefficients) :
    modelLeft F a ≫ Lines.P.structureMap = modelProjection F a ≫ toC := by
  dsimp [modelLeft, modelProjection]
  rw [Category.assoc, F.left_over, ← Category.assoc, pullback.condition,
    Category.assoc, parameterMap_toC]

@[reassoc] theorem modelRight_toC (F : Smoothing.StandardSource) (a : Coefficients) :
    modelRight F a ≫ Lines.P.structureMap = modelProjection F a ≫ toC := by
  dsimp [modelRight, modelProjection]
  rw [Category.assoc, F.right_over, ← Category.assoc, pullback.condition,
    Category.assoc, parameterMap_toC]

end LeBrunSalamon.Construction.StableMaps.FormalArcs

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
