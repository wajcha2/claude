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

end
