import LSFormalTraitParameters
import LSStandardConicZeroComparison

/-! Specialize the proved all-test conic presentation to the original
power-series parameter map. This retains the literal Model, projection,
and selected modelLine used by the original formal-trait statements.
No family classification or new admission occurs here. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton
open LeBrunSalamon.Construction LeBrunSalamon.Construction.Smoothing
open LeBrunSalamon.Construction.StableMaps.FormalArcs

namespace LeBrunSalamon.FormalTraitSourceComparison

local notation "Model" => LeBrunSalamon.Construction.StableMaps.FormalArcs.Model

variable (F : StandardSource) (a : Coefficients)

def iso : Model F a ≅ PlaneQuadratic.ZeroScheme Coefficients
    (PlaneQuadratic.split Coefficients a) :=
  StandardConicZeroComparison.iso Coefficients F (parameterMap a) a
    (parameterMap_parameter a)

@[reassoc] theorem over_base :
    (iso F a).hom ≫ PlaneQuadratic.projection Coefficients
      (PlaneQuadratic.split Coefficients a) = modelProjection F a :=
  StandardConicZeroComparison.iso_over Coefficients F (parameterMap a) a
    (parameterMap_parameter a)

def lineIso : (modelLine F a).sheaf ≅ pullbackModule (iso F a).hom
    (pullbackLine (PlaneQuadratic.inclusion Coefficients
      (PlaneQuadratic.split Coefficients a))
      (StandardTautological.line Coefficients 2)).sheaf :=
  StandardConicZeroComparison.lineIso Coefficients F (parameterMap a) a
    (parameterMap_parameter a)

/-- Exact interface used to assemble the original two-component trait
normal form after its primitive quadratic and normal-form matrix are proved. -/
theorem model_quadratic_comparison :
    ∃ e : Model F a ≅ PlaneQuadratic.ZeroScheme Coefficients
        (PlaneQuadratic.split Coefficients a),
      e.hom ≫ PlaneQuadratic.projection Coefficients
          (PlaneQuadratic.split Coefficients a) = modelProjection F a ∧
      Nonempty ((modelLine F a).sheaf ≅ pullbackModule e.hom
        (pullbackLine (PlaneQuadratic.inclusion Coefficients
          (PlaneQuadratic.split Coefficients a))
          (StandardTautological.line Coefficients 2)).sheaf) :=
  ⟨iso F a, over_base F a, ⟨lineIso F a⟩⟩

end LeBrunSalamon.FormalTraitSourceComparison
end
