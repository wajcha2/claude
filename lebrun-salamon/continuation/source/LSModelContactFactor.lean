import LSModelGenericParametrization
import LSModelTensorScalar

/-!
# Whole-generic-square comparison for the actual conic model

The dense test used below is the residue-field point of the integral
generic square.  The final equalities are on the complete square,
including the diagonal and both outer endpoints.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirty
open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction.TraitContact.ModelGenericComparison

local notation "Model" => LeBrunSalamon.Construction.StableMaps.FormalArcs.Model

open StableMaps.FormalArcs StableMaps.FormalArcs.ModelGeometry
open Smoothing.CoordinateCharts Smoothing.SourceAffineCharts
open FamilyBivectors

variable (F : Smoothing.StandardSource) (a : Coefficients)

variable {d : ℕ} (X : SmoothProperComplexVariety d)
variable (e : Model F a ⟶ X.scheme)
variable (he : e ≫ X.structureMap = modelProjection F a ≫ toC)

section Contact

variable {n : ℕ} (Y : ContactFanoManifold n)
variable (f : Model F a ⟶ Y.variety.scheme)
variable (hf : f ≫ Y.variety.structureMap = modelProjection F a ≫ toC)
variable (ell : (modelLine F a).sheaf ≅ pullbackModule f Y.contact.sequence.line.sheaf)
variable (c : Coefficients)

def genericDividedContact (ha : a ≠ 0) :
    pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule (genericEvaluation F a Y.variety f ha) Y.contact.sequence.line.sheaf :=
  (Scheme.Modules.pullback (genericParametrization F a ha)).map
    (RegularModel.dividedContact Y F a f ell c) ≫
      (compositionPullback (genericParametrization F a ha) f
        (genericEvaluation F a Y.variety f ha) rfl Y.contact.sequence.line.sheaf).hom

variable (hc : ContactScalar.morphism Y F a f hf =
  GlobalScalars.scalarEnd (modelLine F a).sheaf
    ((modelProjection F a).appTop (coefficientSection a)) ≫
      RegularModel.dividedContact Y F a f ell c)

include hc in
/-- The one divided contact factor is exactly the original contact
velocity divided by the smoothing element on the generic fibre. -/
theorem genericContact_factor (ha : a ≠ 0) :
    genericSourceVelocity F a ha ≫
      ParametrizedContact.velocity Lines.P genericBase Y
        (genericEvaluation F a Y.variety f ha) (genericEvaluation_over F a Y.variety f hf ha) =
      GlobalScalars.scalarEnd
        (pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf)
        (p1Parameter.appTop (genericBaseCoefficient a)) ≫
          genericDividedContact F a Y f ell c ha := by
  rw [ParametrizedContact.velocity, ← Category.assoc, ← genericVelocity_factor]
  rw [Category.assoc, ← Normalization.BundleGluing.compositionPullback_naturality,
    ← Category.assoc, ← Functor.map_comp]
  change (Scheme.Modules.pullback (genericParametrization F a ha)).map
      (ContactScalar.morphism Y F a f hf) ≫
        (compositionPullback (genericParametrization F a ha) f
          (genericEvaluation F a Y.variety f ha) rfl Y.contact.sequence.line.sheaf).hom = _
  rw [hc, Functor.map_comp, LineEndomorphisms.scalarEnd_pullback]
  have hcoef : (genericParametrization F a ha).appTop
      ((modelProjection F a).appTop (coefficientSection a)) =
      p1Parameter.appTop (genericBaseCoefficient a) := by
    change (genericParametrization F a ha ≫ modelProjection F a).appTop
      (coefficientSection a) = _
    rw [genericParametrization_parameter]
    rfl
  rw [hcoef]
  rfl

end Contact

end LeBrunSalamon.Construction.TraitContact.ModelGenericComparison

end
