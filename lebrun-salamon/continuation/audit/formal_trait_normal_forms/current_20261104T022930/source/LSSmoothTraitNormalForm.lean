import LSFormalTraitParameters
import LSTraitQuadraticPresentation
import LSFormalQuadraticConditions
import LSQuadraticPolarizedModels

/-! The actual smooth formal-trait normal form, assembled from the
primitive quadratic presentation, its exact published algebraic normal
form, and the explicit polarized Veronese comparison. No family
isomorphism or chosen-line transport is admitted. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.Construction.StableMaps.FormalArcs

namespace LeBrunSalamon.SmoothTraitNormalForm

theorem exists_model
    {X : Scheme.{0}} (pi : X ⟶ Trait) [IsProper pi] [Flat pi]
    (L : LineBundle X) (i : ProjectiveLine ≅ pullback pi closedPoint)
    (hi : i.hom ≫ pullback.snd pi closedPoint = Lines.P.structureMap)
    (hdegree : projectiveLineDegree Lines.P Lines.marking
      (pullbackLine (i.hom ≫ pullback.fst pi closedPoint) L) = 2) :
    ∃ e : X ≅ SmoothModel,
      e.hom ≫ smoothProjection = pi ∧
        Nonempty (L.sheaf ≅ pullbackModule e.hom smoothLine.sheaf) := by
  obtain ⟨q, hq, e, he, ⟨eL⟩⟩ := smooth_quadratic_equation pi L i hi hdegree
  have hs := FormalQuadraticConditions.smooth_residue_of_rational_fibre pi q e he i hi
  obtain ⟨M, hM⟩ := FormalQuadraticConditions.smooth_normal_form q hq hs
  let family : PolarizedOverIso pi (PlaneQuadratic.projection Coefficients q)
      L (QuadraticPolarizedModels.line Coefficients q) := ⟨e, he, eL⟩
  obtain ⟨model⟩ := QuadraticPolarizedModels.smooth_model_to_quadratic Coefficients q M hM
  let actualModel : PolarizedOverIso smoothProjection (PlaneQuadratic.projection Coefficients q)
      smoothLine (QuadraticPolarizedModels.line Coefficients q) := model
  exact (family.trans actualModel.symm).exists_iso

end LeBrunSalamon.SmoothTraitNormalForm
end
