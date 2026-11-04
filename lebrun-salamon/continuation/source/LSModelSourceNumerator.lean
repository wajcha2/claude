import LSModelDifferential
import LSRegularModelPair
import LSFamilyBaseChange
import LSModelSourceProductTransport

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

/-- Actual source-numerator specialization, before any density or
generic-fibre argument. -/
theorem sourceNumerator_pullback {T : Scheme} (f : T ⟶ ModelNumerator.Square F a) :
    pullSection f (modelSourceNumerator F a) ≫
      (compositionPullback f (modelSourceSquare F a) (ModelBivector.canonicalPair F a f)
        (canonicalPair_eq F a f)
        (externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf).hom =
      pullSection f (ModelNumerator.numerator F a) ≫ ModelDifferential.squareVelocity F a f := by
  have hadd {E : OModule (ModelNumerator.Square F a)} (s t : AlgebraicSection E) :
      pullSection f (s + t) = pullSection f s + pullSection f t := by
    simp only [pullSection, restrictSection, Functor.map_add, Preadditive.comp_add]
  unfold modelSourceNumerator
  rw [ModelNumerator.numerator, section_scale]
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Normalization.BundleGluing.pullSection_sub,
    hadd, Category.assoc, LogVelocity.pullSection_scalar]
  rw [sourceProduct_pullback, sourceProduct_pullback, sourceProduct_pullback]

def genericSourceNumerator : AlgebraicSection
    (pullbackModule (ModelBivector.canonicalPair F a (toModelSquare F a))
      (externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf) :=
  pullSection (toModelSquare F a) (modelSourceNumerator F a) ≫
    (compositionPullback (toModelSquare F a) (modelSourceSquare F a)
      (ModelBivector.canonicalPair F a (toModelSquare F a))
      (canonicalPair_eq F a (toModelSquare F a))
      (externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf).hom

end LeBrunSalamon.Construction.TraitContact.ModelGenericComparison

end
