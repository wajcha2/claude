import LSModelGenericParametrization
import LSModelGenericNormalization

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


private theorem parametrized_generic_pair (ha : a ≠ 0) :
    parametrizedToGenericSquare F a ha ≫
      ModelBivector.canonicalPair F a (toModelSquare F a) =
        Parametrized.sourceSquare Lines.P genericBase := by
  rw [← canonicalPair_eq, ← Category.assoc, parametrizedToModelSquare_factor,
    parametrizedToModelSquare_source]

private theorem model_numerator_restrict {T : Scheme}
    (j : T ⟶ Square F a) (q : T ⟶ ModelNumerator.Square F a)
    (x : T ⟶ SelfProduct Lines.P.structureMap)
    (hq : j ≫ toModelSquare F a = q)
    (hx : j ≫ ModelBivector.canonicalPair F a (toModelSquare F a) = x)
    (hx' : q ≫ modelSourceSquare F a = x) :
    pullSection j (genericSourceNumerator F a) ≫
      (compositionPullback j (ModelBivector.canonicalPair F a (toModelSquare F a))
        x hx
        (externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf).hom =
      pullSection q (modelSourceNumerator F a) ≫
        (compositionPullback q (modelSourceSquare F a) x hx'
          (externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf).hom := by
  exact LogVelocity.section_comp
    (E := (externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf)
    j (toModelSquare F a) (modelSourceSquare F a)
    (ModelBivector.canonicalPair F a (toModelSquare F a))
    (genericSourceNumerator._proof_1 F a) q hq x hx hx' (modelSourceNumerator F a)

private theorem scalar_section_restrict {T Y Z : Scheme}
    (j : T ⟶ Y) (c : Y ⟶ Z) (x : T ⟶ Z) (hx : j ≫ c = x)
    {E : OModule Z} (r : RingSections Y ⊤) (s : AlgebraicSection E) :
    pullSection j (scalarSection r ≫ pullSection c s) ≫
      (compositionPullback j c x hx E).hom =
        scalarSection (j.appTop r) ≫ pullSection x s := by
  rw [LogVelocity.pullSection_scalar j r (pullSection c s), Category.assoc]
  exact congrArg (fun t : AlgebraicSection (pullbackModule x E) =>
    scalarSection (j.appTop r) ≫ t) (compositionPullback_sections j c x hx s)

private theorem pull_comp_section_eq {T Y Z : Scheme}
    (j : T ⟶ Y) (c : Y ⟶ Z) (x : T ⟶ Z) (h : j ≫ c = x)
    (E : OModule Z) (s t : AlgebraicSection (pullbackModule c E)) (hst : s = t) :
    pullSection j s ≫ (compositionPullback j c x h E).hom =
      pullSection j t ≫ (compositionPullback j c x h E).hom := by
  exact congrArg (fun v : AlgebraicSection (pullbackModule c E) =>
    pullSection j v ≫ (compositionPullback j c x h E).hom) hst

private theorem scalar_section_comp_eq {T : Scheme} (E : OModule T)
    (r r' : RingSections T ⊤) (h : r = r') (s : AlgebraicSection E) :
    scalarSection r ≫ s = scalarSection r' ≫ s := by
  cases h
  rfl

private theorem parametrized_numerator_restriction (ha : a ≠ 0) :
    pullSection (parametrizedToGenericSquare F a ha) (genericSourceNumerator F a) ≫ (compositionPullback (parametrizedToGenericSquare F a ha) (ModelBivector.canonicalPair F a (toModelSquare F a)) (Parametrized.sourceSquare Lines.P genericBase) (parametrized_generic_pair F a ha) ((externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf)).hom = pullSection (parametrizedToModelSquare F a ha) (modelSourceNumerator F a) ≫
      (compositionPullback (parametrizedToModelSquare F a ha) (modelSourceSquare F a) (Parametrized.sourceSquare Lines.P genericBase) (parametrizedToModelSquare_source F a ha) ((externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf)).hom := by
  exact model_numerator_restrict F a (parametrizedToGenericSquare F a ha) (parametrizedToModelSquare F a ha) (Parametrized.sourceSquare Lines.P genericBase)
    (parametrizedToModelSquare_factor F a ha) (parametrized_generic_pair F a ha) (parametrizedToModelSquare_source F a ha)

private theorem parametrized_source_equality (ha : a ≠ 0) :
    pullSection (parametrizedToGenericSquare F a ha) (genericSourceNumerator F a) ≫ (compositionPullback (parametrizedToGenericSquare F a ha) (ModelBivector.canonicalPair F a (toModelSquare F a)) (Parametrized.sourceSquare Lines.P genericBase) (parametrized_generic_pair F a ha) ((externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf)).hom = pullSection (parametrizedToGenericSquare F a ha) (scalarSection ((toModelSquare F a ≫ ModelNumerator.squareProjection F a).appTop (coefficientSection a)) ≫ pullSection (ModelBivector.canonicalPair F a (toModelSquare F a)) (sourceBivector Lines.P)) ≫ (compositionPullback (parametrizedToGenericSquare F a ha) (ModelBivector.canonicalPair F a (toModelSquare F a)) (Parametrized.sourceSquare Lines.P genericBase) (parametrized_generic_pair F a ha) ((externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf)).hom := by
  exact pull_comp_section_eq (parametrizedToGenericSquare F a ha) (ModelBivector.canonicalPair F a (toModelSquare F a)) (Parametrized.sourceSquare Lines.P genericBase) (parametrized_generic_pair F a ha) ((externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf)
    (genericSourceNumerator F a) (scalarSection ((toModelSquare F a ≫ ModelNumerator.squareProjection F a).appTop (coefficientSection a)) ≫ pullSection (ModelBivector.canonicalPair F a (toModelSquare F a)) (sourceBivector Lines.P))
    (genericSourceNumerator_eq F a ha)

private theorem parametrized_scalar_restriction (ha : a ≠ 0) :
    pullSection (parametrizedToGenericSquare F a ha) (scalarSection ((toModelSquare F a ≫ ModelNumerator.squareProjection F a).appTop (coefficientSection a)) ≫ pullSection (ModelBivector.canonicalPair F a (toModelSquare F a)) (sourceBivector Lines.P)) ≫ (compositionPullback (parametrizedToGenericSquare F a ha) (ModelBivector.canonicalPair F a (toModelSquare F a)) (Parametrized.sourceSquare Lines.P genericBase) (parametrized_generic_pair F a ha) ((externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf)).hom = scalarSection ((parametrizedToGenericSquare F a ha).appTop ((toModelSquare F a ≫ ModelNumerator.squareProjection F a).appTop (coefficientSection a))) ≫ pullSection (Parametrized.sourceSquare Lines.P genericBase) (sourceBivector Lines.P) := by
  exact scalar_section_restrict (E := (externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf) (parametrizedToGenericSquare F a ha) (ModelBivector.canonicalPair F a (toModelSquare F a)) (Parametrized.sourceSquare Lines.P genericBase) (parametrized_generic_pair F a ha)
    ((toModelSquare F a ≫ ModelNumerator.squareProjection F a).appTop (coefficientSection a)) (sourceBivector Lines.P)

private theorem parametrized_coefficient (ha : a ≠ 0) :
    (parametrizedToGenericSquare F a ha).appTop ((toModelSquare F a ≫ ModelNumerator.squareProjection F a).appTop (coefficientSection a)) = genericCoefficient F a ha := by
  change (((parametrizedToGenericSquare F a ha) ≫ toModelSquare F a) ≫ ModelNumerator.squareProjection F a).appTop
    (coefficientSection a) = _
  rw [parametrizedToModelSquare_factor]
  rfl

private theorem parametrized_scalar_coefficient (ha : a ≠ 0) :
    scalarSection ((parametrizedToGenericSquare F a ha).appTop ((toModelSquare F a ≫ ModelNumerator.squareProjection F a).appTop (coefficientSection a))) ≫ pullSection (Parametrized.sourceSquare Lines.P genericBase) (sourceBivector Lines.P) = scalarSection (genericCoefficient F a ha) ≫ pullSection (Parametrized.sourceSquare Lines.P genericBase) (sourceBivector Lines.P) := by
  exact scalar_section_comp_eq (pullbackModule (Parametrized.sourceSquare Lines.P genericBase) ((externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf))
    ((parametrizedToGenericSquare F a ha).appTop ((toModelSquare F a ≫ ModelNumerator.squareProjection F a).appTop (coefficientSection a))) (genericCoefficient F a ha)
    (parametrized_coefficient F a ha) (pullSection (Parametrized.sourceSquare Lines.P genericBase) (sourceBivector Lines.P))

private theorem parametrized_source_normalization (ha : a ≠ 0) :
    pullSection (parametrizedToModelSquare F a ha) (modelSourceNumerator F a) ≫
      (compositionPullback (parametrizedToModelSquare F a ha) (modelSourceSquare F a) (Parametrized.sourceSquare Lines.P genericBase) (parametrizedToModelSquare_source F a ha) ((externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf)).hom = scalarSection (genericCoefficient F a ha) ≫ pullSection (Parametrized.sourceSquare Lines.P genericBase) (sourceBivector Lines.P) := by
  exact (parametrized_numerator_restriction F a ha).symm.trans
    ((parametrized_source_equality F a ha).trans
      ((parametrized_scalar_restriction F a ha).trans
        (parametrized_scalar_coefficient F a ha)))
end LeBrunSalamon.Construction.TraitContact.ModelGenericComparison

end
