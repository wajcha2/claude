import LSModelSourceNumerator
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

private theorem scalar_pullSection_comp {T Y Z : Scheme}
    (j : T ⟶ Y) (c : Y ⟶ Z) (c' : T ⟶ Z) (hcc : j ≫ c = c')
    {E : OModule Z} (r : RingSections Y ⊤) (s : AlgebraicSection E) :
    pullSection j (scalarSection r ≫ pullSection c s) ≫
      (compositionPullback j c c' hcc E).hom =
        scalarSection (j.appTop r) ≫ pullSection c' s := by
  rw [LogVelocity.pullSection_scalar j r (pullSection c s), Category.assoc]
  exact congrArg (fun t : AlgebraicSection (pullbackModule c' E) =>
    scalarSection (j.appTop r) ≫ t) (compositionPullback_sections j c c' hcc s)

private theorem genericSourceNumerator_restrict {T : Scheme} (j : T ⟶ Square F a) :
    pullSection j (genericSourceNumerator F a) ≫
      (compositionPullback j (ModelBivector.canonicalPair F a (toModelSquare F a))
        (ModelBivector.canonicalPair F a (j ≫ toModelSquare F a))
        (canonicalPair_comp F a j (toModelSquare F a))
        (externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf).hom =
      pullSection (j ≫ toModelSquare F a) (modelSourceNumerator F a) ≫
        (compositionPullback (j ≫ toModelSquare F a) (modelSourceSquare F a)
          (ModelBivector.canonicalPair F a (j ≫ toModelSquare F a))
          (canonicalPair_eq F a (j ≫ toModelSquare F a))
          (externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf).hom := by
  exact LogVelocity.section_comp j (toModelSquare F a) (modelSourceSquare F a)
    (ModelBivector.canonicalPair F a (toModelSquare F a))
    (genericSourceNumerator._proof_1 F a) (j ≫ toModelSquare F a) rfl
    (ModelBivector.canonicalPair F a (j ≫ toModelSquare F a))
    (canonicalPair_comp F a j (toModelSquare F a))
    (canonicalPair_eq F a (j ≫ toModelSquare F a)) (modelSourceNumerator F a)

private theorem genericSourceBivector_restrict {T : Scheme} (j : T ⟶ Square F a) :
    pullSection j
      (scalarSection ((toModelSquare F a ≫ ModelNumerator.squareProjection F a).appTop
        (coefficientSection a)) ≫
        pullSection (ModelBivector.canonicalPair F a (toModelSquare F a)) (sourceBivector Lines.P)) ≫
      (compositionPullback j (ModelBivector.canonicalPair F a (toModelSquare F a))
        (ModelBivector.canonicalPair F a (j ≫ toModelSquare F a))
        (canonicalPair_comp F a j (toModelSquare F a))
        (externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf).hom =
      scalarSection (((j ≫ toModelSquare F a) ≫ ModelNumerator.squareProjection F a).appTop
        (coefficientSection a)) ≫
        pullSection (ModelBivector.canonicalPair F a (j ≫ toModelSquare F a)) (sourceBivector Lines.P) := by
  have h := scalar_pullSection_comp
    (E := (externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf) j
    (ModelBivector.canonicalPair F a (toModelSquare F a))
    (ModelBivector.canonicalPair F a (j ≫ toModelSquare F a))
    (canonicalPair_comp F a j (toModelSquare F a))
    ((toModelSquare F a ≫ ModelNumerator.squareProjection F a).appTop (coefficientSection a))
    (sourceBivector Lines.P)
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using h


/-- Equality on the dense affine node test extends to the complete
generic square because the actual target is a line bundle and the
generic square is integral. -/
theorem genericSourceNumerator_eq (ha : a ≠ 0) :
    genericSourceNumerator F a =
      scalarSection ((toModelSquare F a ≫ ModelNumerator.squareProjection F a).appTop
        (coefficientSection a)) ≫
      pullSection (ModelBivector.canonicalPair F a (toModelSquare F a)) (sourceBivector Lines.P) := by
  letI : IsIntegral (Square F a) := square_integral F a ha
  obtain ⟨T, j, hT, hj, u, v, w, z, hu, hv, hw, hz⟩ := denseNodeTest_exists F a ha
  letI := hT
  let E := externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine
  let c := ModelBivector.canonicalPair F a (toModelSquare F a)
  let c' := ModelBivector.canonicalPair F a (j ≫ toModelSquare F a)
  let hcc := canonicalPair_comp F a j (toModelSquare F a)
  apply dominant_pullSection_injective j hj (fun _ => inferInstance) (pullbackLine c E)
  apply (cancel_mono (compositionPullback j c c' hcc E.sheaf).hom).mp
  exact (genericSourceNumerator_restrict F a j).trans
    ((sourceNumerator_pullback F a (j ≫ toModelSquare F a)).trans
      ((ModelDifferential.numerator_sourceBivector_denominatorCleared F a
        (j ≫ toModelSquare F a) u v w z hu hv hw hz).trans
        (genericSourceBivector_restrict F a j).symm))

private theorem pullSection_comp_proof_irrel {T Y Z : Scheme}
    (f : T ⟶ Y) (g : Y ⟶ Z) (h : T ⟶ Z) (e e' : f ≫ g = h)
    {E : OModule Z} (s : AlgebraicSection (pullbackModule g E)) :
    pullSection f s ≫ (compositionPullback f g h e E).hom =
      pullSection f s ≫ (compositionPullback f g h e' E).hom := rfl

private theorem genericSourceNumerator_from_canonical :
    pullSection (toModelSquare F a) (modelSourceNumerator F a) ≫
      (compositionPullback (toModelSquare F a) (modelSourceSquare F a)
        (ModelBivector.canonicalPair F a (toModelSquare F a))
        (canonicalPair_eq F a (toModelSquare F a))
        (externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf).hom =
      genericSourceNumerator F a := by
  exact pullSection_comp_proof_irrel (toModelSquare F a) (modelSourceSquare F a)
    (ModelBivector.canonicalPair F a (toModelSquare F a))
    (canonicalPair_eq F a (toModelSquare F a)) (genericSourceNumerator._proof_1 F a)
    (E := (externalSquareLine Lines.P.structureMap SourceBivectorCoordinates.TangentLine).sheaf)
    (modelSourceNumerator F a)


/-- The two actual logarithmic source differentials send the global
numerator to a times the original normalized source bivector on the
entire smooth generic square. -/
theorem generic_source_denominatorCleared (ha : a ≠ 0) :
    pullSection (toModelSquare F a) (ModelNumerator.numerator F a) ≫
      ModelDifferential.squareVelocity F a (toModelSquare F a) =
      scalarSection ((toModelSquare F a ≫ ModelNumerator.squareProjection F a).appTop
        (coefficientSection a)) ≫
      pullSection (ModelBivector.canonicalPair F a (toModelSquare F a)) (sourceBivector Lines.P) := by
  exact (sourceNumerator_pullback F a (toModelSquare F a)).symm.trans
    ((genericSourceNumerator_from_canonical F a).trans (genericSourceNumerator_eq F a ha))

theorem genericParameter_isUnit (ha : a ≠ 0) :
    IsUnit ((toModelSquare F a ≫ ModelNumerator.squareProjection F a).appTop (coefficientSection a)) :=
  ModelBivector.parameter_isUnit_of_generic a ha
    (toModelSquare F a ≫ ModelNumerator.squareProjection F a) (squareBase F a)
    (toModelSquare_base F a).symm

/-- Exact normalized equality on the complete generic square, retaining
both outer endpoints and the diagonal. -/
theorem generic_source_normalized (ha : a ≠ 0) :
    scalarSection (↑(genericParameter_isUnit F a ha).unit⁻¹ : RingSections (Square F a) ⊤) ≫
      pullSection (toModelSquare F a) (ModelNumerator.numerator F a) ≫
        ModelDifferential.squareVelocity F a (toModelSquare F a) =
      pullSection (ModelBivector.canonicalPair F a (toModelSquare F a)) (sourceBivector Lines.P) := by
  rw [generic_source_denominatorCleared F a ha, ← Category.assoc, ← scalarSection_mul,
    (genericParameter_isUnit F a ha).val_inv_mul, scalarSection_one, Category.id_comp]

end LeBrunSalamon.Construction.TraitContact.ModelGenericComparison

end
