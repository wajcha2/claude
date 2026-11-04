import LSModelBivector
import LSContactLineTests
import LSGenericGlobalFunctions

/-!
# The actual generic conic and its projective-line projection

The nonzero smoothing element factors the fixed fraction-field point
through the punctured parameter line.  The already constructed universal
conic trivialization then supplies an actual normalized projective-line
identification, with both projections recorded.  No abstract replacement
of the generic curve is used.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton

namespace LeBrunSalamon.Construction.StableMaps.FormalArcs.ModelGeometry

open Smoothing TraitContact

variable (F : StandardSource) (a : Coefficients) (ha : a ≠ 0)

include ha in
theorem genericParameter_isUnit :
    IsUnit ((genericPoint ≫ parameterMap a).appTop parameterFunction) := by
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    parameterMap_parameter] using ModelBivector.genericPoint_parameter_isUnit a ha

include ha in
theorem genericParameter_range :
    Set.range (genericPoint ≫ parameterMap a) ⊆ Set.range puncturedParameter.ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  have h : (genericPoint ≫ parameterMap a) ⁻¹ᵁ puncturedParameter = ⊤ := by
    rw [puncturedParameter, Scheme.preimage_basicOpen_top]
    exact GenericPoint.basicOpen_of_isUnit (genericParameter_isUnit a ha)
  change x ∈ (genericPoint ≫ parameterMap a) ⁻¹ᵁ puncturedParameter
  rw [h]
  trivial

def genericToPunctured : GenericPoint ⟶ puncturedParameter.toScheme :=
  IsOpenImmersion.lift puncturedParameter.ι (genericPoint ≫ parameterMap a)
    (genericParameter_range a ha)

@[reassoc] theorem genericToPunctured_parameter :
    genericToPunctured a ha ≫ puncturedParameter.ι = genericPoint ≫ parameterMap a :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc] theorem genericToPunctured_toC :
    genericToPunctured a ha ≫ PuncturedSourceProof.baseMap = genericPoint ≫ toC := by
  rw [PuncturedSourceProof.baseMap, ← Category.assoc,
    genericToPunctured_parameter, Category.assoc, parameterMap_toC]

abbrev GenericModel := pullback (modelProjection F a) genericPoint

abbrev genericProjection : GenericModel F a ⟶ GenericPoint :=
  pullback.snd (modelProjection F a) genericPoint

def genericLeft : GenericModel F a ⟶ ProjectiveLine :=
  pullback.fst (modelProjection F a) genericPoint ≫ modelLeft F a

def toPuncturedModel : GenericModel F a ⟶ PuncturedSourceProof.Star F :=
  pullback.lift
    (pullback.fst (modelProjection F a) genericPoint ≫
      pullback.fst F.parameter (parameterMap a))
    (genericProjection F a ≫ genericToPunctured a ha) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      change (pullback.fst (modelProjection F a) genericPoint ≫
        modelProjection F a) ≫ parameterMap a =
          (genericProjection F a ≫ genericToPunctured a ha) ≫ puncturedParameter.ι
      rw [pullback.condition]
      simp only [genericProjection, Category.assoc, genericToPunctured_parameter])

@[reassoc] theorem toPuncturedModel_source :
    toPuncturedModel F a ha ≫ pullback.fst F.parameter puncturedParameter.ι =
      pullback.fst (modelProjection F a) genericPoint ≫
        pullback.fst F.parameter (parameterMap a) :=
  pullback.lift_fst _ _ _

@[reassoc] theorem toPuncturedModel_base :
    toPuncturedModel F a ha ≫ PuncturedSourceProof.starBase F =
      genericProjection F a ≫ genericToPunctured a ha :=
  pullback.lift_snd _ _ _

theorem toPuncturedModel_isPullback :
    IsPullback (toPuncturedModel F a ha) (genericProjection F a)
      (PuncturedSourceProof.starBase F) (genericToPunctured a ha) := by
  apply IsPullback.of_right
    (t := IsPullback.of_hasPullback F.parameter puncturedParameter.ι)
  · simpa only [toPuncturedModel_source, genericToPunctured_parameter,
      modelProjection, genericProjection] using
      (IsPullback.of_hasPullback (modelProjection F a) genericPoint).paste_horiz
        (IsPullback.of_hasPullback F.parameter (parameterMap a))
  · exact toPuncturedModel_base F a ha

def toPuncturedProduct : GenericModel F a ⟶ PuncturedSourceProof.Product :=
  toPuncturedModel F a ha ≫ (PuncturedSourceProof.trivialization F).hom

@[reassoc] theorem toPuncturedProduct_left :
    toPuncturedProduct F a ha ≫
        pullback.fst Lines.P.structureMap PuncturedSourceProof.baseMap =
      genericLeft F a := by
  change toPuncturedModel F a ha ≫ PuncturedSourceProof.projection F ≫
    PuncturedSourceProof.productLeft = genericLeft F a
  rw [PuncturedSourceProof.projection_left]
  simpa only [genericLeft, modelLeft, PuncturedSourceProof.starSource, Category.assoc] using
    toPuncturedModel_source_assoc F a ha F.left

@[reassoc] theorem toPuncturedProduct_base :
    toPuncturedProduct F a ha ≫
        pullback.snd Lines.P.structureMap PuncturedSourceProof.baseMap =
      genericProjection F a ≫ genericToPunctured a ha := by
  change toPuncturedModel F a ha ≫ PuncturedSourceProof.projection F ≫
    PuncturedSourceProof.productBase = genericProjection F a ≫ genericToPunctured a ha
  rw [PuncturedSourceProof.projection_base]
  exact toPuncturedModel_base F a ha

theorem toPuncturedProduct_isPullback :
    IsPullback (toPuncturedProduct F a ha) (genericProjection F a)
      (pullback.snd Lines.P.structureMap PuncturedSourceProof.baseMap)
      (genericToPunctured a ha) := by
  apply (toPuncturedModel_isPullback F a ha).of_iso
    (Iso.refl _) (PuncturedSourceProof.trivialization F) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.id_comp, toPuncturedProduct]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simpa only [Iso.refl_hom, Category.comp_id,
      PuncturedSourceProof.trivialization, PuncturedSourceProof.productBase] using
      (PuncturedSourceProof.projection_base F).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

include ha in
/-- The original first projective coordinate is an isomorphism after
the actual fraction-field base change, with the base map fixed. -/
theorem genericLeft_isPullback :
    IsPullback (genericLeft F a) (genericProjection F a)
      Lines.P.structureMap (genericPoint ≫ toC) := by
  simpa only [toPuncturedProduct_left, genericToPunctured_toC] using
    (toPuncturedProduct_isPullback F a ha).paste_horiz
      (IsPullback.of_hasPullback Lines.P.structureMap PuncturedSourceProof.baseMap)

def genericTrivialization :
    GenericModel F a ≅ RationalSourceOver Lines.P GenericPoint (genericPoint ≫ toC) :=
  (genericLeft_isPullback F a ha).isoPullback

@[reassoc] theorem genericTrivialization_left :
    (genericTrivialization F a ha).hom ≫
      pullback.fst Lines.P.structureMap (genericPoint ≫ toC) = genericLeft F a :=
  (genericLeft_isPullback F a ha).isoPullback_hom_fst

@[reassoc] theorem genericTrivialization_base :
    (genericTrivialization F a ha).hom ≫
      pullback.snd Lines.P.structureMap (genericPoint ≫ toC) = genericProjection F a :=
  (genericLeft_isPullback F a ha).isoPullback_hom_snd

include ha in
theorem generic_geometricallyIntegral :
    GeometricallyIntegral (genericProjection F a) := by
  letI : Smooth Lines.P.structureMap :=
    smoothProperComplexVariety_smooth (projectiveLineVariety Lines.P)
  letI : ConnectedSpace ProjectiveLine := (projectiveLineVariety Lines.P).connected
  have h : GeometricallyIntegral Lines.P.structureMap :=
    LeBrunSalamon.StandardInputs.smooth_connected_complex_geometricallyIntegral
      Lines.P.structureMap
  exact MorphismProperty.of_isPullback (genericLeft_isPullback F a ha) h

theorem model_proper : IsProper (modelProjection F a) := by
  letI : IsProper F.parameter := standardSource_proper F
  change IsProper (pullback.snd F.parameter (parameterMap a))
  exact inferInstance

theorem model_flat : Flat (modelProjection F a) := by
  letI : Flat F.parameter := standardSource_flat F
  change Flat (pullback.snd F.parameter (parameterMap a))
  exact inferInstance

theorem model_finitePresentation : LocallyOfFinitePresentation (modelProjection F a) := by
  letI : LocallyOfFinitePresentation F.parameter := standardSource_lfp F
  change LocallyOfFinitePresentation (pullback.snd F.parameter (parameterMap a))
  exact inferInstance

include ha in
/-- Every global function on the entire (possibly nodal) model is the
pullback of a unique actual power-series coefficient. -/
theorem model_globalFunctions : Function.Bijective (modelProjection F a).appTop := by
  letI : IsProper (modelProjection F a) := model_proper F a
  letI : Flat (modelProjection F a) := model_flat F a
  letI : GeometricallyIntegral (pullback.snd (modelProjection F a)
      (Spec.map (CommRingCat.ofHom
        (algebraMap (CommRingCat.of Coefficients)
          (FractionRing (CommRingCat.of Coefficients)))))) :=
    generic_geometricallyIntegral F a ha
  exact LeBrunSalamon.StandardInputs.proper_flat_normal_generic_globalFunctions
    (CommRingCat.of Coefficients) (modelProjection F a)

end LeBrunSalamon.Construction.StableMaps.FormalArcs.ModelGeometry

end
