import LSFormalTraitModel
import LSFormalTraitProjectivity

/-!
# Literal trait pullbacks of the stable-map family

The special fibre is identified by the canonical iterated-pullback
isomorphism. Component maps, their complete pushout, the evaluation
morphism, and the degree of the actual pulled line are transported
together. No fibre is replaced by an abstract curve with the same graph.
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

/-- Stacks 0C59, 0C5B and 0H8M: nodal curve families remain nodal
after arbitrary base change, with actual etale local node equations. -/
theorem isNodalCurve_pullback
    {B C T : Scheme} (pi : C ⟶ B)
    [Flat pi] [LocallyOfFinitePresentation pi]
    (hnodal : LeBrunSalamon.Construction.StableMaps.IsNodalCurve pi)
    (t : T ⟶ B) :
    LeBrunSalamon.Construction.StableMaps.IsNodalCurve (pullback.snd pi t) := by
  sorry

/- isProjectiveOver_formalTrait is proved in LSFormalTraitProjectivity. -/

end LeBrunSalamon.StandardInputs

namespace LeBrunSalamon.Construction.StableMaps.TraitPullback

open FormalArcs

variable {P : ProjectiveLineOverC} {p : ProjectiveLinePoint P}
variable {d : ℕ} {X : SmoothProperComplexVariety d}
variable {L : LineBundle X.scheme} {degree : ℕ}
variable (F : ProjectiveNodalFamily P p X L degree)
variable (t : PointsOver Trait toC F.base F.toC)

abbrev Source : Scheme := pullback F.parameter t.val

abbrev parameter : Source F t ⟶ Trait := pullback.snd F.parameter t.val

def evaluation : Source F t ⟶ X.scheme :=
  pullback.fst F.parameter t.val ≫ F.evaluation

def line : LineBundle (Source F t) := pullbackLine (evaluation F t) L

@[reassoc] theorem evaluation_overC :
    evaluation F t ≫ X.structureMap = parameter F t ≫ toC := by
  dsimp [evaluation, parameter]
  rw [Category.assoc, F.overC, ← Category.assoc, pullback.condition,
    Category.assoc, t.property]

theorem parameter_proper : IsProper (parameter F t) := by
  letI : IsProper F.parameter := F.proper
  exact inferInstance

theorem parameter_flat : Flat (parameter F t) := by
  letI : Flat F.parameter := F.flat
  exact inferInstance

theorem parameter_finitePresentation : LocallyOfFinitePresentation (parameter F t) := by
  letI : LocallyOfFinitePresentation F.parameter := F.finitePresentation
  exact inferInstance

theorem parameter_nodal : IsNodalCurve (parameter F t) := by
  letI : Flat F.parameter := F.flat
  letI : LocallyOfFinitePresentation F.parameter := F.finitePresentation
  exact LeBrunSalamon.StandardInputs.isNodalCurve_pullback F.parameter F.nodal t.val

theorem parameter_projective : IsProjectiveOver (parameter F t) toC :=
  LeBrunSalamon.StandardInputs.isProjectiveOver_formalTrait
    F.parameter F.toC F.projective t

def genericToSmooth (u : GenericPoint ⟶ F.smoothOpen.toScheme)
    (hu : u ≫ F.smoothOpen.ι = genericPoint ≫ t.val) :
    pullback (parameter F t) genericPoint ⟶ pullback F.parameter F.smoothOpen.ι :=
  pullback.lift
    (pullback.fst (parameter F t) genericPoint ≫ pullback.fst F.parameter t.val)
    (pullback.snd (parameter F t) genericPoint ≫ u) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc,
        pullback.condition, Category.assoc, ← hu, Category.assoc])

@[reassoc] theorem genericToSmooth_source (u : GenericPoint ⟶ F.smoothOpen.toScheme)
    (hu : u ≫ F.smoothOpen.ι = genericPoint ≫ t.val) :
    genericToSmooth F t u hu ≫ pullback.fst F.parameter F.smoothOpen.ι =
      pullback.fst (parameter F t) genericPoint ≫ pullback.fst F.parameter t.val :=
  pullback.lift_fst _ _ _

@[reassoc] theorem genericToSmooth_base (u : GenericPoint ⟶ F.smoothOpen.toScheme)
    (hu : u ≫ F.smoothOpen.ι = genericPoint ≫ t.val) :
    genericToSmooth F t u hu ≫ pullback.snd F.parameter F.smoothOpen.ι =
      pullback.snd (parameter F t) genericPoint ≫ u :=
  pullback.lift_snd _ _ _

theorem genericToSmooth_isPullback (u : GenericPoint ⟶ F.smoothOpen.toScheme)
    (hu : u ≫ F.smoothOpen.ι = genericPoint ≫ t.val) :
    IsPullback (genericToSmooth F t u hu) (pullback.snd (parameter F t) genericPoint)
      (pullback.snd F.parameter F.smoothOpen.ι) u := by
  apply IsPullback.of_right (t := IsPullback.of_hasPullback F.parameter F.smoothOpen.ι)
  · simpa only [genericToSmooth_source, hu] using
      (IsPullback.of_hasPullback (parameter F t) genericPoint).paste_horiz
        (IsPullback.of_hasPullback F.parameter t.val)
  · exact genericToSmooth_base F t u hu

theorem generic_smooth_of_factor (u : GenericPoint ⟶ F.smoothOpen.toScheme)
    (hu : u ≫ F.smoothOpen.ι = genericPoint ≫ t.val) :
    SmoothOfRelativeDimension 1 (pullback.snd (parameter F t) genericPoint) :=
  MorphismProperty.of_isPullback (genericToSmooth_isPullback F t u hu) F.smooth

theorem generic_geometricallyIntegral_of_factor (u : GenericPoint ⟶ F.smoothOpen.toScheme)
    (hu : u ≫ F.smoothOpen.ι = genericPoint ≫ t.val) :
    GeometricallyIntegral (pullback.snd (parameter F t) genericPoint) :=
  MorphismProperty.of_isPullback (genericToSmooth_isPullback F t u hu)
    F.smoothGeometricallyIntegral

theorem genericPoint_dense : DenseRange genericPoint.base := by
  change DenseRange (PrimeSpectrum.comap
    (algebraMap Coefficients (FractionRing Coefficients)))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp
      (IsFractionRing.injective Coefficients (FractionRing Coefficients))]
  exact bot_le

/-- A dense inverse-image open of the actual trait contains its actual
fraction-field point. Thus the generic fibre uses the entire smooth
source locus, without assuming that any divisorial residue field is C. -/
theorem generic_factor_of_dense
    (ht : Dense (t.val ⁻¹ᵁ F.smoothOpen : Set Trait)) :
    ∃ u : GenericPoint ⟶ F.smoothOpen.toScheme,
      u ≫ F.smoothOpen.ι = genericPoint ≫ t.val := by
  obtain ⟨z, hz⟩ := genericPoint_dense.exists_mem_open
    (t.val ⁻¹ᵁ F.smoothOpen).isOpen ht.nonempty
  have hr : Set.range (genericPoint ≫ t.val) ⊆ Set.range F.smoothOpen.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    have hw : w = z := Subsingleton.elim w z
    subst w
    exact hz
  exact ⟨IsOpenImmersion.lift F.smoothOpen.ι (genericPoint ≫ t.val) hr,
    IsOpenImmersion.lift_fac F.smoothOpen.ι (genericPoint ≫ t.val) hr⟩

theorem generic_smooth (ht : Dense (t.val ⁻¹ᵁ F.smoothOpen : Set Trait)) :
    SmoothOfRelativeDimension 1 (pullback.snd (parameter F t) genericPoint) := by
  obtain ⟨u, hu⟩ := generic_factor_of_dense F t ht
  exact generic_smooth_of_factor F t u hu

theorem generic_geometricallyIntegral
    (ht : Dense (t.val ⁻¹ᵁ F.smoothOpen : Set Trait)) :
    GeometricallyIntegral (pullback.snd (parameter F t) genericPoint) := by
  obtain ⟨u, hu⟩ := generic_factor_of_dense F t ht
  exact generic_geometricallyIntegral_of_factor F t u hu

def specialPoint : PointsOver ComplexBase (𝟙 ComplexBase) F.base F.toC :=
  ⟨closedPoint ≫ t.val, by simp only [Category.assoc, t.property, closedPoint_toC]⟩

/-- The original complex fibre and the literal closed fibre after
trait pullback, compared with both actual projections normalized. -/
def specialFibreIso :
    pullback F.parameter (specialPoint F t).val ≅
      pullback (parameter F t) closedPoint :=
  (pullbackLeftPullbackSndIso F.parameter t.val closedPoint).symm

@[reassoc] theorem specialFibreIso_source :
    (specialFibreIso F t).hom ≫ pullback.fst (parameter F t) closedPoint ≫
      pullback.fst F.parameter t.val =
        pullback.fst F.parameter (specialPoint F t).val :=
  pullbackLeftPullbackSndIso_inv_fst _ _ _

@[reassoc] theorem specialFibreIso_base :
    (specialFibreIso F t).hom ≫ pullback.snd (parameter F t) closedPoint =
      pullback.snd F.parameter (specialPoint F t).val :=
  pullbackLeftPullbackSndIso_inv_snd_snd _ _ _

@[reassoc] theorem specialFibreIso_evaluation :
    (specialFibreIso F t).hom ≫ pullback.fst (parameter F t) closedPoint ≫
      evaluation F t =
        pullback.fst F.parameter (specialPoint F t).val ≫ F.evaluation := by
  simpa only [evaluation, Category.assoc] using
    specialFibreIso_source_assoc F t F.evaluation

theorem degree_composite (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {Y Z : Scheme} (f : ProjectiveLine ⟶ Y) (g : Y ⟶ Z) (M : LineBundle Z) :
    projectiveLineDegree P p (pullbackLine f (pullbackLine g M)) =
      projectiveLineDegree P p (pullbackLine (f ≫ g) M) :=
  projectiveLineDegree_iso P p _ _ (compositionPullback f g (f ≫ g) rfl M.sheaf)

/-- This equality compares the actual evaluation pullback on the trait
family with the exact component line in the recorded complex fibre. -/
theorem specialFibre_degree
    (i : ProjectiveLine ⟶ pullback F.parameter (specialPoint F t).val) :
    projectiveLineDegree P p
      (pullbackLine ((i ≫ (specialFibreIso F t).hom) ≫
        pullback.fst (parameter F t) closedPoint) (line F t)) =
      projectiveLineDegree P p
        (pullbackLine i
          (pullbackLine (pullback.fst F.parameter (specialPoint F t).val ≫
            F.evaluation) L)) := by
  simp only [line, degree_composite, Category.assoc, specialFibreIso_evaluation]

/-- The original ordinary degree-two tree theorem yields exactly the
two geometric alternatives required by the trait source normal forms. -/
theorem degreeTwo_specialFibre
    (F : ProjectiveNodalFamily P p X L 2)
    (t : PointsOver Trait toC F.base F.toC) :
    (∃ i : ProjectiveLine ≅ pullback (parameter F t) closedPoint,
      i.hom ≫ pullback.snd (parameter F t) closedPoint = P.structureMap ∧
      projectiveLineDegree P p
        (pullbackLine (i.hom ≫ pullback.fst (parameter F t) closedPoint) (line F t)) = 2) ∨
    (∃ (i j : ProjectiveLine ⟶ pullback (parameter F t) closedPoint)
        (a b : ProjectiveLinePoint P),
      IsClosedImmersion i ∧ IsClosedImmersion j ∧
      i ≫ pullback.snd (parameter F t) closedPoint = P.structureMap ∧
      j ≫ pullback.snd (parameter F t) closedPoint = P.structureMap ∧
      IsPushout a.map b.map i j ∧
      projectiveLineDegree P p
        (pullbackLine (i ≫ pullback.fst (parameter F t) closedPoint) (line F t)) = 1 ∧
      projectiveLineDegree P p
        (pullbackLine (j ≫ pullback.fst (parameter F t) closedPoint) (line F t)) = 1) := by
  rcases (F.fibre (specialPoint F t)).degreeTwo_presentation
      (F.fibreDegree (specialPoint F t)) with h | h
  · obtain ⟨i, hi, hd⟩ := h
    refine Or.inl ⟨i ≪≫ specialFibreIso F t, ?_, ?_⟩
    · simpa only [Iso.trans_hom, Category.assoc, specialFibreIso_base] using hi
    · exact (specialFibre_degree F t i.hom).trans hd
  · obtain ⟨i, j, a, b, hi, hj, hiover, hjover, hpushout, hideg, hjdeg⟩ := h
    letI : IsClosedImmersion i := hi
    letI : IsClosedImmersion j := hj
    refine Or.inr ⟨i ≫ (specialFibreIso F t).hom,
      j ≫ (specialFibreIso F t).hom, a, b, inferInstance, inferInstance,
      ?_, ?_, ?_, (specialFibre_degree F t i).trans hideg,
      (specialFibre_degree F t j).trans hjdeg⟩
    · simpa only [Category.assoc, specialFibreIso_base] using hiover
    · simpa only [Category.assoc, specialFibreIso_base] using hjover
    · apply hpushout.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (specialFibreIso F t)
      all_goals simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

section DegreeTwoModelNotation

local notation "Model" => LeBrunSalamon.Construction.StableMaps.FormalArcs.Model

/-- Apply the two reviewed generic source normal forms to the literal
trait family. The original graph theorem decides which form applies;
the displayed line is always the actual evaluation pullback of L. -/
theorem degreeTwo_lineNormalForm (S : Smoothing.StandardSource)
    (F : ProjectiveNodalFamily Lines.P Lines.marking X L 2)
    (t : PointsOver Trait toC F.base F.toC)
    (ht : Dense (t.val ⁻¹ᵁ F.smoothOpen : Set Trait)) :
    (∃ e : Source F t ≅ SmoothModel,
      e.hom ≫ smoothProjection = parameter F t ∧
        Nonempty ((line F t).sheaf ≅ pullbackModule e.hom smoothLine.sheaf)) ∨
    (∃ a : Coefficients, a ≠ 0 ∧ PowerSeries.constantCoeff a = 0 ∧
      ∃ e : Source F t ≅ Model S a,
        e.hom ≫ modelProjection S a = parameter F t ∧
          Nonempty ((line F t).sheaf ≅ pullbackModule e.hom (modelLine S a).sheaf)) := by
  letI : IsProper (parameter F t) := parameter_proper F t
  letI : Flat (parameter F t) := parameter_flat F t
  letI : LocallyOfFinitePresentation (parameter F t) := parameter_finitePresentation F t
  rcases degreeTwo_specialFibre F t with h | h
  · obtain ⟨i, hi, hd⟩ := h
    exact Or.inl (LeBrunSalamon.StandardInputs.formalTrait_smooth_lineNormalForm
      (parameter F t) (parameter_nodal F t) (parameter_projective F t)
      (generic_smooth F t ht) (generic_geometricallyIntegral F t ht)
      (line F t) i hi hd)
  · obtain ⟨i, j, a, b, hi, hj, hiover, hjover, hpushout, hideg, hjdeg⟩ := h
    exact Or.inr (LeBrunSalamon.StandardInputs.formalTrait_twoComponent_lineNormalForm S
      (parameter F t) (parameter_nodal F t) (parameter_projective F t)
      (generic_smooth F t ht) (generic_geometricallyIntegral F t ht)
      (line F t) i j a b hi hj hiover hjover hpushout hideg hjdeg)

end DegreeTwoModelNotation

/-- An actual arc of the total source square supplies the actual base
arc. Its two projections will be sections of the same pulled family. -/
def baseArc (gamma : PointsOver Trait toC F.Square (F.squareToBase ≫ F.toC)) :
    PointsOver Trait toC F.base F.toC :=
  ⟨gamma.val ≫ F.squareToBase, by simpa only [Category.assoc] using gamma.property⟩

theorem baseArc_dense
    (gamma : PointsOver Trait toC F.Square (F.squareToBase ≫ F.toC))
    (hgamma : Dense (gamma.val ⁻¹ᵁ F.smoothSquareOpen : Set Trait)) :
    Dense ((baseArc F gamma).val ⁻¹ᵁ F.smoothOpen : Set Trait) := by
  change Dense ((gamma.val ≫ F.squareToBase) ⁻¹ᵁ F.smoothOpen : Set Trait)
  rw [Scheme.Hom.comp_preimage]
  exact hgamma

def firstSection (gamma : PointsOver Trait toC F.Square (F.squareToBase ≫ F.toC)) :
    Trait ⟶ Source F (baseArc F gamma) :=
  pullback.lift (gamma.val ≫ pullback.fst F.parameter F.parameter) (𝟙 Trait) (by
    simp only [baseArc, ProjectiveNodalFamily.squareToBase, Category.assoc,
      Category.id_comp])

def secondSection (gamma : PointsOver Trait toC F.Square (F.squareToBase ≫ F.toC)) :
    Trait ⟶ Source F (baseArc F gamma) :=
  pullback.lift (gamma.val ≫ pullback.snd F.parameter F.parameter) (𝟙 Trait) (by
    simp only [baseArc, ProjectiveNodalFamily.squareToBase, Category.assoc,
      Category.id_comp]
    exact congrArg (fun k : F.Square ⟶ F.base => gamma.val ≫ k)
      (pullback.condition (f := F.parameter) (g := F.parameter)).symm)

@[reassoc] theorem firstSection_parameter
    (gamma : PointsOver Trait toC F.Square (F.squareToBase ≫ F.toC)) :
    firstSection F gamma ≫ parameter F (baseArc F gamma) = 𝟙 Trait :=
  pullback.lift_snd _ _ _

@[reassoc] theorem secondSection_parameter
    (gamma : PointsOver Trait toC F.Square (F.squareToBase ≫ F.toC)) :
    secondSection F gamma ≫ parameter F (baseArc F gamma) = 𝟙 Trait :=
  pullback.lift_snd _ _ _

@[reassoc] theorem firstSection_evaluation
    (gamma : PointsOver Trait toC F.Square (F.squareToBase ≫ F.toC)) :
    firstSection F gamma ≫ evaluation F (baseArc F gamma) =
      gamma.val ≫ F.squareEvaluation ≫ firstProjection X.structureMap := by
  simp only [firstSection, evaluation, Category.assoc,
    pullback.lift_fst_assoc, F.squareEvaluation_first]

@[reassoc] theorem secondSection_evaluation
    (gamma : PointsOver Trait toC F.Square (F.squareToBase ≫ F.toC)) :
    secondSection F gamma ≫ evaluation F (baseArc F gamma) =
      gamma.val ≫ F.squareEvaluation ≫ secondProjection X.structureMap := by
  simp only [secondSection, evaluation, Category.assoc,
    pullback.lift_fst_assoc, F.squareEvaluation_second]

end LeBrunSalamon.Construction.StableMaps.TraitPullback

end
