import LSFamilyDescentReparametrization

/-!
# Open-section comparison and smooth-family descent of the actual tensors.

This namespace block is extracted verbatim from the candidate descent
source. Public names, statements and proof bodies are retained. The preceding
transport blocks are imported so each completed native output can be reused.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.PhaseTwentyEight.ExternalExchangeCoherenceProof

namespace LeBrunSalamon.Construction.FamilyBivectors


-- Normalize the existing P1/contact carrier aliases for the same actual maps.
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety identityCurveContact intrinsicTangentBundle

namespace OpenSection

/-- A section on the pulled-back module over an open subscheme gives
the actual section of the original sheaf on that open. -/
def value {Y : Scheme} (U : Y.Opens) {E : OModule Y}
    (s : AlgebraicSection (pullbackModule U.ι E)) : SectionsOn E U :=
  E.presheaf.map (eqToHom U.ι_image_top.symm).op
    (sectionValue (s ≫ (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app E))

/-- The inverse construction retains the canonical open pullback. -/
def fromValue {Y : Scheme} (U : Y.Opens) {E : OModule Y}
    (s : SectionsOn E U) : AlgebraicSection (pullbackModule U.ι E) :=
  sectionFromValue (E.presheaf.map (eqToHom U.ι_image_top).op s) ≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app E

theorem value_section {Y : Scheme} (U : Y.Opens) {E : OModule Y}
    (s : SectionsOn E U) : value U (fromValue U s) = s := by
  simp only [value, fromValue, Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
    sectionFromValue_spec, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp, eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

theorem section_value {Y : Scheme} (U : Y.Opens) {E : OModule Y}
    (s : AlgebraicSection (pullbackModule U.ι E)) : fromValue U (value U s) = s := by
  apply (cancel_mono ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app E)).mp
  simp only [fromValue, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  apply (sectionValue_bijective (E.restrict U.ι)).injective
  simp only [sectionFromValue_spec, value, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

theorem value_map {Y : Scheme} (U : Y.Opens) {E F : OModule Y}
    (s : AlgebraicSection (pullbackModule U.ι E)) (v : E ⟶ F) :
    value U (s ≫ (Scheme.Modules.pullback U.ι).map v) = v.app U (value U s) := by
  unfold value
  rw [Category.assoc, (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.naturality,
    ← Category.assoc, sectionValue_comp]
  exact sheafHom_naturality v (eqToHom U.ι_image_top.symm)
    (sectionValue (s ≫ (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app E))

theorem value_pullSection {Y : Scheme} (U : Y.Opens) {E : OModule Y}
    (s : AlgebraicSection E) :
    value U (pullSection U.ι s) =
      E.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (sectionValue s) := by
  rw [← FrameEvaluation.restrictedSection_to_pullSection]
  simp only [value, Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
    FrameEvaluation.restrictedSection_value, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← op_comp]
  rfl

end OpenSection

namespace SmoothFamily

variable {P : ProjectiveLineOverC} {p : ProjectiveLinePoint P}
variable {n : ℕ} {X : ContactFanoManifold n} {g : VeryFreeContactConic P p X}
variable {N : FullConicNeighborhood P p X g}
variable {F : StableMaps.ProjectiveNodalFamily P p X.variety X.contact.sequence.line 2}
variable (Q : StableMaps.FullHomComparison P p X.variety N.homSpace N.neighborhood
  X.contact.sequence.line 2 F)

abbrev evaluation : Q.parametrizedSource ⟶ X.variety.scheme :=
  Q.sourceMap ≫ F.evaluation

theorem evaluation_overC :
    evaluation Q ≫ X.variety.structureMap =
      Parametrized.parameter P Q.coverToC ≫ Q.coverToC := by
  rw [evaluation, Category.assoc, F.overC, ← Category.assoc, Q.sourceMap_parameter]
  simpa only [Category.assoc, StableMaps.FullHomComparison.coverToBase,
    StableMaps.FullHomComparison.coverToC] using
    congrArg (fun k => Parametrized.parameter P Q.coverToC ≫ k) Q.overC

abbrev smoothEvaluation : F.smoothSquareOpen.toScheme ⟶ SelfProduct X.variety.structureMap :=
  F.smoothSquareOpen.ι ≫ F.squareEvaluation

abbrev parametrizedEvaluation : Q.ParametrizedSquare ⟶ SelfProduct X.variety.structureMap :=
  ParametrizedContact.evaluationSquare P Q.coverToC X (evaluation Q) (evaluation_overC Q)

@[reassoc] theorem evaluation_commutes :
    Q.parametrizedSquareToSmooth ≫ smoothEvaluation (F := F) =
      parametrizedEvaluation Q := by
  rw [smoothEvaluation, ← Category.assoc, Q.parametrizedSquareToSmooth_ι]
  apply pullback.hom_ext
  · simp only [parametrizedEvaluation, ParametrizedContact.evaluationSquare,
      Parametrized.evaluationSquare, Category.assoc,
      RelativeSquare.evaluation_left, F.squareEvaluation_first,
      Q.parametrizedSquareToFamily_first_assoc, evaluation]
  · simp only [parametrizedEvaluation, ParametrizedContact.evaluationSquare,
      Parametrized.evaluationSquare, Category.assoc,
      RelativeSquare.evaluation_right, F.squareEvaluation_second,
      Q.parametrizedSquareToFamily_second_assoc, evaluation]

abbrev smoothToC : F.smoothSquareOpen.toScheme ⟶ ComplexBase :=
  F.smoothSquareOpen.ι ≫ F.squareToBase ≫ F.toC

@[reassoc] theorem parametrized_toC :
    Q.parametrizedSquareToSmooth ≫ smoothToC (F := F) =
      Q.parametrizedSquareToCover ≫ Q.coverToC := by
  simp only [smoothToC, ← Category.assoc, Q.parametrizedSquareToSmooth_ι,
    Q.parametrizedSquareToFamily_base]
  simpa only [Category.assoc, StableMaps.FullHomComparison.coverToBase,
    StableMaps.FullHomComparison.coverToC] using
    congrArg (fun k => Q.parametrizedSquareToCover ≫ k) Q.overC

abbrev Point := PointsOver ComplexBase (𝟙 ComplexBase) Q.ParametrizedSquare
  (Q.parametrizedSquareToSmooth ≫ smoothToC (F := F))

def coverPoint (t : Point Q) :
    PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC :=
  ⟨t.val ≫ Q.parametrizedSquareToCover, by
    simpa only [Category.assoc, ← parametrized_toC Q] using t.property⟩

def neighborhoodPoint
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    PointsOver ComplexBase (𝟙 ComplexBase) N.neighborhood.toScheme
      (N.neighborhood.ι ≫ N.homSpace.toC) :=
  ⟨q.val ≫ Q.toHom, by simpa only [Category.assoc] using q.property⟩

abbrev curve
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    RationalCurve P X.variety := N.curveAt (neighborhoodPoint Q q)

@[reassoc] theorem fibre_evaluation
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    Q.complexSourceInclusion q ≫ evaluation Q = (curve Q q).map := by
  change Q.complexSourceMap q ≫ F.evaluation = _
  rw [Q.complexSourceMap_evaluation, curve, N.curveAt_spec]
  rfl

def fibreSquare
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    SelfProduct P.structureMap ⟶ Q.ParametrizedSquare :=
  Parametrized.squareAtSection P Q.coverToC q.val (Q.complexSourceInclusion q)
    (pullback.lift_snd _ _ _)

@[reassoc] theorem fibreSquare_evaluation
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    fibreSquare Q q ≫ parametrizedEvaluation Q = curveSquareMap P (curve Q q) :=
  Parametrized.squareAtSection_evaluation P Q.coverToC X.variety
    (evaluation Q) (evaluation_overC Q) q.val (Q.complexSourceInclusion q)
    (pullback.lift_snd _ _ _) (curve Q q) (fibre_evaluation Q q)

def coordinatePair (t : Point Q) : ComplexBase ⟶ SelfProduct P.structureMap :=
  t.val ≫ Parametrized.sourceSquare P Q.coverToC

@[reassoc] theorem coordinatePair_left (t : Point Q) :
    coordinatePair Q t ≫ firstProjection P.structureMap =
      t.val ≫ RelativeSquare.left Q.parametrizedParameter ≫
        Parametrized.projection P Q.coverToC := by
  simp only [coordinatePair, Parametrized.sourceSquare, Category.assoc,
    RelativeSquare.evaluation_left]

@[reassoc] theorem coordinatePair_right (t : Point Q) :
    coordinatePair Q t ≫ secondProjection P.structureMap =
      t.val ≫ RelativeSquare.right Q.parametrizedParameter ≫
        Parametrized.projection P Q.coverToC := by
  simp only [coordinatePair, Parametrized.sourceSquare, Category.assoc,
    RelativeSquare.evaluation_right]

theorem sourcePoint_factor
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC)
    (a : ComplexBase ⟶ Q.parametrizedSource)
    (ha : a ≫ Q.parametrizedParameter = q.val) :
    (a ≫ Parametrized.projection P Q.coverToC) ≫ Q.complexSourceInclusion q = a := by
  have hz : (a ≫ Parametrized.projection P Q.coverToC) ≫ P.structureMap =
      𝟙 ComplexBase := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha, q.property]
  apply pullback.hom_ext
  · simp only [Category.assoc, StableMaps.FullHomComparison.complexSourceInclusion,
      pullback.lift_fst, Category.comp_id]
  · simp only [StableMaps.FullHomComparison.complexSourceInclusion, Category.assoc,
      pullback.lift_snd]
    rw [← Category.assoc, hz, Category.id_comp, ha]

@[reassoc] theorem point_factorization (t : Point Q) :
    coordinatePair Q t ≫ fibreSquare Q (coverPoint Q t) = t.val := by
  apply pullback.hom_ext
  · simp only [fibreSquare, Category.assoc, Parametrized.squareAtSection_left]
    rw [← Category.assoc, coordinatePair_left]
    exact sourcePoint_factor Q (coverPoint Q t)
      (t.val ≫ RelativeSquare.left Q.parametrizedParameter) rfl
  · simp only [fibreSquare, Category.assoc, Parametrized.squareAtSection_right]
    rw [← Category.assoc, coordinatePair_right]
    apply sourcePoint_factor Q (coverPoint Q t)
      (t.val ≫ RelativeSquare.right Q.parametrizedParameter)
    simpa only [coverPoint, Category.assoc] using
      congrArg (fun k => t.val ≫ k) Q.parametrizedSquare_second_parameter

@[reassoc] theorem coordinatePair_toC (t : Point Q) :
    coordinatePair Q t ≫ firstProjection P.structureMap ≫ P.structureMap =
      𝟙 ComplexBase := by
  rw [coordinatePair_left_assoc]
  simp only [Category.assoc, Parametrized.projection, pullback.condition]
  exact (coverPoint Q t).property

theorem same_base (t₀ t₁ : Point Q)
    (h : t₀.val ≫ Q.parametrizedSquareToSmooth =
      t₁.val ≫ Q.parametrizedSquareToSmooth) :
    (coverPoint Q t₀).val ≫ Q.coverToBase =
      (coverPoint Q t₁).val ≫ Q.coverToBase := by
  have hb := congrArg (fun k => k ≫ F.smoothSquareParameter ≫ F.smoothOpen.ι) h
  simpa only [coverPoint, Category.assoc, Q.parametrizedSquareToSmooth_base,
    StableMaps.FullHomComparison.coverToBase] using hb

theorem complexSourceMap_ext
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC)
    {T : Scheme} (u v : T ⟶ ProjectiveLine)
    (hs : u ≫ Q.complexSourceMap q = v ≫ Q.complexSourceMap q)
    (hc : u ≫ P.structureMap = v ≫ P.structureMap) : u = v := by
  apply (cancel_mono (Q.complexFibreIso q).hom).mp
  apply pullback.hom_ext
  · simpa only [Category.assoc, Q.complexFibreIso_source] using hs
  · simpa only [Category.assoc, Q.complexFibreIso_toC] using hc

@[reassoc] theorem coordinatePair_source_left (t : Point Q) :
    coordinatePair Q t ≫ firstProjection P.structureMap ≫
        Q.complexSourceMap (coverPoint Q t) =
      t.val ≫ RelativeSquare.left Q.parametrizedParameter ≫ Q.sourceMap := by
  rw [StableMaps.FullHomComparison.complexSourceMap, ← Category.assoc,
    ← Category.assoc, coordinatePair_left]
  rw [sourcePoint_factor Q (coverPoint Q t)
    (t.val ≫ RelativeSquare.left Q.parametrizedParameter) rfl]

@[reassoc] theorem coordinatePair_source_right (t : Point Q) :
    coordinatePair Q t ≫ secondProjection P.structureMap ≫
        Q.complexSourceMap (coverPoint Q t) =
      t.val ≫ RelativeSquare.right Q.parametrizedParameter ≫ Q.sourceMap := by
  rw [StableMaps.FullHomComparison.complexSourceMap, ← Category.assoc,
    ← Category.assoc, coordinatePair_right]
  have hp : (t.val ≫ RelativeSquare.right Q.parametrizedParameter) ≫
      Q.parametrizedParameter = (coverPoint Q t).val := by
    simpa only [coverPoint, Category.assoc] using
      congrArg (fun k => t.val ≫ k) Q.parametrizedSquare_second_parameter
  rw [sourcePoint_factor Q (coverPoint Q t)
    (t.val ≫ RelativeSquare.right Q.parametrizedParameter) hp]

theorem transition_curves (t₀ t₁ : Point Q)
    (h : t₀.val ≫ Q.parametrizedSquareToSmooth =
      t₁.val ≫ Q.parametrizedSquareToSmooth) :
    (curve Q (coverPoint Q t₀)).map =
      (Q.complexTransition (coverPoint Q t₀) (coverPoint Q t₁)
        (same_base Q t₀ t₁ h)).hom ≫ (curve Q (coverPoint Q t₁)).map := by
  rw [← fibre_evaluation Q (coverPoint Q t₀),
    ← fibre_evaluation Q (coverPoint Q t₁)]
  change Q.complexSourceMap (coverPoint Q t₀) ≫ F.evaluation =
    _ ≫ Q.complexSourceMap (coverPoint Q t₁) ≫ F.evaluation
  rw [Q.complexTransition_source_assoc]

theorem transition_coordinates (t₀ t₁ : Point Q)
    (h : t₀.val ≫ Q.parametrizedSquareToSmooth =
      t₁.val ≫ Q.parametrizedSquareToSmooth) :
    coordinatePair Q t₀ ≫ curveSquareMap P
      (Reparametrization.curve P
        (Q.complexTransition (coverPoint Q t₀) (coverPoint Q t₁) (same_base Q t₀ t₁ h))
        (Q.complexTransition_overC (coverPoint Q t₀) (coverPoint Q t₁)
          (same_base Q t₀ t₁ h))) = coordinatePair Q t₁ := by
  let e := Q.complexTransition (coverPoint Q t₀) (coverPoint Q t₁) (same_base Q t₀ t₁ h)
  have he : e.hom ≫ P.structureMap = P.structureMap :=
    Q.complexTransition_overC _ _ _
  have hfamily : t₀.val ≫ Q.parametrizedSquareToFamily =
      t₁.val ≫ Q.parametrizedSquareToFamily := by
    simpa only [Category.assoc, Q.parametrizedSquareToSmooth_ι] using
      congrArg (fun k => k ≫ F.smoothSquareOpen.ι) h
  apply pullback.hom_ext
  · simp only [Category.assoc, curveSquareMap_first]
    apply complexSourceMap_ext Q (coverPoint Q t₁)
    · simp only [Category.assoc, Q.complexTransition_source,
        coordinatePair_source_left]
      simpa only [Category.assoc, Q.parametrizedSquareToFamily_first] using
        congrArg (fun k => k ≫ pullback.fst F.parameter F.parameter) hfamily
    · simp only [Category.assoc, he, coordinatePair_toC]
  · simp only [Category.assoc, curveSquareMap_second]
    apply complexSourceMap_ext Q (coverPoint Q t₁)
    · simp only [Category.assoc, Q.complexTransition_source,
        coordinatePair_source_right]
      simpa only [Category.assoc, Q.parametrizedSquareToFamily_second] using
        congrArg (fun k => k ≫ pullback.snd F.parameter F.parameter) hfamily
    · simp only [Category.assoc, he]
      simpa only [← pullback.condition] using
        (coordinatePair_toC Q t₀).trans (coordinatePair_toC Q t₁).symm

abbrev left : AlgebraicSection
    (pullbackModule (parametrizedEvaluation Q) (movingPairBundleLeft X.variety X.contact)) :=
  ParametrizedContact.leftSection P Q.coverToC X (evaluation Q) (evaluation_overC Q)

abbrev right : AlgebraicSection
    (pullbackModule (parametrizedEvaluation Q) (movingPairBundleRight X.variety X.contact)) :=
  ParametrizedContact.rightSection P Q.coverToC X (evaluation Q) (evaluation_overC Q)

theorem fibre_left
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    pullSection (fibreSquare Q q) (left Q) ≫
      (compositionPullback (fibreSquare Q q) (parametrizedEvaluation Q)
        (curveSquareMap P (curve Q q)) (fibreSquare_evaluation Q q)
        (movingPairBundleLeft X.variety X.contact)).hom = Curve.leftSection P X (curve Q q) :=
  ParametrizedContact.leftSection_atCurve P Q.coverToC X (evaluation Q)
    (evaluation_overC Q) q.val q.property (Q.complexSourceInclusion q)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (curve Q q) (fibre_evaluation Q q)

theorem fibre_right
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    pullSection (fibreSquare Q q) (right Q) ≫
      (compositionPullback (fibreSquare Q q) (parametrizedEvaluation Q)
        (curveSquareMap P (curve Q q)) (fibreSquare_evaluation Q q)
        (movingPairBundleRight X.variety X.contact)).hom = Curve.rightSection P X (curve Q q) :=
  ParametrizedContact.rightSection_atCurve P Q.coverToC X (evaluation Q)
    (evaluation_overC Q) q.val q.property (Q.complexSourceInclusion q)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (curve Q q) (fibre_evaluation Q q)

@[reassoc] theorem coordinatePair_evaluation (t : Point Q) :
    coordinatePair Q t ≫ curveSquareMap P (curve Q (coverPoint Q t)) =
      t.val ≫ parametrizedEvaluation Q := by
  rw [← fibreSquare_evaluation Q (coverPoint Q t), ← Category.assoc, point_factorization]

theorem point_left (t : Point Q) (x : ComplexBase ⟶ SelfProduct X.variety.structureMap)
    (hx : t.val ≫ parametrizedEvaluation Q = x)
    (hz : coordinatePair Q t ≫ curveSquareMap P (curve Q (coverPoint Q t)) = x) :
    pullSection t.val (left Q) ≫
      (compositionPullback t.val (parametrizedEvaluation Q) x hx
        (movingPairBundleLeft X.variety X.contact)).hom =
    pullSection (coordinatePair Q t) (Curve.leftSection P X (curve Q (coverPoint Q t))) ≫
      (compositionPullback (coordinatePair Q t)
        (curveSquareMap P (curve Q (coverPoint Q t))) x hz
        (movingPairBundleLeft X.variety X.contact)).hom :=
  SectionTransport.pull_specialization (coordinatePair Q t) (fibreSquare Q (coverPoint Q t))
    (parametrizedEvaluation Q) t.val (curveSquareMap P (curve Q (coverPoint Q t))) x
    (point_factorization Q t) (fibreSquare_evaluation Q (coverPoint Q t)) hz hx
    (left Q) (Curve.leftSection P X (curve Q (coverPoint Q t))) (fibre_left Q (coverPoint Q t))

theorem point_right (t : Point Q) (x : ComplexBase ⟶ SelfProduct X.variety.structureMap)
    (hx : t.val ≫ parametrizedEvaluation Q = x)
    (hz : coordinatePair Q t ≫ curveSquareMap P (curve Q (coverPoint Q t)) = x) :
    pullSection t.val (right Q) ≫
      (compositionPullback t.val (parametrizedEvaluation Q) x hx
        (movingPairBundleRight X.variety X.contact)).hom =
    pullSection (coordinatePair Q t) (Curve.rightSection P X (curve Q (coverPoint Q t))) ≫
      (compositionPullback (coordinatePair Q t)
        (curveSquareMap P (curve Q (coverPoint Q t))) x hz
        (movingPairBundleRight X.variety X.contact)).hom :=
  SectionTransport.pull_specialization (coordinatePair Q t) (fibreSquare Q (coverPoint Q t))
    (parametrizedEvaluation Q) t.val (curveSquareMap P (curve Q (coverPoint Q t))) x
    (point_factorization Q t) (fibreSquare_evaluation Q (coverPoint Q t)) hz hx
    (right Q) (Curve.rightSection P X (curve Q (coverPoint Q t))) (fibre_right Q (coverPoint Q t))

theorem same_evaluation (t₀ t₁ : Point Q)
    (h : t₀.val ≫ Q.parametrizedSquareToSmooth =
      t₁.val ≫ Q.parametrizedSquareToSmooth) :
    t₀.val ≫ parametrizedEvaluation Q = t₁.val ≫ parametrizedEvaluation Q := by
  simpa only [Category.assoc, evaluation_commutes] using
    congrArg (fun k => k ≫ smoothEvaluation (F := F)) h

/-- The two values on an actual double fibre agree after the canonical
identification of their target fibres. -/
theorem left_point_values (t₀ t₁ : Point Q)
    (h : t₀.val ≫ Q.parametrizedSquareToSmooth =
      t₁.val ≫ Q.parametrizedSquareToSmooth) :
    pullSection t₀.val (left Q) ≫
      (compositionPullback t₀.val (parametrizedEvaluation Q)
        (t₁.val ≫ parametrizedEvaluation Q) (same_evaluation Q t₀ t₁ h)
        (movingPairBundleLeft X.variety X.contact)).hom =
    pullSection t₁.val (left Q) ≫
      (compositionPullback t₁.val (parametrizedEvaluation Q)
        (t₁.val ≫ parametrizedEvaluation Q) rfl
        (movingPairBundleLeft X.variety X.contact)).hom := by
  let e := Q.complexTransition (coverPoint Q t₀) (coverPoint Q t₁) (same_base Q t₀ t₁ h)
  have he : e.hom ≫ P.structureMap = P.structureMap := Q.complexTransition_overC _ _ _
  have hz₀ := (coordinatePair_evaluation Q t₀).trans (same_evaluation Q t₀ t₁ h)
  have hz₁ := coordinatePair_evaluation Q t₁
  rw [point_left Q t₀ _ (same_evaluation Q t₀ t₁ h) hz₀,
    point_left Q t₁ _ rfl hz₁]
  exact (SectionTransport.pull_specialization (coordinatePair Q t₀)
    (curveSquareMap P (Reparametrization.curve P e he))
    (curveSquareMap P (curve Q (coverPoint Q t₁))) (coordinatePair Q t₁)
    (curveSquareMap P (curve Q (coverPoint Q t₀))) (t₁.val ≫ parametrizedEvaluation Q)
    (transition_coordinates Q t₀ t₁ h)
    (Reparametrization.square_comp P e he X (curve Q (coverPoint Q t₁))
      (curve Q (coverPoint Q t₀)) (transition_curves Q t₀ t₁ h)) hz₀ hz₁
    (Curve.leftSection P X (curve Q (coverPoint Q t₁)))
    (Curve.leftSection P X (curve Q (coverPoint Q t₀)))
    (Reparametrization.leftSection P e he X (curve Q (coverPoint Q t₁))
      (curve Q (coverPoint Q t₀)) (transition_curves Q t₀ t₁ h))).symm

theorem right_point_values (t₀ t₁ : Point Q)
    (h : t₀.val ≫ Q.parametrizedSquareToSmooth =
      t₁.val ≫ Q.parametrizedSquareToSmooth) :
    pullSection t₀.val (right Q) ≫
      (compositionPullback t₀.val (parametrizedEvaluation Q)
        (t₁.val ≫ parametrizedEvaluation Q) (same_evaluation Q t₀ t₁ h)
        (movingPairBundleRight X.variety X.contact)).hom =
    pullSection t₁.val (right Q) ≫
      (compositionPullback t₁.val (parametrizedEvaluation Q)
        (t₁.val ≫ parametrizedEvaluation Q) rfl
        (movingPairBundleRight X.variety X.contact)).hom := by
  let e := Q.complexTransition (coverPoint Q t₀) (coverPoint Q t₁) (same_base Q t₀ t₁ h)
  have he : e.hom ≫ P.structureMap = P.structureMap := Q.complexTransition_overC _ _ _
  have hz₀ := (coordinatePair_evaluation Q t₀).trans (same_evaluation Q t₀ t₁ h)
  have hz₁ := coordinatePair_evaluation Q t₁
  rw [point_right Q t₀ _ (same_evaluation Q t₀ t₁ h) hz₀,
    point_right Q t₁ _ rfl hz₁]
  exact (SectionTransport.pull_specialization (coordinatePair Q t₀)
    (curveSquareMap P (Reparametrization.curve P e he))
    (curveSquareMap P (curve Q (coverPoint Q t₁))) (coordinatePair Q t₁)
    (curveSquareMap P (curve Q (coverPoint Q t₀))) (t₁.val ≫ parametrizedEvaluation Q)
    (transition_coordinates Q t₀ t₁ h)
    (Reparametrization.square_comp P e he X (curve Q (coverPoint Q t₁))
      (curve Q (coverPoint Q t₀)) (transition_curves Q t₀ t₁ h)) hz₀ hz₁
    (Curve.rightSection P X (curve Q (coverPoint Q t₁)))
    (Curve.rightSection P X (curve Q (coverPoint Q t₀)))
    (Reparametrization.rightSection P e he X (curve Q (coverPoint Q t₁))
      (curve Q (coverPoint Q t₀)) (transition_curves Q t₀ t₁ h))).symm

include Q in
theorem smooth_locallyOfFiniteType : LocallyOfFiniteType (smoothToC (F := F)) := by
  letI : IsProper F.toC := F.baseProper
  letI : IsProper F.squareToBase := F.squareToBase_proper
  dsimp only [smoothToC]
  infer_instance

theorem parametrized_reduced : AlgebraicGeometry.IsReduced Q.ParametrizedSquare := by
  letI : IsIntegral F.Square := F.square_integral
  letI : IsLocallyNoetherian F.Square := F.square_locallyNoetherian
  letI : AlgebraicGeometry.IsReduced F.smoothSquareOpen.toScheme :=
    isReduced_of_isOpenImmersion F.smoothSquareOpen.ι
  letI : IsLocallyNoetherian F.smoothSquareOpen.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian F.smoothSquareOpen.ι
  letI : Smooth Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_smooth
  letI : GeometricallyIntegral Q.parametrizedSquareToSmooth :=
    Q.parametrizedSquareToSmooth_geometricallyIntegral
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
    Q.parametrizedSquareToSmooth

theorem overlap_reduced : AlgebraicGeometry.IsReduced
    (pullback Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth) := by
  letI : LocallyOfFiniteType (smoothToC (F := F)) := smooth_locallyOfFiniteType Q
  letI : IsLocallyNoetherian F.smoothSquareOpen.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (smoothToC (F := F))
  letI : Smooth Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_smooth
  letI : GeometricallyIntegral Q.parametrizedSquareToSmooth :=
    Q.parametrizedSquareToSmooth_geometricallyIntegral
  letI : AlgebraicGeometry.IsReduced Q.ParametrizedSquare := parametrized_reduced Q
  letI : IsLocallyNoetherian Q.ParametrizedSquare :=
    LocallyOfFiniteType.isLocallyNoetherian Q.parametrizedSquareToSmooth
  infer_instance

theorem overlap_locallyOfFiniteType : LocallyOfFiniteType
    (pullback.fst Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth ≫
      Q.parametrizedSquareToSmooth ≫ smoothToC (F := F)) := by
  letI : LocallyOfFiniteType (smoothToC (F := F)) := smooth_locallyOfFiniteType Q
  letI : Smooth Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_smooth
  infer_instance

def leftCover : AlgebraicSection
    (pullbackModule Q.parametrizedSquareToSmooth
      (MovingPair.leftBundle (smoothEvaluation (F := F))).sheaf) :=
  left Q ≫ (compositionPullback Q.parametrizedSquareToSmooth
    (smoothEvaluation (F := F)) (parametrizedEvaluation Q) (evaluation_commutes Q)
    (movingPairBundleLeft X.variety X.contact)).inv

def rightCover : AlgebraicSection
    (pullbackModule Q.parametrizedSquareToSmooth
      (MovingPair.rightBundle (smoothEvaluation (F := F))).sheaf) :=
  right Q ≫ (compositionPullback Q.parametrizedSquareToSmooth
    (smoothEvaluation (F := F)) (parametrizedEvaluation Q) (evaluation_commutes Q)
    (movingPairBundleRight X.variety X.contact)).inv

@[reassoc] theorem leftCover_comparison : leftCover Q ≫
    (compositionPullback Q.parametrizedSquareToSmooth (smoothEvaluation (F := F))
      (parametrizedEvaluation Q) (evaluation_commutes Q)
      (movingPairBundleLeft X.variety X.contact)).hom = left Q := by
  simp only [leftCover, Category.assoc, Iso.inv_hom_id, Category.comp_id]

@[reassoc] theorem rightCover_comparison : rightCover Q ≫
    (compositionPullback Q.parametrizedSquareToSmooth (smoothEvaluation (F := F))
      (parametrizedEvaluation Q) (evaluation_commutes Q)
      (movingPairBundleRight X.variety X.contact)).hom = right Q := by
  simp only [rightCover, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Equality on the actual double overlap, proved from equality at
complex points of that reduced finite-type scheme. -/
theorem leftCover_compatible :
    pullSection (pullback.fst Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        (leftCover Q) ≫
      (pullbackSquareIso
        (pullback.fst Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        Q.parametrizedSquareToSmooth
        (pullback.snd Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        Q.parametrizedSquareToSmooth pullback.condition
        (MovingPair.leftBundle (smoothEvaluation (F := F))).sheaf).hom =
      pullSection (pullback.snd Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        (leftCover Q) := by
  letI := overlap_reduced Q
  letI := overlap_locallyOfFiniteType Q
  apply SectionTransport.compatible_of_point_values Q.parametrizedSquareToSmooth
    (smoothToC (F := F)) (MovingPair.leftBundle (smoothEvaluation (F := F))) (leftCover Q)
  intro q₀ q₁ h
  have hz : (q₁.val ≫ Q.parametrizedSquareToSmooth) ≫ smoothEvaluation (F := F) =
      q₁.val ≫ parametrizedEvaluation Q := by rw [Category.assoc, evaluation_commutes]
  apply (cancel_mono (compositionPullback (q₁.val ≫ Q.parametrizedSquareToSmooth)
    (smoothEvaluation (F := F)) (q₁.val ≫ parametrizedEvaluation Q) hz
    (movingPairBundleLeft X.variety X.contact)).hom).mp
  simp only [Category.assoc]
  rw [SectionTransport.inverse_composition_value q₀.val Q.parametrizedSquareToSmooth
    (smoothEvaluation (F := F)) (parametrizedEvaluation Q) (evaluation_commutes Q)
    (q₁.val ≫ Q.parametrizedSquareToSmooth) h (q₁.val ≫ parametrizedEvaluation Q) hz
    (same_evaluation Q q₀ q₁ h) (left Q)]
  rw [SectionTransport.inverse_composition_value q₁.val Q.parametrizedSquareToSmooth
    (smoothEvaluation (F := F)) (parametrizedEvaluation Q) (evaluation_commutes Q)
    (q₁.val ≫ Q.parametrizedSquareToSmooth) rfl (q₁.val ≫ parametrizedEvaluation Q) hz
    rfl (left Q)]
  exact left_point_values Q q₀ q₁ h

theorem rightCover_compatible :
    pullSection (pullback.fst Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        (rightCover Q) ≫
      (pullbackSquareIso
        (pullback.fst Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        Q.parametrizedSquareToSmooth
        (pullback.snd Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        Q.parametrizedSquareToSmooth pullback.condition
        (MovingPair.rightBundle (smoothEvaluation (F := F))).sheaf).hom =
      pullSection (pullback.snd Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        (rightCover Q) := by
  letI := overlap_reduced Q
  letI := overlap_locallyOfFiniteType Q
  apply SectionTransport.compatible_of_point_values Q.parametrizedSquareToSmooth
    (smoothToC (F := F)) (MovingPair.rightBundle (smoothEvaluation (F := F))) (rightCover Q)
  intro q₀ q₁ h
  have hz : (q₁.val ≫ Q.parametrizedSquareToSmooth) ≫ smoothEvaluation (F := F) =
      q₁.val ≫ parametrizedEvaluation Q := by rw [Category.assoc, evaluation_commutes]
  apply (cancel_mono (compositionPullback (q₁.val ≫ Q.parametrizedSquareToSmooth)
    (smoothEvaluation (F := F)) (q₁.val ≫ parametrizedEvaluation Q) hz
    (movingPairBundleRight X.variety X.contact)).hom).mp
  simp only [Category.assoc]
  rw [SectionTransport.inverse_composition_value q₀.val Q.parametrizedSquareToSmooth
    (smoothEvaluation (F := F)) (parametrizedEvaluation Q) (evaluation_commutes Q)
    (q₁.val ≫ Q.parametrizedSquareToSmooth) h (q₁.val ≫ parametrizedEvaluation Q) hz
    (same_evaluation Q q₀ q₁ h) (right Q)]
  rw [SectionTransport.inverse_composition_value q₁.val Q.parametrizedSquareToSmooth
    (smoothEvaluation (F := F)) (parametrizedEvaluation Q) (evaluation_commutes Q)
    (q₁.val ≫ Q.parametrizedSquareToSmooth) rfl (q₁.val ≫ parametrizedEvaluation Q) hz
    rfl (right Q)]
  exact right_point_values Q q₀ q₁ h

theorem smoothLeft_exists : ∃! s : AlgebraicSection
    (MovingPair.leftBundle (smoothEvaluation (F := F))).sheaf,
    pullSection Q.parametrizedSquareToSmooth s = leftCover Q := by
  letI : Smooth Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_smooth
  letI : Surjective Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_surjective
  exact FlatSectionDescent.existsUnique_fppf Q.parametrizedSquareToSmooth
    (MovingPair.leftBundle (smoothEvaluation (F := F))) (leftCover Q) (leftCover_compatible Q)

theorem smoothRight_exists : ∃! s : AlgebraicSection
    (MovingPair.rightBundle (smoothEvaluation (F := F))).sheaf,
    pullSection Q.parametrizedSquareToSmooth s = rightCover Q := by
  letI : Smooth Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_smooth
  letI : Surjective Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_surjective
  exact FlatSectionDescent.existsUnique_fppf Q.parametrizedSquareToSmooth
    (MovingPair.rightBundle (smoothEvaluation (F := F))) (rightCover Q) (rightCover_compatible Q)

/-- The uniquely descended actual left section on the smooth family. -/
def smoothLeft : AlgebraicSection
    (MovingPair.leftBundle (smoothEvaluation (F := F))).sheaf :=
  Classical.choose (smoothLeft_exists Q)

/-- The uniquely descended actual right section on the smooth family. -/
def smoothRight : AlgebraicSection
    (MovingPair.rightBundle (smoothEvaluation (F := F))).sheaf :=
  Classical.choose (smoothRight_exists Q)

theorem smoothLeft_pullback :
    pullSection Q.parametrizedSquareToSmooth (smoothLeft Q) = leftCover Q :=
  (Classical.choose_spec (smoothLeft_exists Q)).1

theorem smoothRight_pullback :
    pullSection Q.parametrizedSquareToSmooth (smoothRight Q) = rightCover Q :=
  (Classical.choose_spec (smoothRight_exists Q)).1

/-- Universal normalization on the actual parametrization cover.
This equality may subsequently be pulled back along arbitrary schemes. -/
theorem smoothLeft_normalization :
    pullSection Q.parametrizedSquareToSmooth (smoothLeft Q) ≫
      (compositionPullback Q.parametrizedSquareToSmooth (smoothEvaluation (F := F))
        (parametrizedEvaluation Q) (evaluation_commutes Q)
        (movingPairBundleLeft X.variety X.contact)).hom = left Q := by
  rw [smoothLeft_pullback, leftCover_comparison]

theorem smoothRight_normalization :
    pullSection Q.parametrizedSquareToSmooth (smoothRight Q) ≫
      (compositionPullback Q.parametrizedSquareToSmooth (smoothEvaluation (F := F))
        (parametrizedEvaluation Q) (evaluation_commutes Q)
        (movingPairBundleRight X.variety X.contact)).hom = right Q := by
  rw [smoothRight_pullback, rightCover_comparison]

theorem smooth_commonContact :
    smoothLeft Q ≫ MovingPair.leftContact (smoothEvaluation (F := F)) =
      smoothRight Q ≫ MovingPair.rightContact (smoothEvaluation (F := F)) := by
  letI : Smooth Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_smooth
  letI : Surjective Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_surjective
  apply FlatSectionDescent.pullSection_injective_fppf Q.parametrizedSquareToSmooth
    (MovingPair.valueBundle (smoothEvaluation (F := F)))
  apply (cancel_mono (compositionPullback Q.parametrizedSquareToSmooth
    (smoothEvaluation (F := F)) (parametrizedEvaluation Q) (evaluation_commutes Q)
    (externalSquareLine X.variety.structureMap X.contact.sequence.line).sheaf).hom).mp
  rw [pullSection_naturality, pullSection_naturality]
  simp only [Category.assoc]
  rw [Normalization.BundleGluing.compositionPullback_naturality,
    Normalization.BundleGluing.compositionPullback_naturality,
    ← Category.assoc, smoothLeft_normalization,
    ← Category.assoc, smoothRight_normalization]
  exact ParametrizedContact.commonContact P Q.coverToC X (evaluation Q) (evaluation_overC Q)

def restrictedLeft : AlgebraicSection
    (pullbackModule F.smoothSquareOpen.ι (MovingPair.leftBundle F.squareEvaluation).sheaf) :=
  smoothLeft Q ≫ (compositionPullback F.smoothSquareOpen.ι F.squareEvaluation
    (smoothEvaluation (F := F)) rfl (movingPairBundleLeft X.variety X.contact)).inv

def restrictedRight : AlgebraicSection
    (pullbackModule F.smoothSquareOpen.ι (MovingPair.rightBundle F.squareEvaluation).sheaf) :=
  smoothRight Q ≫ (compositionPullback F.smoothSquareOpen.ι F.squareEvaluation
    (smoothEvaluation (F := F)) rfl (movingPairBundleRight X.variety X.contact)).inv

theorem restricted_commonContact :
    restrictedLeft Q ≫ (Scheme.Modules.pullback F.smoothSquareOpen.ι).map
        (MovingPair.leftContact F.squareEvaluation) =
      restrictedRight Q ≫ (Scheme.Modules.pullback F.smoothSquareOpen.ι).map
        (MovingPair.rightContact F.squareEvaluation) := by
  simp only [restrictedLeft, restrictedRight, Category.assoc]
  rw [← Descent.LineValue.composition_inv_naturality,
    ← Descent.LineValue.composition_inv_naturality,
    ← Category.assoc, smooth_commonContact]

/-- The two actual rational sections on the compactified square. Their
domain is exactly the original smooth square open. -/
def rationalPair : MovingPair.RationalVectorPair F.squareEvaluation where
  domain := F.smoothSquareOpen
  dense := F.smoothSquareOpen_dense
  leftSection := OpenSection.value F.smoothSquareOpen (restrictedLeft Q)
  rightSection := OpenSection.value F.smoothSquareOpen (restrictedRight Q)
  common := by
    have h := congrArg (fun a => OpenSection.value F.smoothSquareOpen a)
      (restricted_commonContact Q)
    simpa only [OpenSection.value_map] using h

@[simp] theorem rationalPair_domain : (rationalPair Q).domain = F.smoothSquareOpen := rfl

theorem rationalPair_left_open :
    OpenSection.fromValue F.smoothSquareOpen (rationalPair Q).leftSection = restrictedLeft Q :=
  OpenSection.section_value F.smoothSquareOpen (restrictedLeft Q)

theorem rationalPair_right_open :
    OpenSection.fromValue F.smoothSquareOpen (rationalPair Q).rightSection = restrictedRight Q :=
  OpenSection.section_value F.smoothSquareOpen (restrictedRight Q)

theorem extension_left_smooth (E : (rationalPair Q).Extension) :
    pullSection F.smoothSquareOpen.ι E.leftSection ≫
      (compositionPullback F.smoothSquareOpen.ι F.squareEvaluation
        (smoothEvaluation (F := F)) rfl (movingPairBundleLeft X.variety X.contact)).hom =
      smoothLeft Q := by
  have hv : OpenSection.value F.smoothSquareOpen
      (pullSection F.smoothSquareOpen.ι E.leftSection) =
      OpenSection.value F.smoothSquareOpen (restrictedLeft Q) := by
    rw [OpenSection.value_pullSection]
    exact E.extendsLeft
  have hs := congrArg (fun a => OpenSection.fromValue F.smoothSquareOpen a) hv
  rw [OpenSection.section_value, OpenSection.section_value] at hs
  rw [hs]
  simp only [restrictedLeft, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem extension_right_smooth (E : (rationalPair Q).Extension) :
    pullSection F.smoothSquareOpen.ι E.rightSection ≫
      (compositionPullback F.smoothSquareOpen.ι F.squareEvaluation
        (smoothEvaluation (F := F)) rfl (movingPairBundleRight X.variety X.contact)).hom =
      smoothRight Q := by
  have hv : OpenSection.value F.smoothSquareOpen
      (pullSection F.smoothSquareOpen.ι E.rightSection) =
      OpenSection.value F.smoothSquareOpen (restrictedRight Q) := by
    rw [OpenSection.value_pullSection]
    exact E.extendsRight
  have hs := congrArg (fun a => OpenSection.fromValue F.smoothSquareOpen a) hv
  rw [OpenSection.section_value, OpenSection.section_value] at hs
  rw [hs]
  simp only [restrictedRight, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable (t : PointsOver ComplexBase (𝟙 ComplexBase) N.neighborhood.toScheme
  (N.neighborhood.ι ≫ N.homSpace.toC))

def memberToParametrized : Q.ReducedMemberCover t ⟶ Q.ParametrizedSquare :=
  Q.reducedMemberInclusion t ≫ Q.memberToParametrizedSquare t

def memberToSmooth : Q.ReducedMemberCover t ⟶ F.smoothSquareOpen.toScheme :=
  memberToParametrized Q t ≫ Q.parametrizedSquareToSmooth

def memberToFamily : Q.ReducedMemberCover t ⟶ F.Square :=
  Q.reducedMemberInclusion t ≫ Q.memberToFamilySquare t

abbrev memberEvaluation : Q.ReducedMemberCover t ⟶ SelfProduct X.variety.structureMap :=
  Q.reducedMemberToSquare t ≫ curveSquareMap P (N.curveAt t)

@[reassoc] theorem memberToSmooth_ι :
    memberToSmooth Q t ≫ F.smoothSquareOpen.ι = memberToFamily Q t := by
  simp only [memberToSmooth, memberToParametrized, memberToFamily,
    Category.assoc, Q.parametrizedSquareToSmooth_ι,
    Q.memberToParametrizedSquare_family]

@[reassoc] theorem memberToFamily_evaluation :
    memberToFamily Q t ≫ F.squareEvaluation = memberEvaluation Q t := by
  simp only [memberToFamily, memberEvaluation,
    StableMaps.FullHomComparison.reducedMemberToSquare, Category.assoc,
    Q.member_commutes t (N.curveAt t) (N.curveAt_spec t)]

@[reassoc] theorem memberToSmooth_evaluation :
    memberToSmooth Q t ≫ smoothEvaluation (F := F) = memberEvaluation Q t := by
  rw [smoothEvaluation, ← Category.assoc, memberToSmooth_ι, memberToFamily_evaluation]

@[reassoc] theorem memberToParametrized_evaluation :
    memberToParametrized Q t ≫ parametrizedEvaluation Q = memberEvaluation Q t := by
  rw [← evaluation_commutes, ← Category.assoc]
  exact memberToSmooth_evaluation Q t

@[reassoc] theorem memberToParametrized_parameter :
    memberToParametrized Q t ≫ Q.parametrizedSquareToCover =
      Q.reducedMemberInclusion t ≫ Q.memberToCover t := by
  simp only [memberToParametrized, Category.assoc, Q.memberToParametrizedSquare_base]

@[reassoc] theorem memberToParametrized_toC :
    memberToParametrized Q t ≫ Q.parametrizedSquareToSmooth ≫ smoothToC (F := F) =
      Q.reducedMemberToC t := by
  rw [parametrized_toC, ← Category.assoc, memberToParametrized_parameter]
  rw [Category.assoc, ← Q.member_first_overC t]
  rfl

@[reassoc] theorem memberToParametrized_toHom :
    memberToParametrized Q t ≫ Q.parametrizedSquareToCover ≫ Q.toHom =
      Q.reducedMemberToC t ≫ t.val := by
  rw [← Category.assoc, memberToParametrized_parameter, Category.assoc,
    Q.memberToCover_toHom]
  rfl

@[reassoc] theorem memberToParametrized_coordinates :
    memberToParametrized Q t ≫ Parametrized.sourceSquare P Q.coverToC =
      Q.reducedMemberToSquare t := by
  apply pullback.hom_ext
  · simp only [memberToParametrized, Parametrized.sourceSquare, Category.assoc,
      RelativeSquare.evaluation_left,
      StableMaps.FullHomComparison.memberToParametrizedSquare,
      StableMaps.FullHomComparison.reducedMemberToSquare,
      pullback.lift_fst_assoc, pullback.lift_fst]
  · simp only [memberToParametrized, Parametrized.sourceSquare, Category.assoc,
      RelativeSquare.evaluation_right,
      StableMaps.FullHomComparison.memberToParametrizedSquare,
      StableMaps.FullHomComparison.reducedMemberToSquare,
      pullback.lift_snd_assoc, pullback.lift_fst]

def memberPoint
    (z : PointsOver ComplexBase (𝟙 ComplexBase) (Q.ReducedMemberCover t)
      (Q.reducedMemberToC t)) : Point Q :=
  ⟨z.val ≫ memberToParametrized Q t, by
    rw [Category.assoc, memberToParametrized_toC]
    exact z.property⟩

theorem memberPoint_parameter
    (z : PointsOver ComplexBase (𝟙 ComplexBase) (Q.ReducedMemberCover t)
      (Q.reducedMemberToC t)) :
    neighborhoodPoint Q (coverPoint Q (memberPoint Q t z)) = t := by
  apply Subtype.ext
  change ((z.val ≫ memberToParametrized Q t) ≫ Q.parametrizedSquareToCover) ≫
    Q.toHom = t.val
  simp only [Category.assoc]
  rw [memberToParametrized_toHom, ← Category.assoc, z.property, Category.id_comp]

theorem memberPoint_curve
    (z : PointsOver ComplexBase (𝟙 ComplexBase) (Q.ReducedMemberCover t)
      (Q.reducedMemberToC t)) : curve Q (coverPoint Q (memberPoint Q t z)) = N.curveAt t := by
  rw [curve, memberPoint_parameter]

@[reassoc] theorem memberPoint_coordinates
    (z : PointsOver ComplexBase (𝟙 ComplexBase) (Q.ReducedMemberCover t)
      (Q.reducedMemberToC t)) :
    coordinatePair Q (memberPoint Q t z) = z.val ≫ Q.reducedMemberToSquare t := by
  simp only [coordinatePair, memberPoint, Category.assoc, memberToParametrized_coordinates]

/-- Whole-member normalization after the proper surjective reduction
cover. The source square includes the diagonal and every original point. -/
theorem member_left :
    pullSection (memberToParametrized Q t) (left Q) ≫
      (compositionPullback (memberToParametrized Q t) (parametrizedEvaluation Q)
        (memberEvaluation Q t) (memberToParametrized_evaluation Q t)
        (movingPairBundleLeft X.variety X.contact)).hom =
    pullSection (Q.reducedMemberToSquare t) (Curve.leftSection P X (N.curveAt t)) ≫
      (compositionPullback (Q.reducedMemberToSquare t) (curveSquareMap P (N.curveAt t))
        (memberEvaluation Q t) rfl (movingPairBundleLeft X.variety X.contact)).hom := by
  letI : AlgebraicGeometry.IsReduced (Q.ReducedMemberCover t) :=
    Q.reducedMemberCover_reduced t
  letI : LocallyOfFiniteType (Q.reducedMemberToC t) :=
    Q.reducedMemberToC_locallyOfFiniteType t
  apply ComplexPointSectionDetection.section_eq (Q.reducedMemberToC t)
    (MovingPair.leftBundle (memberEvaluation Q t))
  intro z
  have hx : (memberPoint Q t z).val ≫ parametrizedEvaluation Q =
      z.val ≫ memberEvaluation Q t := by
    simp only [memberPoint, Category.assoc, memberToParametrized_evaluation]
  have hz := (coordinatePair_evaluation Q (memberPoint Q t z)).trans hx
  apply (cancel_mono (compositionPullback z.val (memberEvaluation Q t)
    (z.val ≫ memberEvaluation Q t) rfl (movingPairBundleLeft X.variety X.contact)).hom).mp
  have ha := SectionTransport.pull_specialization z.val (memberToParametrized Q t)
    (parametrizedEvaluation Q) (memberPoint Q t z).val (memberEvaluation Q t)
    (z.val ≫ memberEvaluation Q t) rfl (memberToParametrized_evaluation Q t) rfl hx
    (left Q) _ rfl
  have hb := SectionTransport.pull_specialization z.val (Q.reducedMemberToSquare t)
    (curveSquareMap P (N.curveAt t)) (z.val ≫ Q.reducedMemberToSquare t)
    (memberEvaluation Q t) (z.val ≫ memberEvaluation Q t) rfl rfl rfl
    (Category.assoc _ _ _) (Curve.leftSection P X (N.curveAt t)) _ rfl
  rw [← ha, ← hb]
  have hp := point_left Q (memberPoint Q t z) (z.val ≫ memberEvaluation Q t) hx hz
  simpa only [memberPoint_coordinates, memberPoint_curve] using hp

theorem member_right :
    pullSection (memberToParametrized Q t) (right Q) ≫
      (compositionPullback (memberToParametrized Q t) (parametrizedEvaluation Q)
        (memberEvaluation Q t) (memberToParametrized_evaluation Q t)
        (movingPairBundleRight X.variety X.contact)).hom =
    pullSection (Q.reducedMemberToSquare t) (Curve.rightSection P X (N.curveAt t)) ≫
      (compositionPullback (Q.reducedMemberToSquare t) (curveSquareMap P (N.curveAt t))
        (memberEvaluation Q t) rfl (movingPairBundleRight X.variety X.contact)).hom := by
  letI : AlgebraicGeometry.IsReduced (Q.ReducedMemberCover t) :=
    Q.reducedMemberCover_reduced t
  letI : LocallyOfFiniteType (Q.reducedMemberToC t) :=
    Q.reducedMemberToC_locallyOfFiniteType t
  apply ComplexPointSectionDetection.section_eq (Q.reducedMemberToC t)
    (MovingPair.rightBundle (memberEvaluation Q t))
  intro z
  have hx : (memberPoint Q t z).val ≫ parametrizedEvaluation Q =
      z.val ≫ memberEvaluation Q t := by
    simp only [memberPoint, Category.assoc, memberToParametrized_evaluation]
  have hz := (coordinatePair_evaluation Q (memberPoint Q t z)).trans hx
  apply (cancel_mono (compositionPullback z.val (memberEvaluation Q t)
    (z.val ≫ memberEvaluation Q t) rfl (movingPairBundleRight X.variety X.contact)).hom).mp
  have ha := SectionTransport.pull_specialization z.val (memberToParametrized Q t)
    (parametrizedEvaluation Q) (memberPoint Q t z).val (memberEvaluation Q t)
    (z.val ≫ memberEvaluation Q t) rfl (memberToParametrized_evaluation Q t) rfl hx
    (right Q) _ rfl
  have hb := SectionTransport.pull_specialization z.val (Q.reducedMemberToSquare t)
    (curveSquareMap P (N.curveAt t)) (z.val ≫ Q.reducedMemberToSquare t)
    (memberEvaluation Q t) (z.val ≫ memberEvaluation Q t) rfl rfl rfl
    (Category.assoc _ _ _) (Curve.rightSection P X (N.curveAt t)) _ rfl
  rw [← ha, ← hb]
  have hp := point_right Q (memberPoint Q t z) (z.val ≫ memberEvaluation Q t) hx hz
  simpa only [memberPoint_coordinates, memberPoint_curve] using hp

theorem smoothLeft_member :
    pullSection (memberToSmooth Q t) (smoothLeft Q) ≫
      (compositionPullback (memberToSmooth Q t) (smoothEvaluation (F := F))
        (memberEvaluation Q t) (memberToSmooth_evaluation Q t)
        (movingPairBundleLeft X.variety X.contact)).hom =
    pullSection (Q.reducedMemberToSquare t) (Curve.leftSection P X (N.curveAt t)) ≫
      (compositionPullback (Q.reducedMemberToSquare t) (curveSquareMap P (N.curveAt t))
        (memberEvaluation Q t) rfl (movingPairBundleLeft X.variety X.contact)).hom := by
  rw [SectionTransport.pull_specialization (memberToParametrized Q t)
    Q.parametrizedSquareToSmooth (smoothEvaluation (F := F)) (memberToSmooth Q t)
    (parametrizedEvaluation Q) (memberEvaluation Q t) rfl (evaluation_commutes Q)
    (memberToParametrized_evaluation Q t) (memberToSmooth_evaluation Q t)
    (smoothLeft Q) (left Q) (smoothLeft_normalization Q)]
  exact member_left Q t

theorem smoothRight_member :
    pullSection (memberToSmooth Q t) (smoothRight Q) ≫
      (compositionPullback (memberToSmooth Q t) (smoothEvaluation (F := F))
        (memberEvaluation Q t) (memberToSmooth_evaluation Q t)
        (movingPairBundleRight X.variety X.contact)).hom =
    pullSection (Q.reducedMemberToSquare t) (Curve.rightSection P X (N.curveAt t)) ≫
      (compositionPullback (Q.reducedMemberToSquare t) (curveSquareMap P (N.curveAt t))
        (memberEvaluation Q t) rfl (movingPairBundleRight X.variety X.contact)).hom := by
  rw [SectionTransport.pull_specialization (memberToParametrized Q t)
    Q.parametrizedSquareToSmooth (smoothEvaluation (F := F)) (memberToSmooth Q t)
    (parametrizedEvaluation Q) (memberEvaluation Q t) rfl (evaluation_commutes Q)
    (memberToParametrized_evaluation Q t) (memberToSmooth_evaluation Q t)
    (smoothRight Q) (right Q) (smoothRight_normalization Q)]
  exact member_right Q t

theorem extension_left_member (E : (rationalPair Q).Extension) :
    pullSection (memberToFamily Q t) E.leftSection ≫
      (pullbackSquareIso (memberToFamily Q t) F.squareEvaluation
        (Q.reducedMemberToSquare t) (curveSquareMap P (N.curveAt t))
        (memberToFamily_evaluation Q t)
        (movingPairBundleLeft X.variety X.contact)).hom =
      pullSection (Q.reducedMemberToSquare t) (Curve.leftSection P X (N.curveAt t)) := by
  apply (cancel_mono (compositionPullback (Q.reducedMemberToSquare t)
    (curveSquareMap P (N.curveAt t)) (memberEvaluation Q t) rfl
    (movingPairBundleLeft X.variety X.contact)).hom).mp
  rw [Category.assoc, FlatSectionDescent.squareIso_comp_composition]
  rw [SectionTransport.pull_specialization (memberToSmooth Q t)
    F.smoothSquareOpen.ι F.squareEvaluation (memberToFamily Q t)
    (smoothEvaluation (F := F)) (memberEvaluation Q t) (memberToSmooth_ι Q t) rfl
    (memberToSmooth_evaluation Q t) (memberToFamily_evaluation Q t)
    E.leftSection (smoothLeft Q) (extension_left_smooth Q E)]
  exact smoothLeft_member Q t

theorem extension_right_member (E : (rationalPair Q).Extension) :
    pullSection (memberToFamily Q t) E.rightSection ≫
      (pullbackSquareIso (memberToFamily Q t) F.squareEvaluation
        (Q.reducedMemberToSquare t) (curveSquareMap P (N.curveAt t))
        (memberToFamily_evaluation Q t)
        (movingPairBundleRight X.variety X.contact)).hom =
      pullSection (Q.reducedMemberToSquare t) (Curve.rightSection P X (N.curveAt t)) := by
  apply (cancel_mono (compositionPullback (Q.reducedMemberToSquare t)
    (curveSquareMap P (N.curveAt t)) (memberEvaluation Q t) rfl
    (movingPairBundleRight X.variety X.contact)).hom).mp
  rw [Category.assoc, FlatSectionDescent.squareIso_comp_composition]
  rw [SectionTransport.pull_specialization (memberToSmooth Q t)
    F.smoothSquareOpen.ι F.squareEvaluation (memberToFamily Q t)
    (smoothEvaluation (F := F)) (memberEvaluation Q t) (memberToSmooth_ι Q t) rfl
    (memberToSmooth_evaluation Q t) (memberToFamily_evaluation Q t)
    E.rightSection (smoothRight Q) (extension_right_smooth Q E)]
  exact smoothRight_member Q t

/-- An actual extension yields the exact original covered-curve
comparison. The contact value is the original normalized source tensor. -/
def coveredComparison (E : (rationalPair Q).Extension)
    (hp : IsProper F.squareEvaluation)
    (hd : DenseRange (fun y : F.Square => F.squareEvaluation y)) :
    CoveredCurveComparison P X (E.properPair hp hd F.square_integralScheme) (N.curveAt t) where
  cover := Q.ReducedMemberCover t
  toSquare := Q.reducedMemberToSquare t
  proper := Q.reducedMemberToSquare_proper t
  surjective := Q.reducedMemberToSquare_surjective t
  toSource := memberToFamily Q t
  commutes := memberToFamily_evaluation Q t
  identity := by
    rw [E.properPair_value hp hd F.square_integralScheme, pullSection_naturality]
    simp only [Category.assoc]
    rw [pullbackSquare_naturality, ← Category.assoc, extension_left_member Q t E,
      ← pullSection_naturality, Curve.leftSection_contact]

/-- The original covered moving-pair output follows from extension of
the two rational sections. All full-family comparisons are constructed,
rather than added as a field of an auxiliary hypothesis package. -/
def coveredMovingPair (E : (rationalPair Q).Extension)
    (hd : DenseRange (fun y : F.Square => F.squareEvaluation y)) :
    CoveredMovingPair P p X g where
  properPair := E.properPair F.squareEvaluation_proper hd F.square_integralScheme
  fullFamily := N
  comparison := fun t => coveredComparison Q t E F.squareEvaluation_proper hd

end SmoothFamily

end LeBrunSalamon.Construction.FamilyBivectors

end
