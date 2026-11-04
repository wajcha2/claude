import LSFamilyDescentFibres
import LSOpenSectionTransport

/-!
# Smooth-family source coordinates and fibre tensor comparisons.

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

end SmoothFamily

end LeBrunSalamon.Construction.FamilyBivectors

end
