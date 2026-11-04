import LSFamilySmoothCoordinates
import LSArcParametrization
import LSRationalOpenTransport

/-!
# Regularity of the descended moving pair on every actual formal arc

Both complete source normal forms carry regular model sections.  Their
whole generic squares agree with the original parametrized tensors.
The arbitrary-field comparison identifies those tensors with the
descended smooth-family sections; the actual two marked points then
identify their generic values.  Finally the actual-open transport
theorem gives regularity in the original `FormalArcs.Regular` sense.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction.FormalArcComparison

local notation "Model" => LeBrunSalamon.Construction.StableMaps.FormalArcs.Model

open StableMaps StableMaps.FormalArcs StableMaps.TraitPullback
open FamilyBivectors FormalArcSections TraitContact

variable {n : ℕ} {X : ContactFanoManifold n}

section ModelTransport

variable (F : ProjectiveNodalFamily Lines.P Lines.marking
  X.variety X.contact.sequence.line 2)
variable (gamma : PointsOver Trait toC F.Square (F.squareToBase ≫ F.toC))
variable {M : Scheme} (piM : M ⟶ Trait)
variable (u : Source F (baseArc F gamma) ≅ M)
variable (hu : u.hom ≫ piM = parameter F (baseArc F gamma))
variable (k : Generic.P1 ⟶ M)
variable (hk : IsPullback k Generic.projection piM genericPoint)

def genericEvaluation : Generic.P1 ⟶ X.variety.scheme :=
  k ≫ Transport.evaluation F gamma u

include hu hk in
@[reassoc] theorem genericEvaluation_overC :
    genericEvaluation F gamma u k ≫ X.variety.structureMap =
      Generic.projection ≫ (genericPoint ≫ toC) := by
  rw [genericEvaluation, Category.assoc,
    Transport.evaluation_overC F gamma piM u hu, ← Category.assoc,
    hk.w, Category.assoc]

def genericEvaluationSquare : Parametrized.Square Lines.P (genericPoint ≫ toC) ⟶
    SelfProduct X.variety.structureMap :=
  ParametrizedContact.evaluationSquare Lines.P (genericPoint ≫ toC) X
    (genericEvaluation F gamma u k) (genericEvaluation_overC F gamma piM u hu k hk)

@[reassoc] theorem family_evaluation :
    Generic.toFamily F gamma u k ≫ F.evaluation = genericEvaluation F gamma u k := by
  simp only [Generic.toFamily, Generic.inverseSource, genericEvaluation,
    Transport.evaluation, TraitPullback.evaluation, Category.assoc]

@[reassoc] theorem toModelSquare_evaluation :
    Generic.toModelSquare piM k hk ≫ Transport.evaluationSquare F gamma piM u hu =
      genericEvaluationSquare F gamma piM u hu k hk :=
  RelativeSquare.map_evaluation Generic.projection piM k genericPoint hk.w
    X.variety.structureMap (genericPoint ≫ toC) toC
    (genericEvaluation F gamma u k) (Transport.evaluation F gamma u)
    (genericEvaluation_overC F gamma piM u hu k hk)
    (Transport.evaluation_overC F gamma piM u hu) rfl

variable (b : GenericPoint ⟶ F.smoothOpen.toScheme)
variable (hb : b ≫ F.smoothOpen.ι = genericPoint ≫ (baseArc F gamma).val)

include hb in
theorem smoothBase_overC : (b ≫ F.smoothOpen.ι) ≫ F.toC = genericPoint ≫ toC := by
  rw [hb, Category.assoc, (baseArc F gamma).property]

include hu hk hb in
theorem family_isPullback :
    IsPullback (Generic.toFamily F gamma u k) Generic.projection F.parameter
      (b ≫ F.smoothOpen.ι) := by
  rw [hb]
  exact Generic.toFamily_isPullback F gamma piM u hu k hk

@[reassoc] theorem toSmoothSquare_family :
    Generic.toSmoothSquare F gamma piM u hu k hk b hb ≫ F.smoothSquareOpen.ι =
      RelativeSquare.map Generic.projection F.parameter (Generic.toFamily F gamma u k)
        (b ≫ F.smoothOpen.ι) (family_isPullback F gamma piM u hu k hk b hb).w := by
  simpa only [Generic.toFamilySquare, hb] using
    Generic.toSmoothSquare_inclusion F gamma piM u hu k hk b hb

@[reassoc] theorem toSmoothSquare_evaluation :
    Generic.toSmoothSquare F gamma piM u hu k hk b hb ≫
      SmoothFamily.smoothEvaluation (F := F) =
        genericEvaluationSquare F gamma piM u hu k hk := by
  rw [SmoothFamily.smoothEvaluation, ← Category.assoc,
    Generic.toSmoothSquare_inclusion]
  exact RelativeSquare.map_evaluation Generic.projection F.parameter
    (Generic.toFamily F gamma u k) (genericPoint ≫ (baseArc F gamma).val)
    (Generic.toFamily_parameter F gamma piM u hu k hk)
    X.variety.structureMap (genericPoint ≫ toC) F.toC
    (genericEvaluation F gamma u k) F.evaluation
    (genericEvaluation_overC F gamma piM u hu k hk) F.overC
    (family_evaluation F gamma u k)

def genericToSmooth : GenericPoint ⟶ F.smoothSquareOpen.toScheme :=
  Generic.pair F gamma piM u hu k hk ≫
    Generic.toSmoothSquare F gamma piM u hu k hk b hb

@[reassoc] theorem genericToSmooth_inclusion :
    genericToSmooth F gamma piM u hu k hk b hb ≫ F.smoothSquareOpen.ι =
      genericPoint ≫ gamma.val := by
  simpa only [genericToSmooth, Category.assoc] using
    Generic.pair_toSmoothSquare_inclusion F gamma piM u hu k hk b hb

@[reassoc] theorem genericToSmooth_evaluation :
    genericToSmooth F gamma piM u hu k hk b hb ≫
      SmoothFamily.smoothEvaluation (F := F) =
        (genericPoint ≫ gamma.val) ≫ F.squareEvaluation := by
  rw [SmoothFamily.smoothEvaluation, ← Category.assoc, genericToSmooth_inclusion]

include hb in
@[reassoc] theorem genericPair_evaluation :
    Generic.pair F gamma piM u hu k hk ≫ genericEvaluationSquare F gamma piM u hu k hk =
      (genericPoint ≫ gamma.val) ≫ F.squareEvaluation := by
  rw [← toSmoothSquare_evaluation F gamma piM u hu k hk b hb, ← Category.assoc]
  exact genericToSmooth_evaluation F gamma piM u hu k hk b hb

/-- Canonical transport from a whole model square and from the original
smooth open gives the same value on the actual generic marked pair.
All hypotheses are explicit equalities of actual sections. -/
theorem model_normalization {E : OModule (SelfProduct X.variety.structureMap)}
    (v : AlgebraicSection (pullbackModule (Transport.evaluationSquare F gamma piM u hu) E))
    (s : AlgebraicSection (pullbackModule (SmoothFamily.smoothEvaluation (F := F)) E))
    (vK : AlgebraicSection (pullbackModule (genericEvaluationSquare F gamma piM u hu k hk) E))
    (hv : pullSection (Generic.toModelSquare piM k hk) v ≫
      (compositionPullback (Generic.toModelSquare piM k hk)
        (Transport.evaluationSquare F gamma piM u hu)
        (genericEvaluationSquare F gamma piM u hu k hk)
        (toModelSquare_evaluation F gamma piM u hu k hk) E).hom = vK)
    (hs : pullSection (Generic.toSmoothSquare F gamma piM u hu k hk b hb) s ≫
      (compositionPullback (Generic.toSmoothSquare F gamma piM u hu k hk b hb)
        (SmoothFamily.smoothEvaluation (F := F))
        (genericEvaluationSquare F gamma piM u hu k hk)
        (toSmoothSquare_evaluation F gamma piM u hu k hk b hb) E).hom = vK) :
    pullSection genericPoint (Transport.section F gamma piM u hu v) ≫
      (compositionPullback genericPoint gamma.val (genericPoint ≫ gamma.val) rfl
        (pullbackModule F.squareEvaluation E)).hom =
    pullSection (genericToSmooth F gamma piM u hu k hk b hb)
        (s ≫ (compositionPullback F.smoothSquareOpen.ι F.squareEvaluation
          (SmoothFamily.smoothEvaluation (F := F)) rfl E).inv) ≫
      (compositionPullback (genericToSmooth F gamma piM u hu k hk b hb)
        F.smoothSquareOpen.ι (genericPoint ≫ gamma.val)
        (genericToSmooth_inclusion F gamma piM u hu k hk b hb)
        (pullbackModule F.squareEvaluation E)).hom := by
  let r := (genericPoint ≫ gamma.val) ≫ F.squareEvaluation
  have hm : (genericPoint ≫ Transport.pair F gamma piM u hu) ≫
      Transport.evaluationSquare F gamma piM u hu = r := by
    rw [Category.assoc, Transport.pair_evaluation]
    rfl
  have hp := genericPair_evaluation F gamma piM u hu k hk b hb
  have hg := genericToSmooth_evaluation F gamma piM u hu k hk b hb
  have hmodel := SectionTransport.pull_specialization
    (Generic.pair F gamma piM u hu k hk) (Generic.toModelSquare piM k hk)
    (Transport.evaluationSquare F gamma piM u hu)
    (genericPoint ≫ Transport.pair F gamma piM u hu)
    (genericEvaluationSquare F gamma piM u hu k hk) r
    (Generic.pair_toModelSquare F gamma piM u hu k hk)
    (toModelSquare_evaluation F gamma piM u hu k hk) hp hm v vK hv
  have hsmooth := SectionTransport.pull_specialization
    (Generic.pair F gamma piM u hu k hk)
    (Generic.toSmoothSquare F gamma piM u hu k hk b hb)
    (SmoothFamily.smoothEvaluation (F := F))
    (genericToSmooth F gamma piM u hu k hk b hb)
    (genericEvaluationSquare F gamma piM u hu k hk) r rfl
    (toSmoothSquare_evaluation F gamma piM u hu k hk b hb) hp hg s vK hs
  apply (cancel_mono (compositionPullback (genericPoint ≫ gamma.val)
    F.squareEvaluation r rfl E).hom).mp
  simp only [Category.assoc]
  rw [Transport.section, pullSection_naturality]
  simp only [Category.assoc]
  rw [SectionTransport.square_comp genericPoint (Transport.pair F gamma piM u hu)
    (Transport.evaluationSquare F gamma piM u hu) gamma.val F.squareEvaluation
    (Transport.pair_evaluation F gamma piM u hu) (genericPoint ≫ gamma.val) rfl r rfl hm E]
  rw [← Category.assoc, compositionPullback_sections, hmodel]
  rw [SectionTransport.inverse_composition_value
    (genericToSmooth F gamma piM u hu k hk b hb) F.smoothSquareOpen.ι
    F.squareEvaluation (SmoothFamily.smoothEvaluation (F := F)) rfl
    (genericPoint ≫ gamma.val) (genericToSmooth_inclusion F gamma piM u hu k hk b hb)
    r rfl hg s]
  exact hsmooth.symm

end ModelTransport

end LeBrunSalamon.Construction.FormalArcComparison

end
