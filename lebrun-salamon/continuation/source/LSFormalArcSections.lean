import LSRegularModelPair
import LSStableFamilyTraits

/-!
# Whole-trait sections obtained from the actual source normal forms

An arc of the complete stable source square retains both of its source
points.  The actual source isomorphism carries those points to the model
square.  Pullback of the model sections then gives globally regular
sections of the two original target bundles along the entire trait.

This file records the construction and its canonical transport.  The
additional equality with the descended rational pair on the generic
open is still required before invoking formal-arc regularity.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction.FormalArcSections

local notation "Model" => LeBrunSalamon.Construction.StableMaps.FormalArcs.Model

open StableMaps StableMaps.FormalArcs StableMaps.TraitPullback
open FamilyBivectors TraitContact

variable {n : ℕ} {X : ContactFanoManifold n}
variable (F : ProjectiveNodalFamily Lines.P Lines.marking
  X.variety X.contact.sequence.line 2)
variable (gamma : PointsOver Trait toC F.Square (F.squareToBase ≫ F.toC))

namespace Transport

variable {M : Scheme} (piM : M ⟶ Trait)
variable (u : Source F (baseArc F gamma) ≅ M)
variable (hu : u.hom ≫ piM = parameter F (baseArc F gamma))

include hu in
@[reassoc] theorem inverse_parameter :
    u.inv ≫ parameter F (baseArc F gamma) = piM := by
  rw [← hu, ← Category.assoc, u.inv_hom_id, Category.id_comp]

def evaluation : M ⟶ X.variety.scheme :=
  u.inv ≫ TraitPullback.evaluation F (baseArc F gamma)

include hu in
@[reassoc] theorem evaluation_overC :
    evaluation F gamma u ≫ X.variety.structureMap = piM ≫ toC := by
  rw [evaluation, Category.assoc, TraitPullback.evaluation_overC,
    ← Category.assoc, inverse_parameter F gamma piM u hu]

def first : Trait ⟶ M := firstSection F gamma ≫ u.hom
def second : Trait ⟶ M := secondSection F gamma ≫ u.hom

include hu in
@[reassoc] theorem first_parameter : first F gamma u ≫ piM = 𝟙 Trait := by
  rw [first, Category.assoc, hu, firstSection_parameter]

include hu in
@[reassoc] theorem second_parameter : second F gamma u ≫ piM = 𝟙 Trait := by
  rw [second, Category.assoc, hu, secondSection_parameter]

def pair : Trait ⟶ RelativeSquare.Space piM :=
  pullback.lift (first F gamma u) (second F gamma u)
    ((first_parameter F gamma piM u hu).trans
      (second_parameter F gamma piM u hu).symm)

@[reassoc] theorem pair_first : pair F gamma piM u hu ≫
    RelativeSquare.left piM = first F gamma u := pullback.lift_fst _ _ _

@[reassoc] theorem pair_second : pair F gamma piM u hu ≫
    RelativeSquare.right piM = second F gamma u := pullback.lift_snd _ _ _

def evaluationSquare : RelativeSquare.Space piM ⟶
    SelfProduct X.variety.structureMap :=
  RelativeSquare.evaluation piM X.variety.structureMap toC
    (evaluation F gamma u) (evaluation_overC F gamma piM u hu)

/-- The model square and the original total-space arc have exactly the
same target pair, including when either source point is the node. -/
@[reassoc] theorem pair_evaluation :
    pair F gamma piM u hu ≫ evaluationSquare F gamma piM u hu =
      gamma.val ≫ F.squareEvaluation := by
  apply pullback.hom_ext
  · change (pair F gamma piM u hu ≫ evaluationSquare F gamma piM u hu) ≫
        firstProjection X.variety.structureMap =
      (gamma.val ≫ F.squareEvaluation) ≫ firstProjection X.variety.structureMap
    rw [evaluationSquare, Category.assoc, RelativeSquare.evaluation_left,
      ← Category.assoc, pair_first]
    simp only [first, evaluation, Category.assoc,
      u.hom_inv_id_assoc, firstSection_evaluation]
  · change (pair F gamma piM u hu ≫ evaluationSquare F gamma piM u hu) ≫
        secondProjection X.variety.structureMap =
      (gamma.val ≫ F.squareEvaluation) ≫ secondProjection X.variety.structureMap
    rw [evaluationSquare, Category.assoc, RelativeSquare.evaluation_right,
      ← Category.assoc, pair_second]
    simp only [second, evaluation, Category.assoc,
      u.hom_inv_id_assoc, secondSection_evaluation]

def «section» {E : OModule (SelfProduct X.variety.structureMap)}
    (v : AlgebraicSection (pullbackModule (evaluationSquare F gamma piM u hu) E)) :
    AlgebraicSection (pullbackModule gamma.val (pullbackModule F.squareEvaluation E)) :=
  pullSection (pair F gamma piM u hu) v ≫
    (pullbackSquareIso (pair F gamma piM u hu)
      (evaluationSquare F gamma piM u hu) gamma.val F.squareEvaluation
      (pair_evaluation F gamma piM u hu) E).hom

@[reassoc] theorem section_map
    {E G : OModule (SelfProduct X.variety.structureMap)} (f : E ⟶ G)
    (v : AlgebraicSection (pullbackModule (evaluationSquare F gamma piM u hu) E)) :
    «section» F gamma piM u hu v ≫
        (Scheme.Modules.pullback gamma.val).map
          ((Scheme.Modules.pullback F.squareEvaluation).map f) =
      «section» F gamma piM u hu
        (v ≫ (Scheme.Modules.pullback (evaluationSquare F gamma piM u hu)).map f) := by
  unfold «section»
  rw [Category.assoc, ← FamilyBivectors.pullbackSquare_naturality]
  simp only [pullSection, restrictSection, Functor.map_comp, Category.assoc]

/-- Equality of the two contact images is preserved by the exact
canonical pullback square, with no target frame choice. -/
theorem common
    (v : AlgebraicSection (pullbackModule (evaluationSquare F gamma piM u hu)
      (movingPairBundleLeft X.variety X.contact)))
    (w : AlgebraicSection (pullbackModule (evaluationSquare F gamma piM u hu)
      (movingPairBundleRight X.variety X.contact)))
    (h : v ≫ (Scheme.Modules.pullback (evaluationSquare F gamma piM u hu)).map
        (movingPairContactLeft X.variety X.contact) =
      w ≫ (Scheme.Modules.pullback (evaluationSquare F gamma piM u hu)).map
        (movingPairContactRight X.variety X.contact)) :
    «section» F gamma piM u hu v ≫
        (Scheme.Modules.pullback gamma.val).map (MovingPair.leftContact F.squareEvaluation) =
      «section» F gamma piM u hu w ≫
        (Scheme.Modules.pullback gamma.val).map (MovingPair.rightContact F.squareEvaluation) := by
  change «section» F gamma piM u hu v ≫
      (Scheme.Modules.pullback gamma.val).map
        ((Scheme.Modules.pullback F.squareEvaluation).map
          (movingPairContactLeft X.variety X.contact)) =
    «section» F gamma piM u hu w ≫
      (Scheme.Modules.pullback gamma.val).map
        ((Scheme.Modules.pullback F.squareEvaluation).map
          (movingPairContactRight X.variety X.contact))
  rw [section_map, section_map, h]

/-- Transport the actual line isomorphism from the source normal form
back to the model.  The evaluation pullback is normalized by composition. -/
def line {L : LineBundle M}
    (ell : (TraitPullback.line F (baseArc F gamma)).sheaf ≅
      pullbackModule u.hom L.sheaf) :
    L.sheaf ≅ pullbackModule (evaluation F gamma u) X.contact.sequence.line.sheaf :=
  ((Scheme.Modules.pullback u.inv).mapIso ell ≪≫
    compositionPullback u.inv u.hom (𝟙 M) u.inv_hom_id L.sheaf ≪≫
      (Scheme.Modules.pullbackId M).app L.sheaf).symm ≪≫
    compositionPullback u.inv (TraitPullback.evaluation F (baseArc F gamma))
      (evaluation F gamma u) rfl X.contact.sequence.line.sheaf

end Transport

namespace Nodal

variable (S : Smoothing.StandardSource) (a : Coefficients)
variable (u : Source F (baseArc F gamma) ≅ Model S a)
variable (hu : u.hom ≫ modelProjection S a = parameter F (baseArc F gamma))
variable (ell : (TraitPullback.line F (baseArc F gamma)).sheaf ≅
  pullbackModule u.hom (modelLine S a).sheaf)

def left (c : Coefficients) :
    AlgebraicSection (pullbackModule gamma.val (MovingPair.leftBundle F.squareEvaluation).sheaf) :=
  Transport.section F gamma (modelProjection S a) u hu
    (RegularModel.leftSection X S a (Transport.evaluation F gamma u)
      (Transport.evaluation_overC F gamma (modelProjection S a) u hu)
      (Transport.line F gamma u ell) c)

def right (c : Coefficients) :
    AlgebraicSection (pullbackModule gamma.val (MovingPair.rightBundle F.squareEvaluation).sheaf) :=
  Transport.section F gamma (modelProjection S a) u hu
    (RegularModel.rightSection X S a (Transport.evaluation F gamma u)
      (Transport.evaluation_overC F gamma (modelProjection S a) u hu)
      (Transport.line F gamma u ell) c)

theorem common_exists (ha : a ≠ 0) :
    ∃ c : Coefficients,
      ContactScalar.morphism X S a (Transport.evaluation F gamma u)
          (Transport.evaluation_overC F gamma (modelProjection S a) u hu) =
        GlobalScalars.scalarEnd (modelLine S a).sheaf
          ((modelProjection S a).appTop (coefficientSection a)) ≫
            RegularModel.dividedContact X S a (Transport.evaluation F gamma u)
              (Transport.line F gamma u ell) c ∧
      left F gamma S a u hu ell c ≫
          (Scheme.Modules.pullback gamma.val).map (MovingPair.leftContact F.squareEvaluation) =
        right F gamma S a u hu ell c ≫
          (Scheme.Modules.pullback gamma.val).map (MovingPair.rightContact F.squareEvaluation) := by
  obtain ⟨c, hc, heq⟩ := RegularModel.regularPair_exists X S a
    (Transport.evaluation F gamma u)
    (Transport.evaluation_overC F gamma (modelProjection S a) u hu)
    (Transport.line F gamma u ell) ha
  exact ⟨c, hc, Transport.common F gamma (modelProjection S a) u hu _ _ heq⟩

end Nodal

namespace Smooth

variable (u : Source F (baseArc F gamma) ≅ SmoothModel)
variable (hu : u.hom ≫ smoothProjection = parameter F (baseArc F gamma))

def left :
    AlgebraicSection (pullbackModule gamma.val (MovingPair.leftBundle F.squareEvaluation).sheaf) :=
  Transport.section F gamma smoothProjection u hu
    (ParametrizedContact.leftSection Lines.P toC X (Transport.evaluation F gamma u)
      (Transport.evaluation_overC F gamma smoothProjection u hu))

def right :
    AlgebraicSection (pullbackModule gamma.val (MovingPair.rightBundle F.squareEvaluation).sheaf) :=
  Transport.section F gamma smoothProjection u hu
    (ParametrizedContact.rightSection Lines.P toC X (Transport.evaluation F gamma u)
      (Transport.evaluation_overC F gamma smoothProjection u hu))

theorem common :
    left F gamma u hu ≫
        (Scheme.Modules.pullback gamma.val).map (MovingPair.leftContact F.squareEvaluation) =
      right F gamma u hu ≫
        (Scheme.Modules.pullback gamma.val).map (MovingPair.rightContact F.squareEvaluation) :=
  Transport.common F gamma smoothProjection u hu _ _
    (ParametrizedContact.commonContact Lines.P toC X (Transport.evaluation F gamma u)
      (Transport.evaluation_overC F gamma smoothProjection u hu))

end Smooth

end LeBrunSalamon.Construction.FormalArcSections

end
