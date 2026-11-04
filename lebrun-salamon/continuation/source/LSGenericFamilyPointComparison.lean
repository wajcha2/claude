import LSFamilyBaseChange
import LSParametrizedBaseChange
import LSFamilySmoothCoordinates
import LSFieldParametrization
import LSFamilyReparametrizationFibres

/-!
# Comparison with actual field-valued parametrizations

The normalized descended sections are first compared over every actual
point of the original parametrization cover, over an arbitrary scheme.
Field-valued alternative parametrizations are compared after the actual
residue-field extension of that cover. No complex-point argument is
applied to a fraction-field spectrum.
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

namespace LeBrunSalamon.Construction.FamilyBivectors

namespace SmoothFamily

variable {P : ProjectiveLineOverC} {p : ProjectiveLinePoint P}
variable {n : ℕ} {X : ContactFanoManifold n} {g : VeryFreeContactConic P p X}
variable {N : FullConicNeighborhood P p X g}
variable {F : StableMaps.ProjectiveNodalFamily P p X.variety X.contact.sequence.line 2}
variable (Q : StableMaps.FullHomComparison P p X.variety N.homSpace N.neighborhood
  X.contact.sequence.line 2 F)

theorem cover_locallyOfFiniteType : LocallyOfFiniteType Q.coverToC := by
  letI : IsProper F.toC := F.baseProper
  letI : Smooth Q.toSmooth := Q.smooth
  have hc : Q.coverToC = (Q.toSmooth ≫ F.smoothOpen.ι) ≫ F.toC := Q.overC.symm
  rw [hc]
  infer_instance

theorem cover_reduced : AlgebraicGeometry.IsReduced Q.cover := by
  letI : IsIntegral F.base := F.baseIntegral
  letI : IsLocallyNoetherian F.base := F.base_locallyNoetherian
  letI : AlgebraicGeometry.IsReduced F.smoothOpen.toScheme :=
    isReduced_of_isOpenImmersion F.smoothOpen.ι
  letI : IsLocallyNoetherian F.smoothOpen.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian F.smoothOpen.ι
  letI : Smooth Q.toSmooth := Q.smooth
  letI : GeometricallyIntegral Q.toSmooth := Q.geometricallyIntegral
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian Q.toSmooth

/-- The curve data used by reparametrization come from the original
full Hom family; no new nonconstancy hypothesis is introduced. -/
def nonconstantFamily : FamilyReparametrization.NonconstantFamily P Q.coverToC X
    (evaluation Q) where
  curve := curve Q
  curve_spec := fibre_evaluation Q

variable {T : Scheme} (sT : T ⟶ ComplexBase)
variable (q : PointsOver T sT Q.cover Q.coverToC)

abbrev atPointEvaluation : Parametrized.Source P sT ⟶ X.variety.scheme :=
  Q.atPointSource sT q ≫ evaluation Q

theorem atPointEvaluation_overC :
    atPointEvaluation Q sT q ≫ X.variety.structureMap =
      Parametrized.parameter P sT ≫ sT := by
  rw [atPointEvaluation, Category.assoc, evaluation_overC, ← Category.assoc,
    Q.atPointSource_parameter, Category.assoc, q.property]

def atPointSquare : Parametrized.Square P sT ⟶ Q.ParametrizedSquare :=
  RelativeSquare.map (Parametrized.parameter P sT) Q.parametrizedParameter
    (Q.atPointSource sT q) q.val (Q.atPointSource_parameter sT q)

def atPointSmooth : Parametrized.Square P sT ⟶ F.smoothSquareOpen.toScheme :=
  atPointSquare Q sT q ≫ Q.parametrizedSquareToSmooth

abbrev atPointSquareEvaluation : Parametrized.Square P sT ⟶
    SelfProduct X.variety.structureMap :=
  ParametrizedContact.evaluationSquare P sT X (atPointEvaluation Q sT q)
    (atPointEvaluation_overC Q sT q)

@[reassoc] theorem atPointSquare_evaluation :
    atPointSquare Q sT q ≫ parametrizedEvaluation Q = atPointSquareEvaluation Q sT q :=
  RelativeSquare.map_evaluation (Parametrized.parameter P sT) Q.parametrizedParameter
    (Q.atPointSource sT q) q.val (Q.atPointSource_parameter sT q)
    X.variety.structureMap sT Q.coverToC (atPointEvaluation Q sT q) (evaluation Q)
    (atPointEvaluation_overC Q sT q) (evaluation_overC Q) rfl

@[reassoc] theorem atPointSmooth_evaluation :
    atPointSmooth Q sT q ≫ smoothEvaluation (F := F) = atPointSquareEvaluation Q sT q := by
  rw [atPointSmooth, Category.assoc, evaluation_commutes, atPointSquare_evaluation]

/-- Universal base change of the normalized left section to an actual
point of Q over an arbitrary scheme. -/
theorem atPoint_left :
    pullSection (atPointSquare Q sT q) (left Q) ≫
      (compositionPullback (atPointSquare Q sT q) (parametrizedEvaluation Q)
        (atPointSquareEvaluation Q sT q) (atPointSquare_evaluation Q sT q)
        (movingPairBundleLeft X.variety X.contact)).hom =
      ParametrizedContact.leftSection P sT X (atPointEvaluation Q sT q)
        (atPointEvaluation_overC Q sT q) :=
  ParametrizedContact.leftSection_baseChange P sT Q.coverToC q.val q.property
    (Q.atPointSource sT q) (Q.atPointSource_first sT q) (Q.atPointSource_parameter sT q)
    X (evaluation Q) (evaluation_overC Q) (atPointEvaluation Q sT q)
    (atPointEvaluation_overC Q sT q) rfl (atPointSquare Q sT q)
    (RelativeSquare.map_left _ _ _ _ _) (RelativeSquare.map_right _ _ _ _ _)
    (atPointSquare_evaluation Q sT q)

theorem atPoint_right :
    pullSection (atPointSquare Q sT q) (right Q) ≫
      (compositionPullback (atPointSquare Q sT q) (parametrizedEvaluation Q)
        (atPointSquareEvaluation Q sT q) (atPointSquare_evaluation Q sT q)
        (movingPairBundleRight X.variety X.contact)).hom =
      ParametrizedContact.rightSection P sT X (atPointEvaluation Q sT q)
        (atPointEvaluation_overC Q sT q) :=
  ParametrizedContact.rightSection_baseChange P sT Q.coverToC q.val q.property
    (Q.atPointSource sT q) (Q.atPointSource_first sT q) (Q.atPointSource_parameter sT q)
    X (evaluation Q) (evaluation_overC Q) (atPointEvaluation Q sT q)
    (atPointEvaluation_overC Q sT q) rfl (atPointSquare Q sT q)
    (RelativeSquare.map_left _ _ _ _ _) (RelativeSquare.map_right _ _ _ _ _)
    (atPointSquare_evaluation Q sT q)

end SmoothFamily

end LeBrunSalamon.Construction.FamilyBivectors

end
