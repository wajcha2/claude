import LSFamilyBaseChange
import LSParametrizedBaseChange
import LSFamilySmoothNormalization
import LSFieldParametrization
import LSFamilyReparametrization
import LSGenericFamilyPointComparison
import LSGenericFamilyFieldTransport

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

variable {T : Scheme} (sT : T ⟶ ComplexBase)
variable (q : PointsOver T sT Q.cover Q.coverToC)

/-- The descended section agrees with the actual parametrized tensor
on the entire source square over the supplied test base. -/
theorem smoothLeft_atPoint :
    pullSection (atPointSmooth Q sT q) (smoothLeft Q) ≫
      (compositionPullback (atPointSmooth Q sT q) (smoothEvaluation (F := F))
        (atPointSquareEvaluation Q sT q) (atPointSmooth_evaluation Q sT q)
        (movingPairBundleLeft X.variety X.contact)).hom =
      ParametrizedContact.leftSection P sT X (atPointEvaluation Q sT q)
        (atPointEvaluation_overC Q sT q) := by
  rw [SectionTransport.pull_specialization (atPointSquare Q sT q)
    Q.parametrizedSquareToSmooth (smoothEvaluation (F := F)) (atPointSmooth Q sT q)
    (parametrizedEvaluation Q) (atPointSquareEvaluation Q sT q) rfl (evaluation_commutes Q)
    (atPointSquare_evaluation Q sT q) (atPointSmooth_evaluation Q sT q)
    (smoothLeft Q) (left Q) (smoothLeft_normalization Q)]
  exact atPoint_left Q sT q

theorem smoothRight_atPoint :
    pullSection (atPointSmooth Q sT q) (smoothRight Q) ≫
      (compositionPullback (atPointSmooth Q sT q) (smoothEvaluation (F := F))
        (atPointSquareEvaluation Q sT q) (atPointSmooth_evaluation Q sT q)
        (movingPairBundleRight X.variety X.contact)).hom =
      ParametrizedContact.rightSection P sT X (atPointEvaluation Q sT q)
        (atPointEvaluation_overC Q sT q) := by
  rw [SectionTransport.pull_specialization (atPointSquare Q sT q)
    Q.parametrizedSquareToSmooth (smoothEvaluation (F := F)) (atPointSmooth Q sT q)
    (parametrizedEvaluation Q) (atPointSquareEvaluation Q sT q) rfl (evaluation_commutes Q)
    (atPointSquare_evaluation Q sT q) (atPointSmooth_evaluation Q sT q)
    (smoothRight Q) (right Q) (smoothRight_normalization Q)]
  exact atPoint_right Q sT q

@[reassoc] theorem atPointSmooth_family :
    atPointSmooth Q sT q ≫ F.smoothSquareOpen.ι =
      RelativeSquare.map (Parametrized.parameter P sT) F.parameter
        (Q.atPointMap sT q) (q.val ≫ Q.coverToBase) (Q.atPointMap_parameter sT q) := by
  rw [atPointSmooth, Category.assoc, Q.parametrizedSquareToSmooth_ι]
  apply pullback.hom_ext
  · simp only [atPointSquare, Category.assoc,
      Q.parametrizedSquareToFamily_first, RelativeSquare.map_left,
      RelativeSquare.map_left_assoc, StableMaps.FullHomComparison.atPointMap]
  · simp only [atPointSquare, Category.assoc,
      Q.parametrizedSquareToFamily_second, RelativeSquare.map_right,
      RelativeSquare.map_right_assoc, StableMaps.FullHomComparison.atPointMap]

end SmoothFamily

namespace CartesianParametrization

variable {P : ProjectiveLineOverC} {p : ProjectiveLinePoint P}
variable {n : ℕ} {X : ContactFanoManifold n} {g : VeryFreeContactConic P p X}
variable {N : FullConicNeighborhood P p X g}
variable {F : StableMaps.ProjectiveNodalFamily P p X.variety X.contact.sequence.line 2}
variable (Q : StableMaps.FullHomComparison P p X.variety N.homSpace N.neighborhood
  X.contact.sequence.line 2 F)
variable {T : Scheme} (sT : T ⟶ ComplexBase)
variable (q : PointsOver T sT Q.cover Q.coverToC)
variable (b : T ⟶ F.smoothOpen.toScheme) (hq : q.val ≫ Q.toSmooth = b)
variable (k : Parametrized.Source P sT ⟶ F.source)
variable (hk : IsPullback k (Parametrized.parameter P sT) F.parameter (b ≫ F.smoothOpen.ι))

include hq in
theorem base_equality : q.val ≫ Q.coverToBase = b ≫ F.smoothOpen.ι := by
  rw [StableMaps.FullHomComparison.coverToBase, ← Category.assoc, hq]

/-- The two parametrizations are compared through the same literal
fibre of F. No bijection of geometric points is substituted for this
scheme isomorphism. -/
def transition : Parametrized.Source P sT ≅ Parametrized.Source P sT :=
  hk.isoPullback ≪≫ pullback.congrHom rfl (base_equality Q sT q b hq).symm ≪≫
    (Q.atPointIso sT q).symm

@[reassoc] theorem transition_fibre :
    (transition Q sT q b hq k hk).hom ≫ (Q.atPointIso sT q).hom =
      hk.isoPullback.hom ≫ (pullback.congrHom rfl (base_equality Q sT q b hq).symm).hom := by
  simp only [transition, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

@[reassoc] theorem transition_source :
    (transition Q sT q b hq k hk).hom ≫ Q.atPointMap sT q = k := by
  rw [← Q.atPointIso_source sT q, ← Category.assoc, transition_fibre]
  simp only [Category.assoc, pullback.congrHom_hom, pullback.map,
    pullback.lift_fst, Category.comp_id, hk.isoPullback_hom_fst]

@[reassoc] theorem transition_parameter :
    (transition Q sT q b hq k hk).hom ≫ Parametrized.parameter P sT =
      Parametrized.parameter P sT := by
  change (transition Q sT q b hq k hk).hom ≫ pullback.snd P.structureMap sT =
    pullback.snd P.structureMap sT
  rw [← Q.atPointIso_parameter sT q, ← Category.assoc, transition_fibre]
  simp only [Category.assoc, pullback.congrHom_hom, pullback.map,
    pullback.lift_snd, Category.comp_id, hk.isoPullback_hom_snd,
    StableMaps.FullHomComparison.atPointIso_parameter, Parametrized.parameter]

abbrev evaluation : Parametrized.Source P sT ⟶ X.variety.scheme := k ≫ F.evaluation

include hq hk in
theorem evaluation_overC :
    evaluation (F := F) sT k ≫ X.variety.structureMap =
      Parametrized.parameter P sT ≫ sT := by
  have hb : (b ≫ F.smoothOpen.ι) ≫ F.toC = sT := by
    rw [← base_equality Q sT q b hq]
    simpa only [Category.assoc, StableMaps.FullHomComparison.coverToBase,
      ← Q.overC] using q.property
  rw [evaluation, Category.assoc, F.overC, ← Category.assoc, hk.w, Category.assoc, hb]

@[reassoc] theorem transition_evaluation :
    (transition Q sT q b hq k hk).hom ≫ SmoothFamily.atPointEvaluation Q sT q =
      evaluation (F := F) sT k := by
  calc
    _ = ((transition Q sT q b hq k hk).hom ≫ Q.atPointMap sT q) ≫ F.evaluation := by
      simp only [SmoothFamily.atPointEvaluation, SmoothFamily.evaluation,
        StableMaps.FullHomComparison.atPointMap, Category.assoc]
    _ = evaluation (F := F) sT k := by rw [transition_source]

def square : Parametrized.Square P sT ⟶ Parametrized.Square P sT :=
  RelativeSquare.map (Parametrized.parameter P sT) (Parametrized.parameter P sT)
    (transition Q sT q b hq k hk).hom (𝟙 T)
    (by simpa only [Category.comp_id] using transition_parameter Q sT q b hq k hk)

abbrev squareEvaluation : Parametrized.Square P sT ⟶ SelfProduct X.variety.structureMap :=
  ParametrizedContact.evaluationSquare P sT X (evaluation (F := F) sT k)
    (evaluation_overC Q sT q b hq k hk)

@[reassoc] theorem square_evaluation :
    square Q sT q b hq k hk ≫ SmoothFamily.atPointSquareEvaluation Q sT q =
      squareEvaluation Q sT q b hq k hk :=
  RelativeSquare.map_evaluation (Parametrized.parameter P sT) (Parametrized.parameter P sT)
    (transition Q sT q b hq k hk).hom (𝟙 T)
    (by simpa only [Category.comp_id] using transition_parameter Q sT q b hq k hk)
    X.variety.structureMap sT sT (evaluation (F := F) sT k)
    (SmoothFamily.atPointEvaluation Q sT q) (evaluation_overC Q sT q b hq k hk)
    (SmoothFamily.atPointEvaluation_overC Q sT q) (transition_evaluation Q sT q b hq k hk)

variable (a : Parametrized.Square P sT ⟶ F.smoothSquareOpen.toScheme)
variable (ha : a ≫ F.smoothSquareOpen.ι =
  RelativeSquare.map (Parametrized.parameter P sT) F.parameter k
    (b ≫ F.smoothOpen.ι) hk.w)

include ha in
@[reassoc] theorem square_smooth :
    square Q sT q b hq k hk ≫ SmoothFamily.atPointSmooth Q sT q = a := by
  apply (cancel_mono F.smoothSquareOpen.ι).mp
  rw [Category.assoc, SmoothFamily.atPointSmooth_family, ha]
  apply pullback.hom_ext
  · simp only [square, Category.assoc, RelativeSquare.map_left,
      RelativeSquare.map_left_assoc, transition_source]
  · simp only [square, Category.assoc, RelativeSquare.map_right,
      RelativeSquare.map_right_assoc, transition_source]

include ha in
@[reassoc] theorem smooth_evaluation :
    a ≫ SmoothFamily.smoothEvaluation (F := F) = squareEvaluation Q sT q b hq k hk := by
  rw [← square_smooth Q sT q b hq k hk a ha, Category.assoc,
    SmoothFamily.atPointSmooth_evaluation, square_evaluation]

/-- Pure pullback composition: an actual tensor identity for the
transition carries the universal Q-normalization to the supplied
Cartesian parametrization. The field theorem below proves the premise. -/
theorem smoothLeft_of_invariance
    (hi : pullSection (square Q sT q b hq k hk)
        (ParametrizedContact.leftSection P sT X (SmoothFamily.atPointEvaluation Q sT q)
          (SmoothFamily.atPointEvaluation_overC Q sT q)) ≫
      (compositionPullback (square Q sT q b hq k hk)
        (SmoothFamily.atPointSquareEvaluation Q sT q) (squareEvaluation Q sT q b hq k hk)
        (square_evaluation Q sT q b hq k hk) (movingPairBundleLeft X.variety X.contact)).hom =
      ParametrizedContact.leftSection P sT X (evaluation (F := F) sT k)
        (evaluation_overC Q sT q b hq k hk)) :
    pullSection a (SmoothFamily.smoothLeft Q) ≫
      (compositionPullback a (SmoothFamily.smoothEvaluation (F := F))
        (squareEvaluation Q sT q b hq k hk) (smooth_evaluation Q sT q b hq k hk a ha)
        (movingPairBundleLeft X.variety X.contact)).hom =
      ParametrizedContact.leftSection P sT X (evaluation (F := F) sT k)
        (evaluation_overC Q sT q b hq k hk) := by
  rw [SectionTransport.pull_specialization (square Q sT q b hq k hk)
    (SmoothFamily.atPointSmooth Q sT q) (SmoothFamily.smoothEvaluation (F := F)) a
    (SmoothFamily.atPointSquareEvaluation Q sT q) (squareEvaluation Q sT q b hq k hk)
    (square_smooth Q sT q b hq k hk a ha) (SmoothFamily.atPointSmooth_evaluation Q sT q)
    (square_evaluation Q sT q b hq k hk) (smooth_evaluation Q sT q b hq k hk a ha)
    (SmoothFamily.smoothLeft Q)
    (ParametrizedContact.leftSection P sT X (SmoothFamily.atPointEvaluation Q sT q)
      (SmoothFamily.atPointEvaluation_overC Q sT q)) (SmoothFamily.smoothLeft_atPoint Q sT q)]
  exact hi

theorem smoothRight_of_invariance
    (hi : pullSection (square Q sT q b hq k hk)
        (ParametrizedContact.rightSection P sT X (SmoothFamily.atPointEvaluation Q sT q)
          (SmoothFamily.atPointEvaluation_overC Q sT q)) ≫
      (compositionPullback (square Q sT q b hq k hk)
        (SmoothFamily.atPointSquareEvaluation Q sT q) (squareEvaluation Q sT q b hq k hk)
        (square_evaluation Q sT q b hq k hk) (movingPairBundleRight X.variety X.contact)).hom =
      ParametrizedContact.rightSection P sT X (evaluation (F := F) sT k)
        (evaluation_overC Q sT q b hq k hk)) :
    pullSection a (SmoothFamily.smoothRight Q) ≫
      (compositionPullback a (SmoothFamily.smoothEvaluation (F := F))
        (squareEvaluation Q sT q b hq k hk) (smooth_evaluation Q sT q b hq k hk a ha)
        (movingPairBundleRight X.variety X.contact)).hom =
      ParametrizedContact.rightSection P sT X (evaluation (F := F) sT k)
        (evaluation_overC Q sT q b hq k hk) := by
  rw [SectionTransport.pull_specialization (square Q sT q b hq k hk)
    (SmoothFamily.atPointSmooth Q sT q) (SmoothFamily.smoothEvaluation (F := F)) a
    (SmoothFamily.atPointSquareEvaluation Q sT q) (squareEvaluation Q sT q b hq k hk)
    (square_smooth Q sT q b hq k hk a ha) (SmoothFamily.atPointSmooth_evaluation Q sT q)
    (square_evaluation Q sT q b hq k hk) (smooth_evaluation Q sT q b hq k hk a ha)
    (SmoothFamily.smoothRight Q)
    (ParametrizedContact.rightSection P sT X (SmoothFamily.atPointEvaluation Q sT q)
      (SmoothFamily.atPointEvaluation_overC Q sT q)) (SmoothFamily.smoothRight_atPoint Q sT q)]
  exact hi

end CartesianParametrization

end LeBrunSalamon.Construction.FamilyBivectors

end
