import LSGenericFamilyCartesianFieldComparison
import LSGenericFamilyCartesianComparison
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

private theorem field_section_injective_transport {T Y : Scheme}
    (f : T ⟶ Y) (B C : OModule Y) (hBC : B = C)
    (hi : Function.Injective (fun s : AlgebraicSection B => pullSection f s)) :
    Function.Injective (fun s : AlgebraicSection C => pullSection f s) := by
  cases hBC
  exact hi

private theorem field_specialization_descends {T Y Z W : Scheme}
    (f : T ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (fg : T ⟶ Z) (gh : Y ⟶ W) (fgh : T ⟶ W)
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hfgh : f ≫ gh = fgh) (hfgh' : fg ≫ h = fgh)
    (E : OModule W) (B : OModule Y) (hB : B = pullbackModule gh E)
    (hi : Function.Injective (fun s : AlgebraicSection B => pullSection f s))
    (a : AlgebraicSection (pullbackModule h E))
    (b : AlgebraicSection (pullbackModule gh E))
    (c : AlgebraicSection (pullbackModule fgh E))
    (hbc : pullSection f b ≫ (compositionPullback f gh fgh hfgh E).hom = c)
    (hac : pullSection fg a ≫ (compositionPullback fg h fgh hfgh' E).hom = c) :
    pullSection g a ≫ (compositionPullback g h gh hgh E).hom = b := by
  apply field_section_injective_transport f B (pullbackModule gh E) hB hi
  apply (cancel_mono (compositionPullback f gh fgh hfgh E).hom).mp
  have hn := SectionTransport.pull_specialization f g h fg gh fgh
    hfg hgh hfgh hfgh' a
    (pullSection g a ≫ (compositionPullback g h gh hgh E).hom) rfl
  exact hn.symm.trans (hac.trans hbc.symm)

private theorem field_left_module_eq {n : ℕ} {X : ContactFanoManifold n}
    {Y : Scheme} (f : Y ⟶ SelfProduct X.variety.structureMap) :
    (MovingPair.leftBundle f).sheaf = pullbackModule f (movingPairBundleLeft X.variety X.contact) := by
  rfl

private theorem field_left_pull_input {n : ℕ} {X : ContactFanoManifold n}
    {T Y : Scheme} (q : T ⟶ Y)
    (f : Y ⟶ SelfProduct X.variety.structureMap)
    (r : T ⟶ SelfProduct X.variety.structureMap) (h : q ≫ f = r)
    (s : AlgebraicSection (MovingPair.leftBundle f).sheaf) :
    (@pullSection T Y q (MovingPair.leftBundle f).sheaf s ≫
      (compositionPullback q f r h (movingPairBundleLeft X.variety X.contact)).hom) =
    (@pullSection T Y q (pullbackModule f (movingPairBundleLeft X.variety X.contact)) s ≫
      (compositionPullback q f r h (movingPairBundleLeft X.variety X.contact)).hom) := by
  rfl

private theorem field_right_module_eq {n : ℕ} {X : ContactFanoManifold n}
    {Y : Scheme} (f : Y ⟶ SelfProduct X.variety.structureMap) :
    (MovingPair.rightBundle f).sheaf = pullbackModule f (movingPairBundleRight X.variety X.contact) := by
  rfl

private theorem field_right_pull_input {n : ℕ} {X : ContactFanoManifold n}
    {T Y : Scheme} (q : T ⟶ Y)
    (f : Y ⟶ SelfProduct X.variety.structureMap)
    (r : T ⟶ SelfProduct X.variety.structureMap) (h : q ≫ f = r)
    (s : AlgebraicSection (MovingPair.rightBundle f).sheaf) :
    (@pullSection T Y q (MovingPair.rightBundle f).sheaf s ≫
      (compositionPullback q f r h (movingPairBundleRight X.variety X.contact)).hom) =
    (@pullSection T Y q (pullbackModule f (movingPairBundleRight X.variety X.contact)) s ≫
      (compositionPullback q f r h (movingPairBundleRight X.variety X.contact)).hom) := by
  rfl

namespace FieldComparison

variable {P : ProjectiveLineOverC} {p : ProjectiveLinePoint P}
variable {n : ℕ} {X : ContactFanoManifold n} {g : VeryFreeContactConic P p X}
variable {N : FullConicNeighborhood P p X g}
variable {F : StableMaps.ProjectiveNodalFamily P p X.variety X.contact.sequence.line 2}
variable (Q : StableMaps.FullHomComparison P p X.variety N.homSpace N.neighborhood
  X.contact.sequence.line 2 F)

-- A field structure is chosen only from the actual bundled ring predicate.
variable (K : CommRingCat) [hK : Fact (IsField K)] (sK : Spec K ⟶ ComplexBase)

local instance : Field K := hK.out.toField
variable (b : Spec K ⟶ F.smoothOpen.toScheme)
variable (hb : (b ≫ F.smoothOpen.ι) ≫ F.toC = sK)
variable (k : Parametrized.Source P sK ⟶ F.source)
variable (hk : IsPullback k (Parametrized.parameter P sK) F.parameter (b ≫ F.smoothOpen.ι))

local instance : Surjective Q.toSmooth := Q.smoothSurjective

variable (a : Parametrized.Square P sK ⟶ F.smoothSquareOpen.toScheme)
variable (ha : a ≫ F.smoothSquareOpen.ι = RelativeSquare.map (Parametrized.parameter P sK)
  F.parameter k (b ≫ F.smoothOpen.ι) hk.w)

/-- The descended left section agrees with the intrinsic tensor of
every Cartesian P1 parametrization over an arbitrary field over C.
The proof lifts to the actual residue field of Q, compares the literal
fibre isomorphisms, and descends through the resulting fpqc square map. -/
theorem smoothLeft :
    pullSection a (SmoothFamily.smoothLeft Q) ≫
      (compositionPullback a (SmoothFamily.smoothEvaluation (F := F))
        (ParametrizedContact.evaluationSquare P sK X (k ≫ F.evaluation)
          (evaluation_overC sK b hb k hk))
        (square_evaluation sK b hb k hk a ha)
        (movingPairBundleLeft X.variety X.contact)).hom =
      ParametrizedContact.leftSection P sK X (k ≫ F.evaluation)
        (evaluation_overC sK b hb k hk) := by
  let sL := extensionToC Q K sK b
  let bL := extendedBase Q K b
  let kL := extendedSource Q K sK b k
  let hkL := extendedSource_isPullback Q K sK b k hk
  let aL := extendedSquare Q K sK b a
  have hbL : (bL ≫ F.smoothOpen.ι) ≫ F.toC = sL := extendedBase_overC Q K sK b hb
  have haL : aL ≫ F.smoothSquareOpen.ι = RelativeSquare.map
      (Parametrized.parameter P sL) F.parameter kL (bL ≫ F.smoothOpen.ι) hkL.w :=
    extendedSquare_family Q K sK b k hk a ha
  let rK := ParametrizedContact.evaluationSquare P sK X (k ≫ F.evaluation)
    (evaluation_overC sK b hb k hk)
  let rL := ParametrizedContact.evaluationSquare P sL X (kL ≫ F.evaluation)
    (evaluation_overC sL bL hbL kL hkL)
  have haK : a ≫ SmoothFamily.smoothEvaluation (F := F) = rK :=
    square_evaluation sK b hb k hk a ha
  have hbase : squareMap Q K sK b ≫ rK = rL :=
    evaluationSquare_baseChange Q K sK b hb k hk
  have hAL : aL ≫ SmoothFamily.smoothEvaluation (F := F) = rL :=
    square_evaluation sL bL hbL kL hkL aL haL
  have hL : pullSection aL (SmoothFamily.smoothLeft Q) ≫
      (compositionPullback aL (SmoothFamily.smoothEvaluation (F := F)) rL hAL
        (movingPairBundleLeft X.variety X.contact)).hom =
      ParametrizedContact.leftSection P sL X (kL ≫ F.evaluation)
        (evaluation_overC sL bL hbL kL hkL) := by
    exact CartesianParametrization.smoothLeft_field Q (Q.parametrizingField K b) sL
      (coverPoint Q K sK b hb) bL (coverPoint_base Q K sK b hb) kL hkL aL haL
  exact (field_left_pull_input a (SmoothFamily.smoothEvaluation (F := F))
    rK haK (SmoothFamily.smoothLeft Q)).trans
    (field_specialization_descends (squareMap Q K sK b) a
      (SmoothFamily.smoothEvaluation (F := F)) aL rK rL rfl haK hbase hAL
      (movingPairBundleLeft X.variety X.contact) (MovingPair.leftBundle rK).sheaf
      (field_left_module_eq rK)
      (squareMap_section_injective Q K sK b (MovingPair.leftBundle rK))
      (SmoothFamily.smoothLeft Q)
      (ParametrizedContact.leftSection P sK X (k ≫ F.evaluation)
        (evaluation_overC sK b hb k hk))
      (ParametrizedContact.leftSection P sL X (kL ≫ F.evaluation)
        (evaluation_overC sL bL hbL kL hkL))
      (left_baseChange Q K sK b hb k hk)
      ((field_left_pull_input aL (SmoothFamily.smoothEvaluation (F := F))
        rL hAL (SmoothFamily.smoothLeft Q)).symm.trans hL))

/-- The corresponding arbitrary-field comparison for the second
mixed tensor, with the same complete source square and field extension. -/
theorem smoothRight :
    pullSection a (SmoothFamily.smoothRight Q) ≫
      (compositionPullback a (SmoothFamily.smoothEvaluation (F := F))
        (ParametrizedContact.evaluationSquare P sK X (k ≫ F.evaluation)
          (evaluation_overC sK b hb k hk))
        (square_evaluation sK b hb k hk a ha)
        (movingPairBundleRight X.variety X.contact)).hom =
      ParametrizedContact.rightSection P sK X (k ≫ F.evaluation)
        (evaluation_overC sK b hb k hk) := by
  let sL := extensionToC Q K sK b
  let bL := extendedBase Q K b
  let kL := extendedSource Q K sK b k
  let hkL := extendedSource_isPullback Q K sK b k hk
  let aL := extendedSquare Q K sK b a
  have hbL : (bL ≫ F.smoothOpen.ι) ≫ F.toC = sL := extendedBase_overC Q K sK b hb
  have haL : aL ≫ F.smoothSquareOpen.ι = RelativeSquare.map
      (Parametrized.parameter P sL) F.parameter kL (bL ≫ F.smoothOpen.ι) hkL.w :=
    extendedSquare_family Q K sK b k hk a ha
  let rK := ParametrizedContact.evaluationSquare P sK X (k ≫ F.evaluation)
    (evaluation_overC sK b hb k hk)
  let rL := ParametrizedContact.evaluationSquare P sL X (kL ≫ F.evaluation)
    (evaluation_overC sL bL hbL kL hkL)
  have haK : a ≫ SmoothFamily.smoothEvaluation (F := F) = rK :=
    square_evaluation sK b hb k hk a ha
  have hbase : squareMap Q K sK b ≫ rK = rL :=
    evaluationSquare_baseChange Q K sK b hb k hk
  have hAL : aL ≫ SmoothFamily.smoothEvaluation (F := F) = rL :=
    square_evaluation sL bL hbL kL hkL aL haL
  have hL : pullSection aL (SmoothFamily.smoothRight Q) ≫
      (compositionPullback aL (SmoothFamily.smoothEvaluation (F := F)) rL hAL
        (movingPairBundleRight X.variety X.contact)).hom =
      ParametrizedContact.rightSection P sL X (kL ≫ F.evaluation)
        (evaluation_overC sL bL hbL kL hkL) := by
    exact CartesianParametrization.smoothRight_field Q (Q.parametrizingField K b) sL
      (coverPoint Q K sK b hb) bL (coverPoint_base Q K sK b hb) kL hkL aL haL
  exact (field_right_pull_input a (SmoothFamily.smoothEvaluation (F := F))
    rK haK (SmoothFamily.smoothRight Q)).trans
    (field_specialization_descends (squareMap Q K sK b) a
      (SmoothFamily.smoothEvaluation (F := F)) aL rK rL rfl haK hbase hAL
      (movingPairBundleRight X.variety X.contact) (MovingPair.rightBundle rK).sheaf
      (field_right_module_eq rK)
      (squareMap_section_injective Q K sK b (MovingPair.rightBundle rK))
      (SmoothFamily.smoothRight Q)
      (ParametrizedContact.rightSection P sK X (k ≫ F.evaluation)
        (evaluation_overC sK b hb k hk))
      (ParametrizedContact.rightSection P sL X (kL ≫ F.evaluation)
        (evaluation_overC sL bL hbL kL hkL))
      (right_baseChange Q K sK b hb k hk)
      ((field_right_pull_input aL (SmoothFamily.smoothEvaluation (F := F))
        rL hAL (SmoothFamily.smoothRight Q)).symm.trans hL))

end FieldComparison

end LeBrunSalamon.Construction.FamilyBivectors

end
