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
  apply squareMap_section_injective Q K sK b (MovingPair.leftBundle rK)
  apply (cancel_mono (compositionPullback (squareMap Q K sK b) rK rL hbase
    (movingPairBundleLeft X.variety X.contact)).hom).mp
  have hn := SectionTransport.pull_specialization (squareMap Q K sK b) a
    (SmoothFamily.smoothEvaluation (F := F)) aL rK rL rfl haK hbase hAL
    (SmoothFamily.smoothLeft Q)
    (pullSection a (SmoothFamily.smoothLeft Q) ≫
      (compositionPullback a (SmoothFamily.smoothEvaluation (F := F)) rK haK
        (movingPairBundleLeft X.variety X.contact)).hom) rfl
  rw [← hn, left_baseChange Q K sK b hb k hk]
  exact hL

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
  apply squareMap_section_injective Q K sK b (MovingPair.rightBundle rK)
  apply (cancel_mono (compositionPullback (squareMap Q K sK b) rK rL hbase
    (movingPairBundleRight X.variety X.contact)).hom).mp
  have hn := SectionTransport.pull_specialization (squareMap Q K sK b) a
    (SmoothFamily.smoothEvaluation (F := F)) aL rK rL rfl haK hbase hAL
    (SmoothFamily.smoothRight Q)
    (pullSection a (SmoothFamily.smoothRight Q) ≫
      (compositionPullback a (SmoothFamily.smoothEvaluation (F := F)) rK haK
        (movingPairBundleRight X.variety X.contact)).hom) rfl
  rw [← hn, right_baseChange Q K sK b hb k hk]
  exact hL

end FieldComparison

end LeBrunSalamon.Construction.FamilyBivectors

end
