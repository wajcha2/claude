import LSGenericFamilyCartesianComparison
import LSFamilyBaseChange
import LSParametrizedBaseChange
import LSFamilySmoothNormalization
import LSFieldParametrization
import LSFamilyReparametrization
import LSGenericFamilyPointComparison
import LSGenericFamilyFieldTransport



noncomputable section
set_option autoImplicit false
set_option profiler true
set_option stderrAsMessages false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction.FamilyBivectors

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE ENTER_01_field_equation_transport"
  err.flush

private theorem field_equation_transport {T Y Z : Scheme}
    (q q' : T ⟶ Y) (hq : q = q')
    (f f' : Y ⟶ Z) (hf : f = f') (r r' : T ⟶ Z) (hr : r = r')
    (h : q ≫ f = r) (h' : q' ≫ f' = r') (E : OModule Z)
    (s : AlgebraicSection (pullbackModule f E))
    (s' : AlgebraicSection (pullbackModule f' E)) (hs : HEq s s')
    (t : AlgebraicSection (pullbackModule r E))
    (t' : AlgebraicSection (pullbackModule r' E)) (ht : HEq t t') :
    (pullSection q s ≫ (compositionPullback q f r h E).hom = t) ↔
      (pullSection q' s' ≫ (compositionPullback q' f' r' h' E).hom = t') := by
  cases hq
  cases hf
  cases hr
  have hs' : s = s' := eq_of_heq hs
  cases hs'
  have ht' : t = t' := eq_of_heq ht
  cases ht'
  rfl

namespace CartesianParametrization

variable {P : ProjectiveLineOverC} {p : ProjectiveLinePoint P}
variable {n : ℕ} {X : ContactFanoManifold n} {g : VeryFreeContactConic P p X}
variable {N : FullConicNeighborhood P p X g}
variable {F : StableMaps.ProjectiveNodalFamily P p X.variety X.contact.sequence.line 2}
variable (Q : StableMaps.FullHomComparison P p X.variety N.homSpace N.neighborhood
  X.contact.sequence.line 2 F)
-- A field structure is chosen only from the actual bundled ring predicate.
variable (K : CommRingCat) [hK : Fact (IsField K)] (sK : Spec K ⟶ ComplexBase)

local instance : Field K := hK.out.toField
variable (q : PointsOver (Spec K) sK Q.cover Q.coverToC)
variable (b : Spec K ⟶ F.smoothOpen.toScheme) (hq : q.val ≫ Q.toSmooth = b)
variable (k : Parametrized.Source P sK ⟶ F.source)
variable (hk : IsPullback k (Parametrized.parameter P sK) F.parameter (b ≫ F.smoothOpen.ι))
variable (a : Parametrized.Square P sK ⟶ F.smoothSquareOpen.toScheme)
variable (ha : a ≫ F.smoothSquareOpen.ι = RelativeSquare.map (Parametrized.parameter P sK)
  F.parameter k (b ≫ F.smoothOpen.ι) hk.w)



#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE EXIT_01_field_equation_transport"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE ENTER_02_field_square_eq"
  err.flush

private theorem field_square_eq :
    FamilyReparametrization.squareMap P sK (transition Q sK q b hq k hk)
      (transition_parameter Q sK q b hq k hk) = square Q sK q b hq k hk := by
  rfl


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE EXIT_02_field_square_eq"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE ENTER_03_field_input_map_eq"
  err.flush

private theorem field_input_map_eq :
    ParametrizedContact.evaluationSquare P sK X (SmoothFamily.atPointEvaluation Q sK q)
      (SmoothFamily.atPointEvaluation_overC Q sK q) =
      SmoothFamily.atPointSquareEvaluation Q sK q := by
  rfl


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE EXIT_03_field_input_map_eq"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE ENTER_04_field_output_map_eq"
  err.flush

private theorem field_output_map_eq :
    ParametrizedContact.evaluationSquare P sK X (evaluation (F := F) sK k)
      (evaluation_overC Q sK q b hq k hk) = squareEvaluation Q sK q b hq k hk := by
  rfl


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE EXIT_04_field_output_map_eq"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE ENTER_05_field_left_input_heq"
  err.flush

private theorem field_left_input_heq :
    @HEq (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (ParametrizedContact.evaluationSquare P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (movingPairBundleLeft X.variety X.contact)))
      (ParametrizedContact.leftSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q))
      (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (SmoothFamily.atPointSquareEvaluation Q sK q) (movingPairBundleLeft X.variety X.contact)))
      (ParametrizedContact.leftSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) := by rfl


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE EXIT_05_field_left_input_heq"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE ENTER_06_field_left_output_heq"
  err.flush

private theorem field_left_output_heq :
    @HEq (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (ParametrizedContact.evaluationSquare P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (movingPairBundleLeft X.variety X.contact)))
      (ParametrizedContact.leftSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk))
      (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (squareEvaluation Q sK q b hq k hk) (movingPairBundleLeft X.variety X.contact)))
      (ParametrizedContact.leftSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) := by rfl


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE EXIT_06_field_left_output_heq"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE ENTER_07_field_left_invariance_transport"
  err.flush

private theorem field_left_invariance_transport
    (hi : pullSection (FamilyReparametrization.squareMap P sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)) (ParametrizedContact.leftSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) ≫
      (compositionPullback (FamilyReparametrization.squareMap P sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)) (ParametrizedContact.evaluationSquare P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (ParametrizedContact.evaluationSquare P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (FamilyReparametrization.squareMap_evaluation P sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk) X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q) (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk) (transition_evaluation Q sK q b hq k hk)) (movingPairBundleLeft X.variety X.contact)).hom = (ParametrizedContact.leftSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk))) :
    pullSection (square Q sK q b hq k hk) (ParametrizedContact.leftSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) ≫
      (compositionPullback (square Q sK q b hq k hk) (SmoothFamily.atPointSquareEvaluation Q sK q) (squareEvaluation Q sK q b hq k hk) (square_evaluation Q sK q b hq k hk) (movingPairBundleLeft X.variety X.contact)).hom = (ParametrizedContact.leftSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) := by
  exact (field_equation_transport (FamilyReparametrization.squareMap P sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)) (square Q sK q b hq k hk) (field_square_eq Q K sK q b hq k hk)
    (ParametrizedContact.evaluationSquare P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (SmoothFamily.atPointSquareEvaluation Q sK q) (field_input_map_eq Q K sK q)
    (ParametrizedContact.evaluationSquare P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (squareEvaluation Q sK q b hq k hk) (field_output_map_eq Q K sK q b hq k hk)
    (FamilyReparametrization.squareMap_evaluation P sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk) X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q) (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk) (transition_evaluation Q sK q b hq k hk)) (square_evaluation Q sK q b hq k hk) (movingPairBundleLeft X.variety X.contact)
    (ParametrizedContact.leftSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (ParametrizedContact.leftSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (field_left_input_heq Q K sK q)
    (ParametrizedContact.leftSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (ParametrizedContact.leftSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (field_left_output_heq Q K sK q b hq k hk)).mp hi


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE EXIT_07_field_left_invariance_transport"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE ENTER_08_field_right_input_heq"
  err.flush

private theorem field_right_input_heq :
    @HEq (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (ParametrizedContact.evaluationSquare P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (movingPairBundleRight X.variety X.contact)))
      (ParametrizedContact.rightSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q))
      (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (SmoothFamily.atPointSquareEvaluation Q sK q) (movingPairBundleRight X.variety X.contact)))
      (ParametrizedContact.rightSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) := by rfl


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE EXIT_08_field_right_input_heq"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE ENTER_09_field_right_output_heq"
  err.flush

private theorem field_right_output_heq :
    @HEq (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (ParametrizedContact.evaluationSquare P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (movingPairBundleRight X.variety X.contact)))
      (ParametrizedContact.rightSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk))
      (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (squareEvaluation Q sK q b hq k hk) (movingPairBundleRight X.variety X.contact)))
      (ParametrizedContact.rightSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) := by rfl


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE EXIT_09_field_right_output_heq"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE ENTER_10_field_right_invariance_transport"
  err.flush

private theorem field_right_invariance_transport
    (hi : pullSection (FamilyReparametrization.squareMap P sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)) (ParametrizedContact.rightSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) ≫
      (compositionPullback (FamilyReparametrization.squareMap P sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)) (ParametrizedContact.evaluationSquare P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (ParametrizedContact.evaluationSquare P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (FamilyReparametrization.squareMap_evaluation P sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk) X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q) (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk) (transition_evaluation Q sK q b hq k hk)) (movingPairBundleRight X.variety X.contact)).hom = (ParametrizedContact.rightSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk))) :
    pullSection (square Q sK q b hq k hk) (ParametrizedContact.rightSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) ≫
      (compositionPullback (square Q sK q b hq k hk) (SmoothFamily.atPointSquareEvaluation Q sK q) (squareEvaluation Q sK q b hq k hk) (square_evaluation Q sK q b hq k hk) (movingPairBundleRight X.variety X.contact)).hom = (ParametrizedContact.rightSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) := by
  exact (field_equation_transport (FamilyReparametrization.squareMap P sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)) (square Q sK q b hq k hk) (field_square_eq Q K sK q b hq k hk)
    (ParametrizedContact.evaluationSquare P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (SmoothFamily.atPointSquareEvaluation Q sK q) (field_input_map_eq Q K sK q)
    (ParametrizedContact.evaluationSquare P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (squareEvaluation Q sK q b hq k hk) (field_output_map_eq Q K sK q b hq k hk)
    (FamilyReparametrization.squareMap_evaluation P sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk) X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q) (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk) (transition_evaluation Q sK q b hq k hk)) (square_evaluation Q sK q b hq k hk) (movingPairBundleRight X.variety X.contact)
    (ParametrizedContact.rightSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (ParametrizedContact.rightSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (field_right_input_heq Q K sK q)
    (ParametrizedContact.rightSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (ParametrizedContact.rightSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (field_right_output_heq Q K sK q b hq k hk)).mp hi



#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE EXIT_10_field_right_invariance_transport"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE ENTER_11_smoothLeft_field"
  err.flush

theorem smoothLeft_field :
    pullSection a (SmoothFamily.smoothLeft Q) ≫
      (compositionPullback a (SmoothFamily.smoothEvaluation (F := F))
        (squareEvaluation Q sK q b hq k hk) (smooth_evaluation Q sK q b hq k hk a ha)
        (movingPairBundleLeft X.variety X.contact)).hom =
      ParametrizedContact.leftSection P sK X (evaluation (F := F) sK k)
        (evaluation_overC Q sK q b hq k hk) := by
  letI : LocallyOfFiniteType Q.coverToC := SmoothFamily.cover_locallyOfFiniteType Q
  apply smoothLeft_of_invariance Q sK q b hq k hk a ha
  apply field_left_invariance_transport Q K sK q b hq k hk
  exact FamilyReparametrization.leftSection_field P Q.coverToC X
    (SmoothFamily.evaluation Q) (SmoothFamily.evaluation_overC Q)
    (SmoothFamily.nonconstantFamily Q) K sK q
    (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q) rfl
    (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)
    (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)
    (transition_evaluation Q sK q b hq k hk)


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE EXIT_11_smoothLeft_field"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE ENTER_12_smoothRight_field"
  err.flush

theorem smoothRight_field :
    pullSection a (SmoothFamily.smoothRight Q) ≫
      (compositionPullback a (SmoothFamily.smoothEvaluation (F := F))
        (squareEvaluation Q sK q b hq k hk) (smooth_evaluation Q sK q b hq k hk a ha)
        (movingPairBundleRight X.variety X.contact)).hom =
      ParametrizedContact.rightSection P sK X (evaluation (F := F) sK k)
        (evaluation_overC Q sK q b hq k hk) := by
  letI : LocallyOfFiniteType Q.coverToC := SmoothFamily.cover_locallyOfFiniteType Q
  apply smoothRight_of_invariance Q sK q b hq k hk a ha
  apply field_right_invariance_transport Q K sK q b hq k hk
  exact FamilyReparametrization.rightSection_field P Q.coverToC X
    (SmoothFamily.evaluation Q) (SmoothFamily.evaluation_overC Q)
    (SmoothFamily.nonconstantFamily Q) K sK q
    (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q) rfl
    (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)
    (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)
    (transition_evaluation Q sK q b hq k hk)

end CartesianParametrization

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



#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE EXIT_12_smoothRight_field"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE ENTER_13_smoothLeft"
  err.flush

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



#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE EXIT_13_smoothLeft"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE ENTER_14_smoothRight"
  err.flush

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

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_FIELD_STAGE EXIT_14_smoothRight"
  err.flush

