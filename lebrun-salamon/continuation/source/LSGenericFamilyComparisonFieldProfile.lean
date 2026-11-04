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
set_option stderrAsMessages false
set_option profiler true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction.FamilyBivectors

namespace RepackedFieldAccessors

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_01_ring_eq"
  err.flush

private theorem ring_eq (K : CommRingCat) [hK : Fact (IsField K)] :
    @CommRingCat.of K.carrier (@Field.toCommRing K.carrier (hK.out.toField)) = K := by
  cases K
  rfl


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_01_ring_eq"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_02_spec_eq"
  err.flush

private theorem spec_eq (K : CommRingCat) [hK : Fact (IsField K)] :
    Spec (@CommRingCat.of K.carrier (@Field.toCommRing K.carrier (hK.out.toField))) =
      Spec K := by
  exact congrArg (fun R : CommRingCat => Spec R) (ring_eq K)


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_02_spec_eq"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_03_base_heq"
  err.flush

private theorem base_heq (K : CommRingCat) [hK : Fact (IsField K)]
    (sK : Spec K ⟶ ComplexBase) :
    @HEq
      (Spec (@CommRingCat.of K.carrier
        (@Field.toCommRing K.carrier (hK.out.toField))) ⟶ ComplexBase) sK
      (Spec K ⟶ ComplexBase) sK := by
  rfl


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_03_base_heq"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_04_map_heq"
  err.flush

private theorem map_heq (P : ProjectiveLineOverC) (K : CommRingCat)
    [hK : Fact (IsField K)] (sK : Spec K ⟶ ComplexBase)
    {Y : Scheme} (f : Parametrized.Source P sK ⟶ Y) :
    @HEq
      ((@Parametrized.Source P
        (Spec (@CommRingCat.of K.carrier
          (@Field.toCommRing K.carrier (hK.out.toField)))) sK) ⟶ Y) f
      ((@Parametrized.Source P (Spec K) sK) ⟶ Y) f := by
  rfl


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_04_map_heq"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_05_iso_heq"
  err.flush

private theorem iso_heq (P : ProjectiveLineOverC) (K : CommRingCat)
    [hK : Fact (IsField K)] (sK : Spec K ⟶ ComplexBase)
    (e : Parametrized.Source P sK ≅ Parametrized.Source P sK) :
    @HEq
      ((@Parametrized.Source P
        (Spec (@CommRingCat.of K.carrier
          (@Field.toCommRing K.carrier (hK.out.toField)))) sK) ≅
       (@Parametrized.Source P
        (Spec (@CommRingCat.of K.carrier
          (@Field.toCommRing K.carrier (hK.out.toField)))) sK)) e
      ((@Parametrized.Source P (Spec K) sK) ≅
       (@Parametrized.Source P (Spec K) sK)) e := by
  rfl

end RepackedFieldAccessors

namespace FieldReparamTransport

private structure Data (P : ProjectiveLineOverC) {n : ℕ} (X : ContactFanoManifold n)
    (T : Scheme) where
  s : T ⟶ ComplexBase
  f : Parametrized.Source P s ⟶ X.variety.scheme
  hf : f ≫ X.variety.structureMap = Parametrized.parameter P s ≫ s
  e : Parametrized.Source P s ≅ Parametrized.Source P s
  he : e.hom ≫ Parametrized.parameter P s = Parametrized.parameter P s
  g : Parametrized.Source P s ⟶ X.variety.scheme
  hg : g ≫ X.variety.structureMap = Parametrized.parameter P s ≫ s
  hcomp : e.hom ≫ f = g


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_05_iso_heq"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_06_data_heq"
  err.flush

private theorem data_heq (P : ProjectiveLineOverC) {n : ℕ} (X : ContactFanoManifold n)
    {T U : Scheme} (hTU : T = U)
    (sT : T ⟶ ComplexBase) (sU : U ⟶ ComplexBase) (hs : HEq sT sU)
    (fT : Parametrized.Source P sT ⟶ X.variety.scheme)
    (fU : Parametrized.Source P sU ⟶ X.variety.scheme) (hF : HEq fT fU)
    (hfT : fT ≫ X.variety.structureMap = Parametrized.parameter P sT ≫ sT)
    (hfU : fU ≫ X.variety.structureMap = Parametrized.parameter P sU ≫ sU)
    (eT : Parametrized.Source P sT ≅ Parametrized.Source P sT)
    (eU : Parametrized.Source P sU ≅ Parametrized.Source P sU) (hE : HEq eT eU)
    (heT : eT.hom ≫ Parametrized.parameter P sT = Parametrized.parameter P sT)
    (heU : eU.hom ≫ Parametrized.parameter P sU = Parametrized.parameter P sU)
    (gT : Parametrized.Source P sT ⟶ X.variety.scheme)
    (gU : Parametrized.Source P sU ⟶ X.variety.scheme) (hG : HEq gT gU)
    (hgT : gT ≫ X.variety.structureMap = Parametrized.parameter P sT ≫ sT)
    (hgU : gU ≫ X.variety.structureMap = Parametrized.parameter P sU ≫ sU)
    (hcompT : eT.hom ≫ fT = gT) (hcompU : eU.hom ≫ fU = gU) :
    @HEq (Data P X T) ⟨sT, fT, hfT, eT, heT, gT, hgT, hcompT⟩
      (Data P X U) ⟨sU, fU, hfU, eU, heU, gU, hgU, hcompU⟩ := by
  cases hTU
  have hs' : sT = sU := eq_of_heq hs
  cases hs'
  have hF' : fT = fU := eq_of_heq hF
  cases hF'
  have hE' : eT = eU := eq_of_heq hE
  cases hE'
  have hG' : gT = gU := eq_of_heq hG
  cases hG'
  rfl

universe u v


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_06_data_heq"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_07_predicate_transport"
  err.flush

private theorem predicate_transport {α : Sort u} (F : α → Sort v)
    (G : (a : α) → F a → Prop)
    {a b : α} (hab : a = b) {x : F a} {y : F b} (hxy : HEq x y) :
    G a x ↔ G b y := by
  cases hab
  have hxy' : x = y := eq_of_heq hxy
  cases hxy'
  rfl

end FieldReparamTransport


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_07_predicate_transport"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_08_field_equation_transport"
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
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_08_field_equation_transport"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_09_field_square_eq"
  err.flush

private theorem field_square_eq :
    FamilyReparametrization.squareMap P sK (transition Q sK q b hq k hk)
      (transition_parameter Q sK q b hq k hk) = square Q sK q b hq k hk := by
  rfl


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_09_field_square_eq"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_10_field_input_map_eq"
  err.flush

private theorem field_input_map_eq :
    ParametrizedContact.evaluationSquare P sK X (SmoothFamily.atPointEvaluation Q sK q)
      (SmoothFamily.atPointEvaluation_overC Q sK q) =
      SmoothFamily.atPointSquareEvaluation Q sK q := by
  rfl


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_10_field_input_map_eq"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_11_field_output_map_eq"
  err.flush

private theorem field_output_map_eq :
    ParametrizedContact.evaluationSquare P sK X (evaluation (F := F) sK k)
      (evaluation_overC Q sK q b hq k hk) = squareEvaluation Q sK q b hq k hk := by
  rfl


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_11_field_output_map_eq"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_12_field_left_input_heq"
  err.flush

private theorem field_left_input_heq :
    @HEq (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (ParametrizedContact.evaluationSquare P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (movingPairBundleLeft X.variety X.contact)))
      (ParametrizedContact.leftSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q))
      (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (SmoothFamily.atPointSquareEvaluation Q sK q) (movingPairBundleLeft X.variety X.contact)))
      (ParametrizedContact.leftSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) := by rfl


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_12_field_left_input_heq"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_13_field_left_output_heq"
  err.flush

private theorem field_left_output_heq :
    @HEq (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (ParametrizedContact.evaluationSquare P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (movingPairBundleLeft X.variety X.contact)))
      (ParametrizedContact.leftSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk))
      (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (squareEvaluation Q sK q b hq k hk) (movingPairBundleLeft X.variety X.contact)))
      (ParametrizedContact.leftSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) := by rfl


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_13_field_left_output_heq"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_14_field_left_invariance_transport"
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
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_14_field_left_invariance_transport"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_15_field_right_input_heq"
  err.flush

private theorem field_right_input_heq :
    @HEq (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (ParametrizedContact.evaluationSquare P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (movingPairBundleRight X.variety X.contact)))
      (ParametrizedContact.rightSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q))
      (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (SmoothFamily.atPointSquareEvaluation Q sK q) (movingPairBundleRight X.variety X.contact)))
      (ParametrizedContact.rightSection P sK X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) := by rfl


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_15_field_right_input_heq"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_16_field_right_output_heq"
  err.flush

private theorem field_right_output_heq :
    @HEq (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (ParametrizedContact.evaluationSquare P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (movingPairBundleRight X.variety X.contact)))
      (ParametrizedContact.rightSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk))
      (AlgebraicSection (@pullbackModule (Parametrized.Square P sK) (SelfProduct X.variety.structureMap) (squareEvaluation Q sK q b hq k hk) (movingPairBundleRight X.variety X.contact)))
      (ParametrizedContact.rightSection P sK X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) := by rfl


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_16_field_right_output_heq"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_17_field_right_invariance_transport"
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
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_17_field_right_invariance_transport"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_18_field_left_base_transport"
  err.flush

private theorem field_left_base_transport
    (hi : pullSection (@FamilyReparametrization.squareMap P (Spec (@CommRingCat.of K.carrier (@Field.toCommRing K.carrier (inferInstance : Field K)))) sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)) (@ParametrizedContact.leftSection P (Spec (@CommRingCat.of K.carrier (@Field.toCommRing K.carrier (inferInstance : Field K)))) sK n X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) ≫
      (compositionPullback (@FamilyReparametrization.squareMap P (Spec (@CommRingCat.of K.carrier (@Field.toCommRing K.carrier (inferInstance : Field K)))) sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)) (@ParametrizedContact.evaluationSquare P (Spec (@CommRingCat.of K.carrier (@Field.toCommRing K.carrier (inferInstance : Field K)))) sK n X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (@ParametrizedContact.evaluationSquare P (Spec (@CommRingCat.of K.carrier (@Field.toCommRing K.carrier (inferInstance : Field K)))) sK n X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (@FamilyReparametrization.squareMap_evaluation P (Spec (@CommRingCat.of K.carrier (@Field.toCommRing K.carrier (inferInstance : Field K)))) sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk) n X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q) (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk) (transition_evaluation Q sK q b hq k hk)) (movingPairBundleLeft X.variety X.contact)).hom = (@ParametrizedContact.leftSection P (Spec (@CommRingCat.of K.carrier (@Field.toCommRing K.carrier (inferInstance : Field K)))) sK n X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk))) :
    pullSection (@FamilyReparametrization.squareMap P (Spec K) sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)) (@ParametrizedContact.leftSection P (Spec K) sK n X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) ≫
      (compositionPullback (@FamilyReparametrization.squareMap P (Spec K) sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)) (@ParametrizedContact.evaluationSquare P (Spec K) sK n X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (@ParametrizedContact.evaluationSquare P (Spec K) sK n X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (@FamilyReparametrization.squareMap_evaluation P (Spec K) sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk) n X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q) (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk) (transition_evaluation Q sK q b hq k hk)) (movingPairBundleLeft X.variety X.contact)).hom = (@ParametrizedContact.leftSection P (Spec K) sK n X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) := by
  exact (FieldReparamTransport.predicate_transport (FieldReparamTransport.Data P X)
    (fun _ d =>
      pullSection (FamilyReparametrization.squareMap P d.s d.e d.he)
        (ParametrizedContact.leftSection P d.s X d.f d.hf) ≫
        (compositionPullback (FamilyReparametrization.squareMap P d.s d.e d.he)
          (ParametrizedContact.evaluationSquare P d.s X d.f d.hf)
          (ParametrizedContact.evaluationSquare P d.s X d.g d.hg)
          (FamilyReparametrization.squareMap_evaluation P d.s d.e d.he X
            d.f d.hf d.g d.hg d.hcomp)
          (movingPairBundleLeft X.variety X.contact)).hom =
        ParametrizedContact.leftSection P d.s X d.g d.hg)
    (RepackedFieldAccessors.spec_eq K)
    (FieldReparamTransport.data_heq P X (RepackedFieldAccessors.spec_eq K)
      sK sK (RepackedFieldAccessors.base_heq K sK)
      (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation Q sK q) (RepackedFieldAccessors.map_heq P K sK (SmoothFamily.atPointEvaluation Q sK q))
      (SmoothFamily.atPointEvaluation_overC Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)
      (transition Q sK q b hq k hk) (transition Q sK q b hq k hk) (RepackedFieldAccessors.iso_heq P K sK (transition Q sK q b hq k hk))
      (transition_parameter Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)
      (evaluation (F := F) sK k) (evaluation (F := F) sK k) (RepackedFieldAccessors.map_heq P K sK (evaluation (F := F) sK k))
      (evaluation_overC Q sK q b hq k hk) (evaluation_overC Q sK q b hq k hk) (transition_evaluation Q sK q b hq k hk) (transition_evaluation Q sK q b hq k hk))).mp hi


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_18_field_left_base_transport"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_19_field_right_base_transport"
  err.flush

private theorem field_right_base_transport
    (hi : pullSection (@FamilyReparametrization.squareMap P (Spec (@CommRingCat.of K.carrier (@Field.toCommRing K.carrier (inferInstance : Field K)))) sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)) (@ParametrizedContact.rightSection P (Spec (@CommRingCat.of K.carrier (@Field.toCommRing K.carrier (inferInstance : Field K)))) sK n X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) ≫
      (compositionPullback (@FamilyReparametrization.squareMap P (Spec (@CommRingCat.of K.carrier (@Field.toCommRing K.carrier (inferInstance : Field K)))) sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)) (@ParametrizedContact.evaluationSquare P (Spec (@CommRingCat.of K.carrier (@Field.toCommRing K.carrier (inferInstance : Field K)))) sK n X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (@ParametrizedContact.evaluationSquare P (Spec (@CommRingCat.of K.carrier (@Field.toCommRing K.carrier (inferInstance : Field K)))) sK n X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (@FamilyReparametrization.squareMap_evaluation P (Spec (@CommRingCat.of K.carrier (@Field.toCommRing K.carrier (inferInstance : Field K)))) sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk) n X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q) (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk) (transition_evaluation Q sK q b hq k hk)) (movingPairBundleRight X.variety X.contact)).hom = (@ParametrizedContact.rightSection P (Spec (@CommRingCat.of K.carrier (@Field.toCommRing K.carrier (inferInstance : Field K)))) sK n X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk))) :
    pullSection (@FamilyReparametrization.squareMap P (Spec K) sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)) (@ParametrizedContact.rightSection P (Spec K) sK n X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) ≫
      (compositionPullback (@FamilyReparametrization.squareMap P (Spec K) sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)) (@ParametrizedContact.evaluationSquare P (Spec K) sK n X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)) (@ParametrizedContact.evaluationSquare P (Spec K) sK n X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) (@FamilyReparametrization.squareMap_evaluation P (Spec K) sK (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk) n X (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q) (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk) (transition_evaluation Q sK q b hq k hk)) (movingPairBundleRight X.variety X.contact)).hom = (@ParametrizedContact.rightSection P (Spec K) sK n X (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)) := by
  exact (FieldReparamTransport.predicate_transport (FieldReparamTransport.Data P X)
    (fun _ d =>
      pullSection (FamilyReparametrization.squareMap P d.s d.e d.he)
        (ParametrizedContact.rightSection P d.s X d.f d.hf) ≫
        (compositionPullback (FamilyReparametrization.squareMap P d.s d.e d.he)
          (ParametrizedContact.evaluationSquare P d.s X d.f d.hf)
          (ParametrizedContact.evaluationSquare P d.s X d.g d.hg)
          (FamilyReparametrization.squareMap_evaluation P d.s d.e d.he X
            d.f d.hf d.g d.hg d.hcomp)
          (movingPairBundleRight X.variety X.contact)).hom =
        ParametrizedContact.rightSection P d.s X d.g d.hg)
    (RepackedFieldAccessors.spec_eq K)
    (FieldReparamTransport.data_heq P X (RepackedFieldAccessors.spec_eq K)
      sK sK (RepackedFieldAccessors.base_heq K sK)
      (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation Q sK q) (RepackedFieldAccessors.map_heq P K sK (SmoothFamily.atPointEvaluation Q sK q))
      (SmoothFamily.atPointEvaluation_overC Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q)
      (transition Q sK q b hq k hk) (transition Q sK q b hq k hk) (RepackedFieldAccessors.iso_heq P K sK (transition Q sK q b hq k hk))
      (transition_parameter Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)
      (evaluation (F := F) sK k) (evaluation (F := F) sK k) (RepackedFieldAccessors.map_heq P K sK (evaluation (F := F) sK k))
      (evaluation_overC Q sK q b hq k hk) (evaluation_overC Q sK q b hq k hk) (transition_evaluation Q sK q b hq k hk) (transition_evaluation Q sK q b hq k hk))).mp hi



#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_19_field_right_base_transport"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_20_smoothLeft_field"
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
  apply field_left_base_transport Q K sK q b hq k hk
  exact FamilyReparametrization.leftSection_field P Q.coverToC X
    (SmoothFamily.evaluation Q) (SmoothFamily.evaluation_overC Q)
    (SmoothFamily.nonconstantFamily Q) K sK q
    (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q) rfl
    (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)
    (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)
    (transition_evaluation Q sK q b hq k hk)


#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_20_smoothLeft_field"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_21_smoothRight_field"
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
  apply field_right_base_transport Q K sK q b hq k hk
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
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_21_smoothRight_field"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_22_smoothLeft"
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
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_22_smoothLeft"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE ENTER_23_smoothRight"
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
  err.putStrLn "GENERIC_SINGLE_FIELD_STAGE EXIT_23_smoothRight"
  err.flush

