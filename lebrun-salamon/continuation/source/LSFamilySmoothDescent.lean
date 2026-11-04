import LSFamilyDescentReparametrization
import LSOpenSectionTransport
import LSFamilySmoothCoordinates
import LSFamilySmoothPointValues
import LSFamilySmoothNormalization

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

namespace SmoothFamily

variable {P : ProjectiveLineOverC} {p : ProjectiveLinePoint P}
variable {n : ℕ} {X : ContactFanoManifold n} {g : VeryFreeContactConic P p X}
variable {N : FullConicNeighborhood P p X g}
variable {F : StableMaps.ProjectiveNodalFamily P p X.variety X.contact.sequence.line 2}
variable (Q : StableMaps.FullHomComparison P p X.variety N.homSpace N.neighborhood
  X.contact.sequence.line 2 F)


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
  have h := congrArg
    (fun m : Q.ReducedMemberCover t ⟶ N.neighborhood.toScheme => z.val ≫ m)
    (memberToParametrized_toHom Q t)
  calc
    ((z.val ≫ memberToParametrized Q t) ≫ Q.parametrizedSquareToCover) ≫ Q.toHom =
        z.val ≫ (memberToParametrized Q t ≫ Q.parametrizedSquareToCover ≫ Q.toHom) := by
          simp only [Category.assoc]
    _ = z.val ≫ (Q.reducedMemberToC t ≫ t.val) := h
    _ = t.val := by rw [← Category.assoc, z.property, Category.id_comp]

theorem memberPoint_curve
    (z : PointsOver ComplexBase (𝟙 ComplexBase) (Q.ReducedMemberCover t)
      (Q.reducedMemberToC t)) : curve Q (coverPoint Q (memberPoint Q t z)) = N.curveAt t := by
  rw [curve, memberPoint_parameter]

@[reassoc] theorem memberPoint_coordinates
    (z : PointsOver ComplexBase (𝟙 ComplexBase) (Q.ReducedMemberCover t)
      (Q.reducedMemberToC t)) :
    coordinatePair Q (memberPoint Q t z) = z.val ≫ Q.reducedMemberToSquare t := by
  simp only [coordinatePair, memberPoint, Category.assoc, memberToParametrized_coordinates]

private theorem member_left_point_transport {T : Scheme}
    (u v : RationalCurve P X.variety) (huv : u = v)
    (k k' : T ⟶ SelfProduct P.structureMap) (hkk' : k = k')
    (r : T ⟶ SelfProduct X.variety.structureMap)
    (h : k ≫ curveSquareMap P u = r) (h' : k' ≫ curveSquareMap P v = r) :
    pullSection k (Curve.leftSection P X u) ≫
        (compositionPullback k (curveSquareMap P u) r h
          (movingPairBundleLeft X.variety X.contact)).hom =
      pullSection k' (Curve.leftSection P X v) ≫
        (compositionPullback k' (curveSquareMap P v) r h'
          (movingPairBundleLeft X.variety X.contact)).hom := by
  cases huv
  cases hkk'
  rfl

private theorem member_right_point_transport {T : Scheme}
    (u v : RationalCurve P X.variety) (huv : u = v)
    (k k' : T ⟶ SelfProduct P.structureMap) (hkk' : k = k')
    (r : T ⟶ SelfProduct X.variety.structureMap)
    (h : k ≫ curveSquareMap P u = r) (h' : k' ≫ curveSquareMap P v = r) :
    pullSection k (Curve.rightSection P X u) ≫
        (compositionPullback k (curveSquareMap P u) r h
          (movingPairBundleRight X.variety X.contact)).hom =
      pullSection k' (Curve.rightSection P X v) ≫
        (compositionPullback k' (curveSquareMap P v) r h'
          (movingPairBundleRight X.variety X.contact)).hom := by
  cases huv
  cases hkk'
  rfl

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
  exact hp.trans (member_left_point_transport
    (curve Q (coverPoint Q (memberPoint Q t z))) (N.curveAt t) (memberPoint_curve Q t z)
    (coordinatePair Q (memberPoint Q t z)) (z.val ≫ Q.reducedMemberToSquare t)
    (memberPoint_coordinates Q t z) (z.val ≫ memberEvaluation Q t) hz
    (Category.assoc z.val (Q.reducedMemberToSquare t) (curveSquareMap P (N.curveAt t))))

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
  exact hp.trans (member_right_point_transport
    (curve Q (coverPoint Q (memberPoint Q t z))) (N.curveAt t) (memberPoint_curve Q t z)
    (coordinatePair Q (memberPoint Q t z)) (z.val ≫ Q.reducedMemberToSquare t)
    (memberPoint_coordinates Q t z) (z.val ≫ memberEvaluation Q t) hz
    (Category.assoc z.val (Q.reducedMemberToSquare t) (curveSquareMap P (N.curveAt t))))

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

end SmoothFamily

end LeBrunSalamon.Construction.FamilyBivectors

end
