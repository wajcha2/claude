import LSFamilyDescentReparametrization
import LSOpenSectionTransport
import LSFamilySmoothCoordinates
import LSFamilySmoothPointValues

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


include Q in
theorem smooth_locallyOfFiniteType : LocallyOfFiniteType (smoothToC (F := F)) := by
  letI : IsProper F.toC := F.baseProper
  letI : IsProper F.squareToBase := F.squareToBase_proper
  dsimp only [smoothToC]
  infer_instance

theorem parametrized_reduced : AlgebraicGeometry.IsReduced Q.ParametrizedSquare := by
  letI : IsIntegral F.Square := F.square_integral
  letI : IsLocallyNoetherian F.Square := F.square_locallyNoetherian
  letI : AlgebraicGeometry.IsReduced F.smoothSquareOpen.toScheme :=
    isReduced_of_isOpenImmersion F.smoothSquareOpen.ι
  letI : IsLocallyNoetherian F.smoothSquareOpen.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian F.smoothSquareOpen.ι
  letI : Smooth Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_smooth
  letI : GeometricallyIntegral Q.parametrizedSquareToSmooth :=
    Q.parametrizedSquareToSmooth_geometricallyIntegral
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
    Q.parametrizedSquareToSmooth

theorem overlap_reduced : AlgebraicGeometry.IsReduced
    (pullback Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth) := by
  letI : LocallyOfFiniteType (smoothToC (F := F)) := smooth_locallyOfFiniteType Q
  letI : IsLocallyNoetherian F.smoothSquareOpen.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (smoothToC (F := F))
  letI : Smooth Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_smooth
  letI : GeometricallyIntegral Q.parametrizedSquareToSmooth :=
    Q.parametrizedSquareToSmooth_geometricallyIntegral
  letI : AlgebraicGeometry.IsReduced Q.ParametrizedSquare := parametrized_reduced Q
  letI : IsLocallyNoetherian Q.ParametrizedSquare :=
    LocallyOfFiniteType.isLocallyNoetherian Q.parametrizedSquareToSmooth
  infer_instance

theorem overlap_locallyOfFiniteType : LocallyOfFiniteType
    (pullback.fst Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth ≫
      Q.parametrizedSquareToSmooth ≫ smoothToC (F := F)) := by
  letI : LocallyOfFiniteType (smoothToC (F := F)) := smooth_locallyOfFiniteType Q
  letI : Smooth Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_smooth
  infer_instance

def leftCover : AlgebraicSection
    (pullbackModule Q.parametrizedSquareToSmooth
      (MovingPair.leftBundle (smoothEvaluation (F := F))).sheaf) :=
  left Q ≫ (compositionPullback Q.parametrizedSquareToSmooth
    (smoothEvaluation (F := F)) (parametrizedEvaluation Q) (evaluation_commutes Q)
    (movingPairBundleLeft X.variety X.contact)).inv

def rightCover : AlgebraicSection
    (pullbackModule Q.parametrizedSquareToSmooth
      (MovingPair.rightBundle (smoothEvaluation (F := F))).sheaf) :=
  right Q ≫ (compositionPullback Q.parametrizedSquareToSmooth
    (smoothEvaluation (F := F)) (parametrizedEvaluation Q) (evaluation_commutes Q)
    (movingPairBundleRight X.variety X.contact)).inv

@[reassoc] theorem leftCover_comparison : leftCover Q ≫
    (compositionPullback Q.parametrizedSquareToSmooth (smoothEvaluation (F := F))
      (parametrizedEvaluation Q) (evaluation_commutes Q)
      (movingPairBundleLeft X.variety X.contact)).hom = left Q := by
  simp only [leftCover, Category.assoc, Iso.inv_hom_id, Category.comp_id]

@[reassoc] theorem rightCover_comparison : rightCover Q ≫
    (compositionPullback Q.parametrizedSquareToSmooth (smoothEvaluation (F := F))
      (parametrizedEvaluation Q) (evaluation_commutes Q)
      (movingPairBundleRight X.variety X.contact)).hom = right Q := by
  simp only [rightCover, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Equality on the actual double overlap, proved from equality at
complex points of that reduced finite-type scheme. -/
theorem leftCover_compatible :
    pullSection (pullback.fst Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        (leftCover Q) ≫
      (pullbackSquareIso
        (pullback.fst Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        Q.parametrizedSquareToSmooth
        (pullback.snd Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        Q.parametrizedSquareToSmooth pullback.condition
        (MovingPair.leftBundle (smoothEvaluation (F := F))).sheaf).hom =
      pullSection (pullback.snd Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        (leftCover Q) := by
  letI := overlap_reduced Q
  letI := overlap_locallyOfFiniteType Q
  apply SectionTransport.compatible_of_point_values Q.parametrizedSquareToSmooth
    (smoothToC (F := F)) (MovingPair.leftBundle (smoothEvaluation (F := F))) (leftCover Q)
  intro q₀ q₁ h
  have hz : (q₁.val ≫ Q.parametrizedSquareToSmooth) ≫ smoothEvaluation (F := F) =
      q₁.val ≫ parametrizedEvaluation Q := by rw [Category.assoc, evaluation_commutes]
  apply (cancel_mono (compositionPullback (q₁.val ≫ Q.parametrizedSquareToSmooth)
    (smoothEvaluation (F := F)) (q₁.val ≫ parametrizedEvaluation Q) hz
    (movingPairBundleLeft X.variety X.contact)).hom).mp
  simp only [Category.assoc]
  exact (SectionTransport.inverse_composition_value q₀.val Q.parametrizedSquareToSmooth
    (smoothEvaluation (F := F)) (parametrizedEvaluation Q) (evaluation_commutes Q)
    (q₁.val ≫ Q.parametrizedSquareToSmooth) h (q₁.val ≫ parametrizedEvaluation Q) hz
    (same_evaluation Q q₀ q₁ h) (E := movingPairBundleLeft X.variety X.contact) (left Q)).trans
    ((left_point_values Q q₀ q₁ h).trans
      (SectionTransport.inverse_composition_value q₁.val Q.parametrizedSquareToSmooth
        (smoothEvaluation (F := F)) (parametrizedEvaluation Q) (evaluation_commutes Q)
        (q₁.val ≫ Q.parametrizedSquareToSmooth) rfl (q₁.val ≫ parametrizedEvaluation Q) hz
        rfl (E := movingPairBundleLeft X.variety X.contact) (left Q)).symm)

theorem rightCover_compatible :
    pullSection (pullback.fst Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        (rightCover Q) ≫
      (pullbackSquareIso
        (pullback.fst Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        Q.parametrizedSquareToSmooth
        (pullback.snd Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        Q.parametrizedSquareToSmooth pullback.condition
        (MovingPair.rightBundle (smoothEvaluation (F := F))).sheaf).hom =
      pullSection (pullback.snd Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        (rightCover Q) := by
  letI := overlap_reduced Q
  letI := overlap_locallyOfFiniteType Q
  apply SectionTransport.compatible_of_point_values Q.parametrizedSquareToSmooth
    (smoothToC (F := F)) (MovingPair.rightBundle (smoothEvaluation (F := F))) (rightCover Q)
  intro q₀ q₁ h
  have hz : (q₁.val ≫ Q.parametrizedSquareToSmooth) ≫ smoothEvaluation (F := F) =
      q₁.val ≫ parametrizedEvaluation Q := by rw [Category.assoc, evaluation_commutes]
  apply (cancel_mono (compositionPullback (q₁.val ≫ Q.parametrizedSquareToSmooth)
    (smoothEvaluation (F := F)) (q₁.val ≫ parametrizedEvaluation Q) hz
    (movingPairBundleRight X.variety X.contact)).hom).mp
  simp only [Category.assoc]
  exact (SectionTransport.inverse_composition_value q₀.val Q.parametrizedSquareToSmooth
    (smoothEvaluation (F := F)) (parametrizedEvaluation Q) (evaluation_commutes Q)
    (q₁.val ≫ Q.parametrizedSquareToSmooth) h (q₁.val ≫ parametrizedEvaluation Q) hz
    (same_evaluation Q q₀ q₁ h) (E := movingPairBundleRight X.variety X.contact) (right Q)).trans
    ((right_point_values Q q₀ q₁ h).trans
      (SectionTransport.inverse_composition_value q₁.val Q.parametrizedSquareToSmooth
        (smoothEvaluation (F := F)) (parametrizedEvaluation Q) (evaluation_commutes Q)
        (q₁.val ≫ Q.parametrizedSquareToSmooth) rfl (q₁.val ≫ parametrizedEvaluation Q) hz
        rfl (E := movingPairBundleRight X.variety X.contact) (right Q)).symm)

theorem smoothLeft_exists : ∃! s : AlgebraicSection
    (MovingPair.leftBundle (smoothEvaluation (F := F))).sheaf,
    pullSection Q.parametrizedSquareToSmooth s = leftCover Q := by
  letI : Smooth Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_smooth
  letI : Surjective Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_surjective
  exact FlatSectionDescent.existsUnique_fppf Q.parametrizedSquareToSmooth
    (MovingPair.leftBundle (smoothEvaluation (F := F))) (leftCover Q) (leftCover_compatible Q)

theorem smoothRight_exists : ∃! s : AlgebraicSection
    (MovingPair.rightBundle (smoothEvaluation (F := F))).sheaf,
    pullSection Q.parametrizedSquareToSmooth s = rightCover Q := by
  letI : Smooth Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_smooth
  letI : Surjective Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_surjective
  exact FlatSectionDescent.existsUnique_fppf Q.parametrizedSquareToSmooth
    (MovingPair.rightBundle (smoothEvaluation (F := F))) (rightCover Q) (rightCover_compatible Q)

/-- The uniquely descended actual left section on the smooth family. -/
def smoothLeft : AlgebraicSection
    (MovingPair.leftBundle (smoothEvaluation (F := F))).sheaf :=
  Classical.choose (smoothLeft_exists Q)

/-- The uniquely descended actual right section on the smooth family. -/
def smoothRight : AlgebraicSection
    (MovingPair.rightBundle (smoothEvaluation (F := F))).sheaf :=
  Classical.choose (smoothRight_exists Q)

theorem smoothLeft_pullback :
    pullSection Q.parametrizedSquareToSmooth (smoothLeft Q) = leftCover Q :=
  (Classical.choose_spec (smoothLeft_exists Q)).1

theorem smoothRight_pullback :
    pullSection Q.parametrizedSquareToSmooth (smoothRight Q) = rightCover Q :=
  (Classical.choose_spec (smoothRight_exists Q)).1

/-- Universal normalization on the actual parametrization cover.
This equality may subsequently be pulled back along arbitrary schemes. -/
theorem smoothLeft_normalization :
    pullSection Q.parametrizedSquareToSmooth (smoothLeft Q) ≫
      (compositionPullback Q.parametrizedSquareToSmooth (smoothEvaluation (F := F))
        (parametrizedEvaluation Q) (evaluation_commutes Q)
        (movingPairBundleLeft X.variety X.contact)).hom = left Q := by
  rw [smoothLeft_pullback, leftCover_comparison]

theorem smoothRight_normalization :
    pullSection Q.parametrizedSquareToSmooth (smoothRight Q) ≫
      (compositionPullback Q.parametrizedSquareToSmooth (smoothEvaluation (F := F))
        (parametrizedEvaluation Q) (evaluation_commutes Q)
        (movingPairBundleRight X.variety X.contact)).hom = right Q := by
  rw [smoothRight_pullback, rightCover_comparison]

theorem smooth_commonContact :
    smoothLeft Q ≫ MovingPair.leftContact (smoothEvaluation (F := F)) =
      smoothRight Q ≫ MovingPair.rightContact (smoothEvaluation (F := F)) := by
  letI : Smooth Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_smooth
  letI : Surjective Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_surjective
  apply FlatSectionDescent.pullSection_injective_fppf Q.parametrizedSquareToSmooth
    (MovingPair.valueBundle (smoothEvaluation (F := F)))
  change pullSection Q.parametrizedSquareToSmooth
      (smoothLeft Q ≫ MovingPair.leftContact (smoothEvaluation (F := F))) =
    pullSection Q.parametrizedSquareToSmooth
      (smoothRight Q ≫ MovingPair.rightContact (smoothEvaluation (F := F)))
  apply (cancel_mono (compositionPullback Q.parametrizedSquareToSmooth
    (smoothEvaluation (F := F)) (parametrizedEvaluation Q) (evaluation_commutes Q)
    (externalSquareLine X.variety.structureMap X.contact.sequence.line).sheaf).hom).mp
  erw [pullSection_naturality Q.parametrizedSquareToSmooth
      (smoothLeft Q) (MovingPair.leftContact (smoothEvaluation (F := F))),
    pullSection_naturality Q.parametrizedSquareToSmooth
      (smoothRight Q) (MovingPair.rightContact (smoothEvaluation (F := F)))]
  simp only [Category.assoc]
  erw [Normalization.BundleGluing.compositionPullback_naturality
      Q.parametrizedSquareToSmooth (smoothEvaluation (F := F)) (parametrizedEvaluation Q)
      (evaluation_commutes Q) (movingPairContactLeft X.variety X.contact),
    Normalization.BundleGluing.compositionPullback_naturality
      Q.parametrizedSquareToSmooth (smoothEvaluation (F := F)) (parametrizedEvaluation Q)
      (evaluation_commutes Q) (movingPairContactRight X.variety X.contact)]
  rw [← Category.assoc, smoothLeft_normalization,
    ← Category.assoc, smoothRight_normalization]
  exact ParametrizedContact.commonContact P Q.coverToC X (evaluation Q) (evaluation_overC Q)

def restrictedLeft : AlgebraicSection
    (pullbackModule F.smoothSquareOpen.ι (MovingPair.leftBundle F.squareEvaluation).sheaf) :=
  smoothLeft Q ≫ (compositionPullback F.smoothSquareOpen.ι F.squareEvaluation
    (smoothEvaluation (F := F)) rfl (movingPairBundleLeft X.variety X.contact)).inv

def restrictedRight : AlgebraicSection
    (pullbackModule F.smoothSquareOpen.ι (MovingPair.rightBundle F.squareEvaluation).sheaf) :=
  smoothRight Q ≫ (compositionPullback F.smoothSquareOpen.ι F.squareEvaluation
    (smoothEvaluation (F := F)) rfl (movingPairBundleRight X.variety X.contact)).inv

theorem restricted_commonContact :
    restrictedLeft Q ≫ (Scheme.Modules.pullback F.smoothSquareOpen.ι).map
        (MovingPair.leftContact F.squareEvaluation) =
      restrictedRight Q ≫ (Scheme.Modules.pullback F.smoothSquareOpen.ι).map
        (MovingPair.rightContact F.squareEvaluation) := by
  simp only [restrictedLeft, restrictedRight, Category.assoc]
  rw [← Descent.LineValue.composition_inv_naturality,
    ← Descent.LineValue.composition_inv_naturality,
    ← Category.assoc, smooth_commonContact]
  simp only [MovingPair.rightContact, Category.assoc]

/-- The two actual rational sections on the compactified square. Their
domain is exactly the original smooth square open. -/
def rationalPair : MovingPair.RationalVectorPair F.squareEvaluation where
  domain := F.smoothSquareOpen
  dense := F.smoothSquareOpen_dense
  leftSection := OpenSection.value F.smoothSquareOpen (restrictedLeft Q)
  rightSection := OpenSection.value F.smoothSquareOpen (restrictedRight Q)
  common := by
    have h := congrArg (fun a => OpenSection.value F.smoothSquareOpen a)
      (restricted_commonContact Q)
    simpa only [OpenSection.value_map] using h

@[simp] theorem rationalPair_domain : (rationalPair Q).domain = F.smoothSquareOpen := rfl

theorem rationalPair_left_open :
    OpenSection.fromValue F.smoothSquareOpen (rationalPair Q).leftSection = restrictedLeft Q :=
  OpenSection.section_value F.smoothSquareOpen (restrictedLeft Q)

theorem rationalPair_right_open :
    OpenSection.fromValue F.smoothSquareOpen (rationalPair Q).rightSection = restrictedRight Q :=
  OpenSection.section_value F.smoothSquareOpen (restrictedRight Q)

theorem extension_left_smooth (E : (rationalPair Q).Extension) :
    pullSection F.smoothSquareOpen.ι E.leftSection ≫
      (compositionPullback F.smoothSquareOpen.ι F.squareEvaluation
        (smoothEvaluation (F := F)) rfl (movingPairBundleLeft X.variety X.contact)).hom =
      smoothLeft Q := by
  have hv : OpenSection.value F.smoothSquareOpen
      (pullSection F.smoothSquareOpen.ι E.leftSection) =
      OpenSection.value F.smoothSquareOpen (restrictedLeft Q) := by
    rw [OpenSection.value_pullSection]
    exact E.extendsLeft
  have hs := congrArg (fun a => OpenSection.fromValue F.smoothSquareOpen a) hv
  rw [OpenSection.section_value, OpenSection.section_value] at hs
  rw [hs]
  simp only [restrictedLeft, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem extension_right_smooth (E : (rationalPair Q).Extension) :
    pullSection F.smoothSquareOpen.ι E.rightSection ≫
      (compositionPullback F.smoothSquareOpen.ι F.squareEvaluation
        (smoothEvaluation (F := F)) rfl (movingPairBundleRight X.variety X.contact)).hom =
      smoothRight Q := by
  have hv : OpenSection.value F.smoothSquareOpen
      (pullSection F.smoothSquareOpen.ι E.rightSection) =
      OpenSection.value F.smoothSquareOpen (restrictedRight Q) := by
    rw [OpenSection.value_pullSection]
    exact E.extendsRight
  have hs := congrArg (fun a => OpenSection.fromValue F.smoothSquareOpen a) hv
  rw [OpenSection.section_value, OpenSection.section_value] at hs
  rw [hs]
  simp only [restrictedRight, Category.assoc, Iso.inv_hom_id, Category.comp_id]

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
  simp only [Category.assoc]
  rw [memberToParametrized_toHom Q t, ← Category.assoc, z.property, Category.id_comp]

theorem memberPoint_curve
    (z : PointsOver ComplexBase (𝟙 ComplexBase) (Q.ReducedMemberCover t)
      (Q.reducedMemberToC t)) : curve Q (coverPoint Q (memberPoint Q t z)) = N.curveAt t := by
  rw [curve, memberPoint_parameter]

@[reassoc] theorem memberPoint_coordinates
    (z : PointsOver ComplexBase (𝟙 ComplexBase) (Q.ReducedMemberCover t)
      (Q.reducedMemberToC t)) :
    coordinatePair Q (memberPoint Q t z) = z.val ≫ Q.reducedMemberToSquare t := by
  simp only [coordinatePair, memberPoint, Category.assoc, memberToParametrized_coordinates]

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
  simpa only [memberPoint_coordinates Q t z, memberPoint_curve Q t z] using hp

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
  simpa only [memberPoint_coordinates Q t z, memberPoint_curve Q t z] using hp

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
