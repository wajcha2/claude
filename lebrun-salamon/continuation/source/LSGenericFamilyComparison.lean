import LSFamilyBaseChange
import LSFamilyBivectorDescent
import LSFieldParametrization
import LSFamilyReparametrization

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

namespace RelativeSquare

/-- Cartesian source families have Cartesian complete relative squares.
The assertion includes coincident marked points. -/
theorem map_isPullback {C A D B : Scheme} (piA : C ⟶ A) (piB : D ⟶ B)
    (k : C ⟶ D) (b : A ⟶ B) (hk : IsPullback k piA piB b) :
    IsPullback (map piA piB k b hk.w) (left piA ≫ piA) (left piB ≫ piB) b := by
  have hbase : map piA piB k b hk.w ≫ (left piB ≫ piB) =
      (left piA ≫ piA) ≫ b := by
    rw [← Category.assoc, map_left, Category.assoc, hk.w, Category.assoc]
  apply IsPullback.mk' hbase
  · intro T a c ha hc
    apply pullback.hom_ext
    · apply hk.hom_ext
      · simpa only [Category.assoc, map_left] using
          congrArg (fun f => f ≫ left piB) ha
      · simpa only [Category.assoc] using hc
    · apply hk.hom_ext
      · simpa only [Category.assoc, map_right] using
          congrArg (fun f => f ≫ right piB) ha
      · simpa only [Category.assoc, pullback.condition] using hc
  · intro T a c hac
    have h₁ : (a ≫ left piB) ≫ piB = c ≫ b := by
      simpa only [Category.assoc] using hac
    have h₂ : (a ≫ right piB) ≫ piB = c ≫ b := by
      rw [Category.assoc, ← pullback.condition]
      simpa only [Category.assoc] using h₁
    let l₁ := hk.lift (a ≫ left piB) c h₁
    let l₂ := hk.lift (a ≫ right piB) c h₂
    let l := pullback.lift l₁ l₂ (by
      simp only [l₁, l₂, IsPullback.lift_snd])
    refine ⟨l, ?_, ?_⟩
    · apply pullback.hom_ext
      · simp only [l, Category.assoc, map_left, pullback.lift_fst_assoc,
          l₁, IsPullback.lift_fst]
      · simp only [l, Category.assoc, map_right, pullback.lift_snd_assoc,
          l₂, IsPullback.lift_fst]
    · simp only [l, Category.assoc, pullback.lift_fst_assoc, l₁, IsPullback.lift_snd]

end RelativeSquare

namespace Parametrized

variable (P : ProjectiveLineOverC)
variable {A B : Scheme} (sA : A ⟶ ComplexBase) (sB : B ⟶ ComplexBase)
variable (b : A ⟶ B) (hb : b ≫ sB = sA)

abbrev baseChangeSource : Source P sA ⟶ Source P sB :=
  rationalSourceMap P (⟨b, hb⟩ : PointsOver A sA B sB)

@[reassoc] theorem baseChangeSource_first :
    baseChangeSource P sA sB b hb ≫ projection P sB = projection P sA :=
  pullback.lift_fst _ _ _

@[reassoc] theorem baseChangeSource_parameter :
    baseChangeSource P sA sB b hb ≫ parameter P sB = parameter P sA ≫ b :=
  pullback.lift_snd _ _ _

theorem baseChangeSource_isPullback :
    IsPullback (baseChangeSource P sA sB b hb) (parameter P sA) (parameter P sB) b := by
  apply IsPullback.of_right (t := IsPullback.of_hasPullback P.structureMap sB)
  · simpa only [baseChangeSource_first, hb] using
      (IsPullback.of_hasPullback P.structureMap sA)
  · exact baseChangeSource_parameter P sA sB b hb

def baseChangeSquare : Square P sA ⟶ Square P sB :=
  RelativeSquare.map (parameter P sA) (parameter P sB)
    (baseChangeSource P sA sB b hb) b (baseChangeSource_parameter P sA sB b hb)

theorem baseChangeSquare_isPullback :
    IsPullback (baseChangeSquare P sA sB b hb)
      (RelativeSquare.left (parameter P sA) ≫ parameter P sA)
      (RelativeSquare.left (parameter P sB) ≫ parameter P sB) b :=
  RelativeSquare.map_isPullback (parameter P sA) (parameter P sB)
    (baseChangeSource P sA sB b hb) b (baseChangeSource_isPullback P sA sB b hb)

theorem baseChangeSquare_surjective [Surjective b] :
    Surjective (baseChangeSquare P sA sB b hb) :=
  MorphismProperty.of_isPullback (baseChangeSquare_isPullback P sA sB b hb).flip
    (show Surjective b from inferInstance)

theorem baseChangeSquare_flat [Flat b] : Flat (baseChangeSquare P sA sB b hb) :=
  MorphismProperty.of_isPullback (baseChangeSquare_isPullback P sA sB b hb).flip
    (show Flat b from inferInstance)

theorem baseChangeSquare_quasiCompact [QuasiCompact b] :
    QuasiCompact (baseChangeSquare P sA sB b hb) :=
  MorphismProperty.of_isPullback (baseChangeSquare_isPullback P sA sB b hb).flip
    (show QuasiCompact b from inferInstance)

/-- Faithfully flat quasi-compact base change detects an actual section
on the complete source square, including a field extension. -/
theorem baseChangeSquare_section_injective [Flat b] [Surjective b] [QuasiCompact b]
    {r : ℕ} (E : AlgebraicVectorBundle (Square P sB) r) :
    Function.Injective (fun a : AlgebraicSection E.sheaf =>
      pullSection (baseChangeSquare P sA sB b hb) a) := by
  letI := baseChangeSquare_surjective P sA sB b hb
  letI := baseChangeSquare_flat P sA sB b hb
  letI := baseChangeSquare_quasiCompact P sA sB b hb
  exact FlatSectionDescent.pullSection_injective_of_epi (baseChangeSquare P sA sB b hb) E

end Parametrized

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
  simp only [Category.assoc, pullback.congrHom_hom, pullback.map_fst,
    Category.comp_id, hk.isoPullback_hom_fst]

@[reassoc] theorem transition_parameter :
    (transition Q sT q b hq k hk).hom ≫ Parametrized.parameter P sT =
      Parametrized.parameter P sT := by
  rw [← Q.atPointIso_parameter sT q, ← Category.assoc, transition_fibre]
  simp only [Category.assoc, pullback.congrHom_hom, pullback.map_snd,
    Category.comp_id, hk.isoPullback_hom_snd]

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

/-- Comparison over an arbitrary field when an actual Q-point has
been supplied. Reparametrization is proved by finite-type spreading of
the actual automorphism, and retains the original family evaluation. -/
theorem smoothLeft_field :
    pullSection a (SmoothFamily.smoothLeft Q) ≫
      (compositionPullback a (SmoothFamily.smoothEvaluation (F := F))
        (squareEvaluation Q sK q b hq k hk) (smooth_evaluation Q sK q b hq k hk a ha)
        (movingPairBundleLeft X.variety X.contact)).hom =
      ParametrizedContact.leftSection P sK X (evaluation (F := F) sK k)
        (evaluation_overC Q sK q b hq k hk) := by
  letI : LocallyOfFiniteType Q.coverToC := SmoothFamily.cover_locallyOfFiniteType Q
  apply smoothLeft_of_invariance Q sK q b hq k hk a ha
  exact FamilyReparametrization.leftSection_field P Q.coverToC X
    (SmoothFamily.evaluation Q) (SmoothFamily.evaluation_overC Q)
    (SmoothFamily.nonconstantFamily Q) K sK q
    (SmoothFamily.atPointEvaluation Q sK q) (SmoothFamily.atPointEvaluation_overC Q sK q) rfl
    (transition Q sK q b hq k hk) (transition_parameter Q sK q b hq k hk)
    (evaluation (F := F) sK k) (evaluation_overC Q sK q b hq k hk)
    (transition_evaluation Q sK q b hq k hk)

theorem smoothRight_field :
    pullSection a (SmoothFamily.smoothRight Q) ≫
      (compositionPullback a (SmoothFamily.smoothEvaluation (F := F))
        (squareEvaluation Q sK q b hq k hk) (smooth_evaluation Q sK q b hq k hk a ha)
        (movingPairBundleRight X.variety X.contact)).hom =
      ParametrizedContact.rightSection P sK X (evaluation (F := F) sK k)
        (evaluation_overC Q sK q b hq k hk) := by
  letI : LocallyOfFiniteType Q.coverToC := SmoothFamily.cover_locallyOfFiniteType Q
  apply smoothRight_of_invariance Q sK q b hq k hk a ha
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

/-- A Cartesian parametrization has the original complex structure on
its evaluation map. -/
theorem evaluation_overC {T : Scheme} (sT : T ⟶ ComplexBase)
    (b : T ⟶ F.smoothOpen.toScheme) (hb : (b ≫ F.smoothOpen.ι) ≫ F.toC = sT)
    (k : Parametrized.Source P sT ⟶ F.source)
    (hk : IsPullback k (Parametrized.parameter P sT) F.parameter (b ≫ F.smoothOpen.ι)) :
    (k ≫ F.evaluation) ≫ X.variety.structureMap = Parametrized.parameter P sT ≫ sT := by
  rw [Category.assoc, F.overC, ← Category.assoc, hk.w, Category.assoc, hb]

theorem square_evaluation {T : Scheme} (sT : T ⟶ ComplexBase)
    (b : T ⟶ F.smoothOpen.toScheme) (hb : (b ≫ F.smoothOpen.ι) ≫ F.toC = sT)
    (k : Parametrized.Source P sT ⟶ F.source)
    (hk : IsPullback k (Parametrized.parameter P sT) F.parameter (b ≫ F.smoothOpen.ι))
    (a : Parametrized.Square P sT ⟶ F.smoothSquareOpen.toScheme)
    (ha : a ≫ F.smoothSquareOpen.ι = RelativeSquare.map (Parametrized.parameter P sT)
      F.parameter k (b ≫ F.smoothOpen.ι) hk.w) :
    a ≫ SmoothFamily.smoothEvaluation (F := F) =
      ParametrizedContact.evaluationSquare P sT X (k ≫ F.evaluation)
        (evaluation_overC sT b hb k hk) := by
  rw [SmoothFamily.smoothEvaluation, ← Category.assoc, ha]
  apply pullback.hom_ext
  · simp only [ParametrizedContact.evaluationSquare, Parametrized.evaluationSquare,
      Category.assoc, F.squareEvaluation_first, RelativeSquare.map_left_assoc,
      RelativeSquare.evaluation_left]
  · simp only [ParametrizedContact.evaluationSquare, Parametrized.evaluationSquare,
      Category.assoc, F.squareEvaluation_second, RelativeSquare.map_right_assoc,
      RelativeSquare.evaluation_right]

-- A field structure is chosen only from the actual bundled ring predicate.
variable (K : CommRingCat) [hK : Fact (IsField K)] (sK : Spec K ⟶ ComplexBase)

local instance : Field K := hK.out.toField
variable (b : Spec K ⟶ F.smoothOpen.toScheme)
variable (hb : (b ≫ F.smoothOpen.ι) ≫ F.toC = sK)
variable (k : Parametrized.Source P sK ⟶ F.source)
variable (hk : IsPullback k (Parametrized.parameter P sK) F.parameter (b ≫ F.smoothOpen.ι))

local instance : Surjective Q.toSmooth := Q.smoothSurjective

abbrev extensionToC : Spec (Q.parametrizingField K b) ⟶ ComplexBase :=
  Q.parametrizingExtension K b ≫ sK

def coverPoint : PointsOver (Spec (Q.parametrizingField K b)) (extensionToC Q K sK b)
    Q.cover Q.coverToC :=
  ⟨Q.parametrizingPoint K b, Q.parametrizingPoint_overC K b sK hb⟩

abbrev extendedBase : Spec (Q.parametrizingField K b) ⟶ F.smoothOpen.toScheme :=
  Q.parametrizingExtension K b ≫ b

@[reassoc] theorem coverPoint_base :
    (coverPoint Q K sK b hb).val ≫ Q.toSmooth = extendedBase Q K b :=
  Q.parametrizingPoint_base K b

include hb in
theorem extendedBase_overC :
    (extendedBase Q K b ≫ F.smoothOpen.ι) ≫ F.toC = extensionToC Q K sK b := by
  simp only [extendedBase, extensionToC, Category.assoc] at hb ⊢
  rw [hb]

abbrev sourceMap : Parametrized.Source P (extensionToC Q K sK b) ⟶ Parametrized.Source P sK :=
  Parametrized.baseChangeSource P (extensionToC Q K sK b) sK
    (Q.parametrizingExtension K b) rfl

abbrev squareMap : Parametrized.Square P (extensionToC Q K sK b) ⟶ Parametrized.Square P sK :=
  Parametrized.baseChangeSquare P (extensionToC Q K sK b) sK
    (Q.parametrizingExtension K b) rfl

abbrev extendedSource : Parametrized.Source P (extensionToC Q K sK b) ⟶ F.source :=
  sourceMap Q K sK b ≫ k

include hk in
theorem extendedSource_isPullback :
    IsPullback (extendedSource Q K sK b k)
      (Parametrized.parameter P (extensionToC Q K sK b)) F.parameter
      (extendedBase Q K b ≫ F.smoothOpen.ι) := by
  simpa only [extendedSource, sourceMap, extendedBase, Category.assoc] using
    (Parametrized.baseChangeSource_isPullback P (extensionToC Q K sK b) sK
      (Q.parametrizingExtension K b) rfl).paste_horiz hk

@[reassoc] theorem evaluationSquare_baseChange :
    squareMap Q K sK b ≫
        ParametrizedContact.evaluationSquare P sK X (k ≫ F.evaluation)
          (evaluation_overC sK b hb k hk) =
      ParametrizedContact.evaluationSquare P (extensionToC Q K sK b) X
        (extendedSource Q K sK b k ≫ F.evaluation)
        (evaluation_overC (extensionToC Q K sK b) (extendedBase Q K b)
          (extendedBase_overC Q K sK b hb) (extendedSource Q K sK b k)
          (extendedSource_isPullback Q K sK b k hk)) :=
  RelativeSquare.map_evaluation (Parametrized.parameter P (extensionToC Q K sK b))
    (Parametrized.parameter P sK) (sourceMap Q K sK b) (Q.parametrizingExtension K b)
    (Parametrized.baseChangeSource_parameter P (extensionToC Q K sK b) sK
      (Q.parametrizingExtension K b) rfl)
    X.variety.structureMap (extensionToC Q K sK b) sK
    (extendedSource Q K sK b k ≫ F.evaluation) (k ≫ F.evaluation)
    (evaluation_overC (extensionToC Q K sK b) (extendedBase Q K b)
      (extendedBase_overC Q K sK b hb) (extendedSource Q K sK b k)
      (extendedSource_isPullback Q K sK b k hk))
    (evaluation_overC sK b hb k hk) (Category.assoc _ _ _).symm

theorem left_baseChange :
    pullSection (squareMap Q K sK b)
        (ParametrizedContact.leftSection P sK X (k ≫ F.evaluation)
          (evaluation_overC sK b hb k hk)) ≫
      (compositionPullback (squareMap Q K sK b)
        (ParametrizedContact.evaluationSquare P sK X (k ≫ F.evaluation)
          (evaluation_overC sK b hb k hk))
        (ParametrizedContact.evaluationSquare P (extensionToC Q K sK b) X
          (extendedSource Q K sK b k ≫ F.evaluation)
          (evaluation_overC (extensionToC Q K sK b) (extendedBase Q K b)
            (extendedBase_overC Q K sK b hb) (extendedSource Q K sK b k)
            (extendedSource_isPullback Q K sK b k hk)))
        (evaluationSquare_baseChange Q K sK b hb k hk)
        (movingPairBundleLeft X.variety X.contact)).hom =
      ParametrizedContact.leftSection P (extensionToC Q K sK b) X
        (extendedSource Q K sK b k ≫ F.evaluation)
        (evaluation_overC (extensionToC Q K sK b) (extendedBase Q K b)
          (extendedBase_overC Q K sK b hb) (extendedSource Q K sK b k)
          (extendedSource_isPullback Q K sK b k hk)) :=
  ParametrizedContact.leftSection_baseChange P (extensionToC Q K sK b) sK
    (Q.parametrizingExtension K b) rfl (sourceMap Q K sK b)
    (Parametrized.baseChangeSource_first P (extensionToC Q K sK b) sK
      (Q.parametrizingExtension K b) rfl)
    (Parametrized.baseChangeSource_parameter P (extensionToC Q K sK b) sK
      (Q.parametrizingExtension K b) rfl)
    X (k ≫ F.evaluation) (evaluation_overC sK b hb k hk)
    (extendedSource Q K sK b k ≫ F.evaluation)
    (evaluation_overC (extensionToC Q K sK b) (extendedBase Q K b)
      (extendedBase_overC Q K sK b hb) (extendedSource Q K sK b k)
      (extendedSource_isPullback Q K sK b k hk))
    (Category.assoc _ _ _).symm (squareMap Q K sK b)
    (RelativeSquare.map_left _ _ _ _ _) (RelativeSquare.map_right _ _ _ _ _)
    (evaluationSquare_baseChange Q K sK b hb k hk)

theorem right_baseChange :
    pullSection (squareMap Q K sK b)
        (ParametrizedContact.rightSection P sK X (k ≫ F.evaluation)
          (evaluation_overC sK b hb k hk)) ≫
      (compositionPullback (squareMap Q K sK b)
        (ParametrizedContact.evaluationSquare P sK X (k ≫ F.evaluation)
          (evaluation_overC sK b hb k hk))
        (ParametrizedContact.evaluationSquare P (extensionToC Q K sK b) X
          (extendedSource Q K sK b k ≫ F.evaluation)
          (evaluation_overC (extensionToC Q K sK b) (extendedBase Q K b)
            (extendedBase_overC Q K sK b hb) (extendedSource Q K sK b k)
            (extendedSource_isPullback Q K sK b k hk)))
        (evaluationSquare_baseChange Q K sK b hb k hk)
        (movingPairBundleRight X.variety X.contact)).hom =
      ParametrizedContact.rightSection P (extensionToC Q K sK b) X
        (extendedSource Q K sK b k ≫ F.evaluation)
        (evaluation_overC (extensionToC Q K sK b) (extendedBase Q K b)
          (extendedBase_overC Q K sK b hb) (extendedSource Q K sK b k)
          (extendedSource_isPullback Q K sK b k hk)) :=
  ParametrizedContact.rightSection_baseChange P (extensionToC Q K sK b) sK
    (Q.parametrizingExtension K b) rfl (sourceMap Q K sK b)
    (Parametrized.baseChangeSource_first P (extensionToC Q K sK b) sK
      (Q.parametrizingExtension K b) rfl)
    (Parametrized.baseChangeSource_parameter P (extensionToC Q K sK b) sK
      (Q.parametrizingExtension K b) rfl)
    X (k ≫ F.evaluation) (evaluation_overC sK b hb k hk)
    (extendedSource Q K sK b k ≫ F.evaluation)
    (evaluation_overC (extensionToC Q K sK b) (extendedBase Q K b)
      (extendedBase_overC Q K sK b hb) (extendedSource Q K sK b k)
      (extendedSource_isPullback Q K sK b k hk))
    (Category.assoc _ _ _).symm (squareMap Q K sK b)
    (RelativeSquare.map_left _ _ _ _ _) (RelativeSquare.map_right _ _ _ _ _)
    (evaluationSquare_baseChange Q K sK b hb k hk)

variable (a : Parametrized.Square P sK ⟶ F.smoothSquareOpen.toScheme)
variable (ha : a ≫ F.smoothSquareOpen.ι = RelativeSquare.map (Parametrized.parameter P sK)
  F.parameter k (b ≫ F.smoothOpen.ι) hk.w)

abbrev extendedSquare : Parametrized.Square P (extensionToC Q K sK b) ⟶
    F.smoothSquareOpen.toScheme := squareMap Q K sK b ≫ a

@[reassoc] theorem extendedSquare_family :
    extendedSquare Q K sK b a ≫ F.smoothSquareOpen.ι =
      RelativeSquare.map (Parametrized.parameter P (extensionToC Q K sK b))
        F.parameter (extendedSource Q K sK b k) (extendedBase Q K b ≫ F.smoothOpen.ι)
        (extendedSource_isPullback Q K sK b k hk).w := by
  rw [extendedSquare, Category.assoc, ha]
  apply pullback.hom_ext
  · simp only [squareMap, Parametrized.baseChangeSquare, Category.assoc,
      RelativeSquare.map_left, RelativeSquare.map_left_assoc, extendedSource, sourceMap]
  · simp only [squareMap, Parametrized.baseChangeSquare, Category.assoc,
      RelativeSquare.map_right, RelativeSquare.map_right_assoc, extendedSource, sourceMap]

/-- The whole-square extension is a faithfully flat quasi-compact
cover, so the field comparison can descend without selecting a section. -/
theorem squareMap_section_injective {r : ℕ}
    (E : AlgebraicVectorBundle (Parametrized.Square P sK) r) :
    Function.Injective (fun s : AlgebraicSection E.sheaf =>
      pullSection (squareMap Q K sK b) s) := by
  letI : Surjective (Q.parametrizingExtension K b) := Q.parametrizingExtension_surjective K b
  letI : Flat (Q.parametrizingExtension K b) := inferInstance
  letI : QuasiCompact (Q.parametrizingExtension K b) := by
    apply (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr
    infer_instance
  exact Parametrized.baseChangeSquare_section_injective P (extensionToC Q K sK b) sK
    (Q.parametrizingExtension K b) rfl E

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
