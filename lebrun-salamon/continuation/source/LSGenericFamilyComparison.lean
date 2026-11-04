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

namespace LeBrunSalamon.Construction.FamilyBivectors.ContactSectionDescent

theorem field_section_injective_transport {T Y : Scheme}
    (f : T ⟶ Y) (B C : OModule Y) (hBC : B = C)
    (hi : Function.Injective (fun s : AlgebraicSection B => pullSection f s)) :
    Function.Injective (fun s : AlgebraicSection C => pullSection f s) := by
  cases hBC
  exact hi

theorem field_specialization_descends {T Y Z W : Scheme}
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

theorem field_left_module_eq {n : ℕ} {X : ContactFanoManifold n}
    {Y : Scheme} (f : Y ⟶ SelfProduct X.variety.structureMap) :
    (MovingPair.leftBundle f).sheaf = pullbackModule f (movingPairBundleLeft X.variety X.contact) := by
  rfl

theorem field_left_pull_input {n : ℕ} {X : ContactFanoManifold n}
    {T Y : Scheme} (q : T ⟶ Y)
    (f : Y ⟶ SelfProduct X.variety.structureMap)
    (r : T ⟶ SelfProduct X.variety.structureMap) (h : q ≫ f = r)
    (s : AlgebraicSection (MovingPair.leftBundle f).sheaf) :
    (@pullSection T Y q (MovingPair.leftBundle f).sheaf s ≫
      (compositionPullback q f r h (movingPairBundleLeft X.variety X.contact)).hom) =
    (@pullSection T Y q (pullbackModule f (movingPairBundleLeft X.variety X.contact)) s ≫
      (compositionPullback q f r h (movingPairBundleLeft X.variety X.contact)).hom) := by
  rfl

theorem field_right_module_eq {n : ℕ} {X : ContactFanoManifold n}
    {Y : Scheme} (f : Y ⟶ SelfProduct X.variety.structureMap) :
    (MovingPair.rightBundle f).sheaf = pullbackModule f (movingPairBundleRight X.variety X.contact) := by
  rfl

theorem field_right_pull_input {n : ℕ} {X : ContactFanoManifold n}
    {T Y : Scheme} (q : T ⟶ Y)
    (f : Y ⟶ SelfProduct X.variety.structureMap)
    (r : T ⟶ SelfProduct X.variety.structureMap) (h : q ≫ f = r)
    (s : AlgebraicSection (MovingPair.rightBundle f).sheaf) :
    (@pullSection T Y q (MovingPair.rightBundle f).sheaf s ≫
      (compositionPullback q f r h (movingPairBundleRight X.variety X.contact)).hom) =
    (@pullSection T Y q (pullbackModule f (movingPairBundleRight X.variety X.contact)) s ≫
      (compositionPullback q f r h (movingPairBundleRight X.variety X.contact)).hom) := by
  rfl

variable {P : ProjectiveLineOverC} {p : ProjectiveLinePoint P}
variable {n : ℕ} {X : ContactFanoManifold n} {g : VeryFreeContactConic P p X}
variable {N : FullConicNeighborhood P p X g}
variable {F : StableMaps.ProjectiveNodalFamily P p X.variety X.contact.sequence.line 2}
variable (Q : StableMaps.FullHomComparison P p X.variety N.homSpace N.neighborhood
  X.contact.sequence.line 2 F)

variable {T0 T1 : Scheme} (s0 : T0 ⟶ ComplexBase) (s1 : T1 ⟶ ComplexBase)
variable (f : Parametrized.Square P s1 ⟶ Parametrized.Square P s0)
variable (a0 : Parametrized.Square P s0 ⟶ F.smoothSquareOpen.toScheme)
variable (a1 : Parametrized.Square P s1 ⟶ F.smoothSquareOpen.toScheme)
variable (e0 : Parametrized.Source P s0 ⟶ X.variety.scheme)
variable (e1 : Parametrized.Source P s1 ⟶ X.variety.scheme)
variable (hf0 : e0 ≫ X.variety.structureMap = Parametrized.parameter P s0 ≫ s0)
variable (hf1 : e1 ≫ X.variety.structureMap = Parametrized.parameter P s1 ≫ s1)

theorem left
    (hfa : f ≫ a0 = a1)
    (ha0 : a0 ≫ (SmoothFamily.smoothEvaluation (F := F)) = (ParametrizedContact.evaluationSquare P s0 X e0 hf0))
    (ha1 : a1 ≫ (SmoothFamily.smoothEvaluation (F := F)) = (ParametrizedContact.evaluationSquare P s1 X e1 hf1))
    (hbase : f ≫ (ParametrizedContact.evaluationSquare P s0 X e0 hf0) = (ParametrizedContact.evaluationSquare P s1 X e1 hf1))
    (hi : Function.Injective (fun t : AlgebraicSection (MovingPair.leftBundle (X := X) (ParametrizedContact.evaluationSquare P s0 X e0 hf0)).sheaf => pullSection f t))
    (hbc : pullSection f (ParametrizedContact.leftSection P s0 X e0 hf0) ≫
      (compositionPullback f (ParametrizedContact.evaluationSquare P s0 X e0 hf0) (ParametrizedContact.evaluationSquare P s1 X e1 hf1) hbase (movingPairBundleLeft X.variety X.contact)).hom = (ParametrizedContact.leftSection P s1 X e1 hf1))
    (hL : pullSection a1 (SmoothFamily.smoothLeft Q) ≫
      (compositionPullback a1 (SmoothFamily.smoothEvaluation (F := F)) (ParametrizedContact.evaluationSquare P s1 X e1 hf1) ha1 (movingPairBundleLeft X.variety X.contact)).hom = (ParametrizedContact.leftSection P s1 X e1 hf1)) :
    pullSection a0 (SmoothFamily.smoothLeft Q) ≫
      (compositionPullback a0 (SmoothFamily.smoothEvaluation (F := F)) (ParametrizedContact.evaluationSquare P s0 X e0 hf0) ha0 (movingPairBundleLeft X.variety X.contact)).hom = (ParametrizedContact.leftSection P s0 X e0 hf0) := by
  exact (field_left_pull_input a0 (SmoothFamily.smoothEvaluation (F := F)) (ParametrizedContact.evaluationSquare P s0 X e0 hf0) ha0 (SmoothFamily.smoothLeft Q)).trans
    (field_specialization_descends f a0 (SmoothFamily.smoothEvaluation (F := F)) a1 (ParametrizedContact.evaluationSquare P s0 X e0 hf0) (ParametrizedContact.evaluationSquare P s1 X e1 hf1)
      hfa ha0 hbase ha1 (movingPairBundleLeft X.variety X.contact) (MovingPair.leftBundle (X := X) (ParametrizedContact.evaluationSquare P s0 X e0 hf0)).sheaf
      (field_left_module_eq (ParametrizedContact.evaluationSquare P s0 X e0 hf0)) hi (SmoothFamily.smoothLeft Q) (ParametrizedContact.leftSection P s0 X e0 hf0) (ParametrizedContact.leftSection P s1 X e1 hf1) hbc
      ((field_left_pull_input a1 (SmoothFamily.smoothEvaluation (F := F)) (ParametrizedContact.evaluationSquare P s1 X e1 hf1) ha1 (SmoothFamily.smoothLeft Q)).symm.trans hL))

theorem right
    (hfa : f ≫ a0 = a1)
    (ha0 : a0 ≫ (SmoothFamily.smoothEvaluation (F := F)) = (ParametrizedContact.evaluationSquare P s0 X e0 hf0))
    (ha1 : a1 ≫ (SmoothFamily.smoothEvaluation (F := F)) = (ParametrizedContact.evaluationSquare P s1 X e1 hf1))
    (hbase : f ≫ (ParametrizedContact.evaluationSquare P s0 X e0 hf0) = (ParametrizedContact.evaluationSquare P s1 X e1 hf1))
    (hi : Function.Injective (fun t : AlgebraicSection (MovingPair.rightBundle (X := X) (ParametrizedContact.evaluationSquare P s0 X e0 hf0)).sheaf => pullSection f t))
    (hbc : pullSection f (ParametrizedContact.rightSection P s0 X e0 hf0) ≫
      (compositionPullback f (ParametrizedContact.evaluationSquare P s0 X e0 hf0) (ParametrizedContact.evaluationSquare P s1 X e1 hf1) hbase (movingPairBundleRight X.variety X.contact)).hom = (ParametrizedContact.rightSection P s1 X e1 hf1))
    (hL : pullSection a1 (SmoothFamily.smoothRight Q) ≫
      (compositionPullback a1 (SmoothFamily.smoothEvaluation (F := F)) (ParametrizedContact.evaluationSquare P s1 X e1 hf1) ha1 (movingPairBundleRight X.variety X.contact)).hom = (ParametrizedContact.rightSection P s1 X e1 hf1)) :
    pullSection a0 (SmoothFamily.smoothRight Q) ≫
      (compositionPullback a0 (SmoothFamily.smoothEvaluation (F := F)) (ParametrizedContact.evaluationSquare P s0 X e0 hf0) ha0 (movingPairBundleRight X.variety X.contact)).hom = (ParametrizedContact.rightSection P s0 X e0 hf0) := by
  exact (field_right_pull_input a0 (SmoothFamily.smoothEvaluation (F := F)) (ParametrizedContact.evaluationSquare P s0 X e0 hf0) ha0 (SmoothFamily.smoothRight Q)).trans
    (field_specialization_descends f a0 (SmoothFamily.smoothEvaluation (F := F)) a1 (ParametrizedContact.evaluationSquare P s0 X e0 hf0) (ParametrizedContact.evaluationSquare P s1 X e1 hf1)
      hfa ha0 hbase ha1 (movingPairBundleRight X.variety X.contact) (MovingPair.rightBundle (X := X) (ParametrizedContact.evaluationSquare P s0 X e0 hf0)).sheaf
      (field_right_module_eq (ParametrizedContact.evaluationSquare P s0 X e0 hf0)) hi (SmoothFamily.smoothRight Q) (ParametrizedContact.rightSection P s0 X e0 hf0) (ParametrizedContact.rightSection P s1 X e1 hf1) hbc
      ((field_right_pull_input a1 (SmoothFamily.smoothEvaluation (F := F)) (ParametrizedContact.evaluationSquare P s1 X e1 hf1) ha1 (SmoothFamily.smoothRight Q)).symm.trans hL))

end LeBrunSalamon.Construction.FamilyBivectors.ContactSectionDescent


namespace LeBrunSalamon.Construction.FamilyBivectors.FieldPostmapTransport

/-- Transport the complete pullback/postcomposition equation while preserving
each side's own schemes, input and output modules, and morphism presentations. -/
theorem pull_post_eq_iff {T T' Y Y' : Scheme}
    (hT : T = T') (hY : Y = Y')
    (q : T ⟶ Y) (q' : T' ⟶ Y') (hq : HEq q q')
    (M : OModule Y) (M' : OModule Y') (hM : HEq M M')
    (N : OModule T) (N' : OModule T') (hN : HEq N N')
    (s : AlgebraicSection M) (s' : AlgebraicSection M') (hs : HEq s s')
    (c : pullbackModule q M ⟶ N) (c' : pullbackModule q' M' ⟶ N')
    (hc : HEq c c')
    (t : AlgebraicSection N) (t' : AlgebraicSection N') (ht : HEq t t') :
    (pullSection q s ≫ c = t) ↔ (pullSection q' s' ≫ c' = t') := by
  cases hT
  cases hY
  have hq_eq : q = q' := eq_of_heq hq
  cases hq_eq
  have hM_eq : M = M' := eq_of_heq hM
  cases hM_eq
  have hN_eq : N = N' := eq_of_heq hN
  cases hN_eq
  have hs_eq : s = s' := eq_of_heq hs
  cases hs_eq
  have hc_eq : c = c' := eq_of_heq hc
  cases hc_eq
  have ht_eq : t = t' := eq_of_heq ht
  cases ht_eq
  rfl

end LeBrunSalamon.Construction.FamilyBivectors.FieldPostmapTransport

namespace LeBrunSalamon.Construction.FamilyBivectors.FieldWitnessTransport

/-- Changing only the witnesses for the evaluation and its composite preserves
the complete left-section equation, with its original input bundle explicit. -/
theorem left_iff (P : ProjectiveLineOverC) {B : Scheme} (sB : B ⟶ ComplexBase)
    {n : ℕ} (X : ContactFanoManifold n) {Y : Scheme}
    (q : Parametrized.Square P sB ⟶ Y)
    (u : Y ⟶ SelfProduct X.variety.structureMap)
    (e : Parametrized.Source P sB ⟶ X.variety.scheme)
    (hf₁ hf₂ : e ≫ X.variety.structureMap = Parametrized.parameter P sB ≫ sB)
    (h₁ : q ≫ u = ParametrizedContact.evaluationSquare P sB X e hf₁)
    (h₂ : q ≫ u = ParametrizedContact.evaluationSquare P sB X e hf₂)
    (s : AlgebraicSection (MovingPair.leftBundle u).sheaf) :
    ((@pullSection (Parametrized.Square P sB) Y q
        (MovingPair.leftBundle u).sheaf s) ≫
      (compositionPullback q u
        (ParametrizedContact.evaluationSquare P sB X e hf₁) h₁
        (movingPairBundleLeft X.variety X.contact)).hom =
      ParametrizedContact.leftSection P sB X e hf₁) ↔
    ((@pullSection (Parametrized.Square P sB) Y q
        (MovingPair.leftBundle u).sheaf s) ≫
      (compositionPullback q u
        (ParametrizedContact.evaluationSquare P sB X e hf₂) h₂
        (movingPairBundleLeft X.variety X.contact)).hom =
      ParametrizedContact.leftSection P sB X e hf₂) := by
  have hh : hf₁ = hf₂ := Subsingleton.elim _ _
  cases hh
  rfl

/-- The corresponding witness-irrelevance equation for the right section. -/
theorem right_iff (P : ProjectiveLineOverC) {B : Scheme} (sB : B ⟶ ComplexBase)
    {n : ℕ} (X : ContactFanoManifold n) {Y : Scheme}
    (q : Parametrized.Square P sB ⟶ Y)
    (u : Y ⟶ SelfProduct X.variety.structureMap)
    (e : Parametrized.Source P sB ⟶ X.variety.scheme)
    (hf₁ hf₂ : e ≫ X.variety.structureMap = Parametrized.parameter P sB ≫ sB)
    (h₁ : q ≫ u = ParametrizedContact.evaluationSquare P sB X e hf₁)
    (h₂ : q ≫ u = ParametrizedContact.evaluationSquare P sB X e hf₂)
    (s : AlgebraicSection (MovingPair.rightBundle u).sheaf) :
    ((@pullSection (Parametrized.Square P sB) Y q
        (MovingPair.rightBundle u).sheaf s) ≫
      (compositionPullback q u
        (ParametrizedContact.evaluationSquare P sB X e hf₁) h₁
        (movingPairBundleRight X.variety X.contact)).hom =
      ParametrizedContact.rightSection P sB X e hf₁) ↔
    ((@pullSection (Parametrized.Square P sB) Y q
        (MovingPair.rightBundle u).sheaf s) ≫
      (compositionPullback q u
        (ParametrizedContact.evaluationSquare P sB X e hf₂) h₂
        (movingPairBundleRight X.variety X.contact)).hom =
      ParametrizedContact.rightSection P sB X e hf₂) := by
  have hh : hf₁ = hf₂ := Subsingleton.elim _ _
  cases hh
  rfl

end LeBrunSalamon.Construction.FamilyBivectors.FieldWitnessTransport

namespace LeBrunSalamon.Construction.FamilyBivectors

namespace CartesianLiteralAccessors

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

theorem evaluation_eq :
    CartesianParametrization.evaluation (F := F) sT k = k ≫ F.evaluation := by
  rfl

theorem square_eq :
    CartesianParametrization.squareEvaluation Q sT q b hq k hk =
      ParametrizedContact.evaluationSquare P sT X (k ≫ F.evaluation)
        (CartesianParametrization.evaluation_overC Q sT q b hq k hk) := by
  rfl

theorem left_output_module_eq :
    @pullbackModule (Parametrized.Square P sT) (SelfProduct X.variety.structureMap)
      (CartesianParametrization.squareEvaluation Q sT q b hq k hk)
      (movingPairBundleLeft X.variety X.contact) =
    @pullbackModule (Parametrized.Square P sT) (SelfProduct X.variety.structureMap)
      (ParametrizedContact.evaluationSquare P sT X (k ≫ F.evaluation)
        (CartesianParametrization.evaluation_overC Q sT q b hq k hk))
      (movingPairBundleLeft X.variety X.contact) := by
  rfl

theorem right_output_module_eq :
    @pullbackModule (Parametrized.Square P sT) (SelfProduct X.variety.structureMap)
      (CartesianParametrization.squareEvaluation Q sT q b hq k hk)
      (movingPairBundleRight X.variety X.contact) =
    @pullbackModule (Parametrized.Square P sT) (SelfProduct X.variety.structureMap)
      (ParametrizedContact.evaluationSquare P sT X (k ≫ F.evaluation)
        (CartesianParametrization.evaluation_overC Q sT q b hq k hk))
      (movingPairBundleRight X.variety X.contact) := by
  rfl

theorem left_section_heq :
    @HEq
      (AlgebraicSection (@pullbackModule (Parametrized.Square P sT)
        (SelfProduct X.variety.structureMap)
        (CartesianParametrization.squareEvaluation Q sT q b hq k hk)
        (movingPairBundleLeft X.variety X.contact)))
      (ParametrizedContact.leftSection P sT X
        (CartesianParametrization.evaluation (F := F) sT k)
        (CartesianParametrization.evaluation_overC Q sT q b hq k hk))
      (AlgebraicSection (@pullbackModule (Parametrized.Square P sT)
        (SelfProduct X.variety.structureMap)
        (ParametrizedContact.evaluationSquare P sT X (k ≫ F.evaluation)
          (CartesianParametrization.evaluation_overC Q sT q b hq k hk))
        (movingPairBundleLeft X.variety X.contact)))
      (ParametrizedContact.leftSection P sT X (k ≫ F.evaluation)
        (CartesianParametrization.evaluation_overC Q sT q b hq k hk)) := by
  rfl

theorem right_section_heq :
    @HEq
      (AlgebraicSection (@pullbackModule (Parametrized.Square P sT)
        (SelfProduct X.variety.structureMap)
        (CartesianParametrization.squareEvaluation Q sT q b hq k hk)
        (movingPairBundleRight X.variety X.contact)))
      (ParametrizedContact.rightSection P sT X
        (CartesianParametrization.evaluation (F := F) sT k)
        (CartesianParametrization.evaluation_overC Q sT q b hq k hk))
      (AlgebraicSection (@pullbackModule (Parametrized.Square P sT)
        (SelfProduct X.variety.structureMap)
        (ParametrizedContact.evaluationSquare P sT X (k ≫ F.evaluation)
          (CartesianParametrization.evaluation_overC Q sT q b hq k hk))
        (movingPairBundleRight X.variety X.contact)))
      (ParametrizedContact.rightSection P sT X (k ≫ F.evaluation)
        (CartesianParametrization.evaluation_overC Q sT q b hq k hk)) := by
  rfl

variable {Y : Scheme} (u : Y ⟶ SelfProduct X.variety.structureMap)
variable (a : Parametrized.Square P sT ⟶ Y)
variable (h : a ≫ u = CartesianParametrization.squareEvaluation Q sT q b hq k hk)

theorem left_postmap_heq :
    @HEq
      (pullbackModule a (MovingPair.leftBundle u).sheaf ⟶
        pullbackModule (CartesianParametrization.squareEvaluation Q sT q b hq k hk)
          (movingPairBundleLeft X.variety X.contact))
      (compositionPullback a u
        (CartesianParametrization.squareEvaluation Q sT q b hq k hk) h
        (movingPairBundleLeft X.variety X.contact)).hom
      (pullbackModule a (MovingPair.leftBundle u).sheaf ⟶
        pullbackModule
          (ParametrizedContact.evaluationSquare P sT X (k ≫ F.evaluation)
            (CartesianParametrization.evaluation_overC Q sT q b hq k hk))
          (movingPairBundleLeft X.variety X.contact))
      (compositionPullback a u
        (ParametrizedContact.evaluationSquare P sT X (k ≫ F.evaluation)
          (CartesianParametrization.evaluation_overC Q sT q b hq k hk)) h
        (movingPairBundleLeft X.variety X.contact)).hom := by
  rfl

theorem right_postmap_heq :
    @HEq
      (pullbackModule a (MovingPair.rightBundle u).sheaf ⟶
        pullbackModule (CartesianParametrization.squareEvaluation Q sT q b hq k hk)
          (movingPairBundleRight X.variety X.contact))
      (compositionPullback a u
        (CartesianParametrization.squareEvaluation Q sT q b hq k hk) h
        (movingPairBundleRight X.variety X.contact)).hom
      (pullbackModule a (MovingPair.rightBundle u).sheaf ⟶
        pullbackModule
          (ParametrizedContact.evaluationSquare P sT X (k ≫ F.evaluation)
            (CartesianParametrization.evaluation_overC Q sT q b hq k hk))
          (movingPairBundleRight X.variety X.contact))
      (compositionPullback a u
        (ParametrizedContact.evaluationSquare P sT X (k ≫ F.evaluation)
          (CartesianParametrization.evaluation_overC Q sT q b hq k hk)) h
        (movingPairBundleRight X.variety X.contact)).hom := by
  rfl

end CartesianLiteralAccessors


namespace CartesianLiteralEquations

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

variable {Y : Scheme} (u : Y ⟶ SelfProduct X.variety.structureMap)
variable (a : Parametrized.Square P sT ⟶ Y)
variable (h : a ≫ u = CartesianParametrization.squareEvaluation Q sT q b hq k hk)

theorem left_iff (s : AlgebraicSection (MovingPair.leftBundle (X := X) u).sheaf) :
    (@pullSection (Parametrized.Square P sT) Y a (MovingPair.leftBundle (X := X) u).sheaf s ≫
      (compositionPullback a u (CartesianParametrization.squareEvaluation Q sT q b hq k hk) h (movingPairBundleLeft X.variety X.contact)).hom =
      (ParametrizedContact.leftSection P sT X
        (CartesianParametrization.evaluation (F := F) sT k) (CartesianParametrization.evaluation_overC Q sT q b hq k hk))) ↔
    (@pullSection (Parametrized.Square P sT) Y a (MovingPair.leftBundle (X := X) u).sheaf s ≫
      (compositionPullback a u (ParametrizedContact.evaluationSquare P sT X (k ≫ F.evaluation) (CartesianParametrization.evaluation_overC Q sT q b hq k hk)) h (movingPairBundleLeft X.variety X.contact)).hom =
      (ParametrizedContact.leftSection P sT X (k ≫ F.evaluation) (CartesianParametrization.evaluation_overC Q sT q b hq k hk))) := by
  exact FieldPostmapTransport.pull_post_eq_iff
    (T := Parametrized.Square P sT) (T' := Parametrized.Square P sT)
    (Y := Y) (Y' := Y) rfl rfl a a HEq.rfl
    (MovingPair.leftBundle (X := X) u).sheaf (MovingPair.leftBundle (X := X) u).sheaf HEq.rfl
    (pullbackModule (CartesianParametrization.squareEvaluation Q sT q b hq k hk) (movingPairBundleLeft X.variety X.contact))
    (pullbackModule (ParametrizedContact.evaluationSquare P sT X (k ≫ F.evaluation) (CartesianParametrization.evaluation_overC Q sT q b hq k hk)) (movingPairBundleLeft X.variety X.contact))
    (heq_of_eq (CartesianLiteralAccessors.left_output_module_eq Q sT q b hq k hk))
    s s HEq.rfl
    (compositionPullback a u (CartesianParametrization.squareEvaluation Q sT q b hq k hk) h (movingPairBundleLeft X.variety X.contact)).hom
    (compositionPullback a u (ParametrizedContact.evaluationSquare P sT X (k ≫ F.evaluation) (CartesianParametrization.evaluation_overC Q sT q b hq k hk)) h (movingPairBundleLeft X.variety X.contact)).hom
    (CartesianLiteralAccessors.left_postmap_heq Q sT q b hq k hk u a h)
    (ParametrizedContact.leftSection P sT X
        (CartesianParametrization.evaluation (F := F) sT k) (CartesianParametrization.evaluation_overC Q sT q b hq k hk))
    (ParametrizedContact.leftSection P sT X (k ≫ F.evaluation) (CartesianParametrization.evaluation_overC Q sT q b hq k hk))
    (CartesianLiteralAccessors.left_section_heq Q sT q b hq k hk)

theorem right_iff (s : AlgebraicSection (MovingPair.rightBundle (X := X) u).sheaf) :
    (@pullSection (Parametrized.Square P sT) Y a (MovingPair.rightBundle (X := X) u).sheaf s ≫
      (compositionPullback a u (CartesianParametrization.squareEvaluation Q sT q b hq k hk) h (movingPairBundleRight X.variety X.contact)).hom =
      (ParametrizedContact.rightSection P sT X
        (CartesianParametrization.evaluation (F := F) sT k) (CartesianParametrization.evaluation_overC Q sT q b hq k hk))) ↔
    (@pullSection (Parametrized.Square P sT) Y a (MovingPair.rightBundle (X := X) u).sheaf s ≫
      (compositionPullback a u (ParametrizedContact.evaluationSquare P sT X (k ≫ F.evaluation) (CartesianParametrization.evaluation_overC Q sT q b hq k hk)) h (movingPairBundleRight X.variety X.contact)).hom =
      (ParametrizedContact.rightSection P sT X (k ≫ F.evaluation) (CartesianParametrization.evaluation_overC Q sT q b hq k hk))) := by
  exact FieldPostmapTransport.pull_post_eq_iff
    (T := Parametrized.Square P sT) (T' := Parametrized.Square P sT)
    (Y := Y) (Y' := Y) rfl rfl a a HEq.rfl
    (MovingPair.rightBundle (X := X) u).sheaf (MovingPair.rightBundle (X := X) u).sheaf HEq.rfl
    (pullbackModule (CartesianParametrization.squareEvaluation Q sT q b hq k hk) (movingPairBundleRight X.variety X.contact))
    (pullbackModule (ParametrizedContact.evaluationSquare P sT X (k ≫ F.evaluation) (CartesianParametrization.evaluation_overC Q sT q b hq k hk)) (movingPairBundleRight X.variety X.contact))
    (heq_of_eq (CartesianLiteralAccessors.right_output_module_eq Q sT q b hq k hk))
    s s HEq.rfl
    (compositionPullback a u (CartesianParametrization.squareEvaluation Q sT q b hq k hk) h (movingPairBundleRight X.variety X.contact)).hom
    (compositionPullback a u (ParametrizedContact.evaluationSquare P sT X (k ≫ F.evaluation) (CartesianParametrization.evaluation_overC Q sT q b hq k hk)) h (movingPairBundleRight X.variety X.contact)).hom
    (CartesianLiteralAccessors.right_postmap_heq Q sT q b hq k hk u a h)
    (ParametrizedContact.rightSection P sT X
        (CartesianParametrization.evaluation (F := F) sT k) (CartesianParametrization.evaluation_overC Q sT q b hq k hk))
    (ParametrizedContact.rightSection P sT X (k ≫ F.evaluation) (CartesianParametrization.evaluation_overC Q sT q b hq k hk))
    (CartesianLiteralAccessors.right_section_heq Q sT q b hq k hk)

end CartesianLiteralEquations


namespace CartesianFieldEquations

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

variable {Y : Scheme} (u : Y ⟶ SelfProduct X.variety.structureMap)
variable (a : Parametrized.Square P sT ⟶ Y)
variable (h : a ≫ u = CartesianParametrization.squareEvaluation Q sT q b hq k hk)
variable (hf₂ : (k ≫ F.evaluation) ≫ X.variety.structureMap = Parametrized.parameter P sT ≫ sT)
variable (h₂ : a ≫ u = ParametrizedContact.evaluationSquare P sT X (k ≫ F.evaluation) hf₂)

theorem left_iff (s : AlgebraicSection (MovingPair.leftBundle (X := X) u).sheaf) :
    (@pullSection (Parametrized.Square P sT) Y a (MovingPair.leftBundle (X := X) u).sheaf s ≫
      (compositionPullback a u (CartesianParametrization.squareEvaluation Q sT q b hq k hk) h (movingPairBundleLeft X.variety X.contact)).hom =
      (ParametrizedContact.leftSection P sT X
        (CartesianParametrization.evaluation (F := F) sT k) (CartesianParametrization.evaluation_overC Q sT q b hq k hk))) ↔
    (@pullSection (Parametrized.Square P sT) Y a (MovingPair.leftBundle (X := X) u).sheaf s ≫
      (compositionPullback a u (ParametrizedContact.evaluationSquare P sT X (k ≫ F.evaluation) hf₂) h₂ (movingPairBundleLeft X.variety X.contact)).hom =
      (ParametrizedContact.leftSection P sT X (k ≫ F.evaluation) hf₂)) := by
  exact (CartesianLiteralEquations.left_iff Q sT q b hq k hk u a h s).trans
    (FieldWitnessTransport.left_iff P sT X a u (k ≫ F.evaluation)
      (CartesianParametrization.evaluation_overC Q sT q b hq k hk) hf₂ h h₂ s)

theorem right_iff (s : AlgebraicSection (MovingPair.rightBundle (X := X) u).sheaf) :
    (@pullSection (Parametrized.Square P sT) Y a (MovingPair.rightBundle (X := X) u).sheaf s ≫
      (compositionPullback a u (CartesianParametrization.squareEvaluation Q sT q b hq k hk) h (movingPairBundleRight X.variety X.contact)).hom =
      (ParametrizedContact.rightSection P sT X
        (CartesianParametrization.evaluation (F := F) sT k) (CartesianParametrization.evaluation_overC Q sT q b hq k hk))) ↔
    (@pullSection (Parametrized.Square P sT) Y a (MovingPair.rightBundle (X := X) u).sheaf s ≫
      (compositionPullback a u (ParametrizedContact.evaluationSquare P sT X (k ≫ F.evaluation) hf₂) h₂ (movingPairBundleRight X.variety X.contact)).hom =
      (ParametrizedContact.rightSection P sT X (k ≫ F.evaluation) hf₂)) := by
  exact (CartesianLiteralEquations.right_iff Q sT q b hq k hk u a h s).trans
    (FieldWitnessTransport.right_iff P sT X a u (k ≫ F.evaluation)
      (CartesianParametrization.evaluation_overC Q sT q b hq k hk) hf₂ h h₂ s)

end CartesianFieldEquations

end LeBrunSalamon.Construction.FamilyBivectors


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

private theorem field_cover_left
    (q : PointsOver (Spec K) sK Q.cover Q.coverToC)
    (hq : q.val ≫ Q.toSmooth = b) :
    pullSection a (SmoothFamily.smoothLeft Q) ≫
      (compositionPullback a (SmoothFamily.smoothEvaluation (F := F))
        (ParametrizedContact.evaluationSquare P sK X (k ≫ F.evaluation)
          (evaluation_overC sK b hb k hk))
        (square_evaluation sK b hb k hk a ha)
        (movingPairBundleLeft X.variety X.contact)).hom =
      ParametrizedContact.leftSection P sK X (k ≫ F.evaluation)
        (evaluation_overC sK b hb k hk) := by
  exact (CartesianFieldEquations.left_iff Q sK q b hq k hk
    (SmoothFamily.smoothEvaluation (F := F)) a
    (CartesianParametrization.smooth_evaluation Q sK q b hq k hk a ha)
    (evaluation_overC sK b hb k hk)
    (square_evaluation sK b hb k hk a ha) (SmoothFamily.smoothLeft Q)).mp
    (CartesianParametrization.smoothLeft_field Q K sK q b hq k hk a ha)

private theorem field_cover_right
    (q : PointsOver (Spec K) sK Q.cover Q.coverToC)
    (hq : q.val ≫ Q.toSmooth = b) :
    pullSection a (SmoothFamily.smoothRight Q) ≫
      (compositionPullback a (SmoothFamily.smoothEvaluation (F := F))
        (ParametrizedContact.evaluationSquare P sK X (k ≫ F.evaluation)
          (evaluation_overC sK b hb k hk))
        (square_evaluation sK b hb k hk a ha)
        (movingPairBundleRight X.variety X.contact)).hom =
      ParametrizedContact.rightSection P sK X (k ≫ F.evaluation)
        (evaluation_overC sK b hb k hk) := by
  exact (CartesianFieldEquations.right_iff Q sK q b hq k hk
    (SmoothFamily.smoothEvaluation (F := F)) a
    (CartesianParametrization.smooth_evaluation Q sK q b hq k hk a ha)
    (evaluation_overC sK b hb k hk)
    (square_evaluation sK b hb k hk a ha) (SmoothFamily.smoothRight Q)).mp
    (CartesianParametrization.smoothRight_field Q K sK q b hq k hk a ha)

private def field_left_extended_cover_inferred :=
  field_cover_left (Q := Q) (K := Q.parametrizingField K b)
    (sK := extensionToC Q K sK b) (b := extendedBase Q K b)
    (hb := extendedBase_overC Q K sK b hb)
    (k := extendedSource Q K sK b k)
    (hk := extendedSource_isPullback Q K sK b k hk)
    (a := extendedSquare Q K sK b a)
    (ha := extendedSquare_family Q K sK b k hk a ha)
    (q := coverPoint Q K sK b hb) (hq := coverPoint_base Q K sK b hb)

private def field_right_extended_cover_inferred :=
  field_cover_right (Q := Q) (K := Q.parametrizingField K b)
    (sK := extensionToC Q K sK b) (b := extendedBase Q K b)
    (hb := extendedBase_overC Q K sK b hb)
    (k := extendedSource Q K sK b k)
    (hk := extendedSource_isPullback Q K sK b k hk)
    (a := extendedSquare Q K sK b a)
    (ha := extendedSquare_family Q K sK b k hk a ha)
    (q := coverPoint Q K sK b hb) (hq := coverPoint_base Q K sK b hb)

private def field_left_final_inferred :=
  ContactSectionDescent.left Q sK (extensionToC Q K sK b)
    (squareMap Q K sK b) a (extendedSquare Q K sK b a)
    (k ≫ F.evaluation) (extendedSource Q K sK b k ≫ F.evaluation)
    (evaluation_overC sK b hb k hk)
    (evaluation_overC (extensionToC Q K sK b) (extendedBase Q K b)
      (extendedBase_overC Q K sK b hb) (extendedSource Q K sK b k)
      (extendedSource_isPullback Q K sK b k hk))
    rfl
    (square_evaluation sK b hb k hk a ha)
    (square_evaluation (extensionToC Q K sK b) (extendedBase Q K b)
      (extendedBase_overC Q K sK b hb) (extendedSource Q K sK b k)
      (extendedSource_isPullback Q K sK b k hk) (extendedSquare Q K sK b a)
      (extendedSquare_family Q K sK b k hk a ha))
    (evaluationSquare_baseChange Q K sK b hb k hk)
    (squareMap_section_injective Q K sK b
      (MovingPair.leftBundle (ParametrizedContact.evaluationSquare P sK X
        (k ≫ F.evaluation) (evaluation_overC sK b hb k hk))))
    (left_baseChange Q K sK b hb k hk)
    (field_left_extended_cover_inferred (Q := Q) (K := K)
      (sK := sK) (b := b) (hb := hb) (k := k) (hk := hk) (a := a) (ha := ha))

private def field_right_final_inferred :=
  ContactSectionDescent.right Q sK (extensionToC Q K sK b)
    (squareMap Q K sK b) a (extendedSquare Q K sK b a)
    (k ≫ F.evaluation) (extendedSource Q K sK b k ≫ F.evaluation)
    (evaluation_overC sK b hb k hk)
    (evaluation_overC (extensionToC Q K sK b) (extendedBase Q K b)
      (extendedBase_overC Q K sK b hb) (extendedSource Q K sK b k)
      (extendedSource_isPullback Q K sK b k hk))
    rfl
    (square_evaluation sK b hb k hk a ha)
    (square_evaluation (extensionToC Q K sK b) (extendedBase Q K b)
      (extendedBase_overC Q K sK b hb) (extendedSource Q K sK b k)
      (extendedSource_isPullback Q K sK b k hk) (extendedSquare Q K sK b a)
      (extendedSquare_family Q K sK b k hk a ha))
    (evaluationSquare_baseChange Q K sK b hb k hk)
    (squareMap_section_injective Q K sK b
      (MovingPair.rightBundle (ParametrizedContact.evaluationSquare P sK X
        (k ≫ F.evaluation) (evaluation_overC sK b hb k hk))))
    (right_baseChange Q K sK b hb k hk)
    (field_right_extended_cover_inferred (Q := Q) (K := K)
      (sK := sK) (b := b) (hb := hb) (k := k) (hk := hk) (a := a) (ha := ha))

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
  exact field_left_final_inferred (Q := Q) (K := K)
    (sK := sK) (b := b) (hb := hb) (k := k) (hk := hk) (a := a) (ha := ha)

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
  exact field_right_final_inferred (Q := Q) (K := K)
    (sK := sK) (b := b) (hb := hb) (k := k) (hk := hk) (a := a) (ha := ha)

end FieldComparison

end LeBrunSalamon.Construction.FamilyBivectors

end
