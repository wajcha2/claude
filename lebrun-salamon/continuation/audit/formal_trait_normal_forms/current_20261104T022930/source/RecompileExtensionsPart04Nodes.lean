import RecompileExtensionsPart04GluingSections

noncomputable section

set_option autoImplicit false
open Bundle
open scoped Bundle ContDiff ENNReal
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing
open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.Limits

namespace LeBrunSalamon.Construction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseSeven
open LeBrunSalamon.PhaseEight LeBrunSalamon.PhaseTen
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFour LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton

namespace Normalization
open Lines Smoothing

namespace NodeCohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def quotientPullback {Y Z : Scheme} (f : Y ⟶ Z) {M : OModule Z}
    (q : M ⟶ structureModule Z) : pullbackModule f M ⟶ structureModule Y :=
  (Scheme.Modules.pullback f).map q ≫ (unitPullbackIso f).hom

theorem pullback_zero {Y Z : Scheme} (f : Y ⟶ Z) {E M : OModule Z}
    (i : E ⟶ M) (q : M ⟶ structureModule Z) (hz : i ≫ q = 0) :
    (Scheme.Modules.pullback f).map i ≫ quotientPullback f q = 0 := by
  rw [quotientPullback, ← Category.assoc, ← Functor.map_comp, hz,
    Functor.map_zero, zero_comp]

/-- The existing flat-quotient theorem applies because the arbitrary
middle sheaf is proved locally free before this lemma is used. -/
theorem pullback_shortExact {Y Z : Scheme} (f : Y ⟶ Z) {a b : ℕ}
    (E : AlgebraicVectorBundle Z a) (M : AlgebraicVectorBundle Z b)
    (i : E.sheaf ⟶ M.sheaf) (q : M.sheaf ⟶ structureModule Z)
    (hz : i ≫ q = 0) (hex : (ShortComplex.mk i q hz).ShortExact) :
    (ShortComplex.mk ((Scheme.Modules.pullback f).map i) (quotientPullback f q)
      (pullback_zero f i q hz)).ShortExact := by
  let S := (ShortComplex.mk i q hz).map (Scheme.Modules.pullback f)
  let T := ShortComplex.mk ((Scheme.Modules.pullback f).map i) (quotientPullback f q)
    (pullback_zero f i q hz)
  have hS : S.ShortExact := StandardInputs.BundleGeometry.vectorBundle_pullback_shortExact
    f E M (trivialLine Z) i q hz hex
  let e : S ≅ T := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (unitPullbackIso f)
    (by
      change 𝟙 (pullbackModule f E.sheaf) ≫ (Scheme.Modules.pullback f).map i =
        (Scheme.Modules.pullback f).map i ≫ 𝟙 (pullbackModule f M.sheaf)
      exact (Category.id_comp _).trans (Category.comp_id _).symm)
    (by
      change 𝟙 (pullbackModule f M.sheaf) ≫ quotientPullback f q = quotientPullback f q
      exact Category.id_comp _)
  exact ShortComplex.shortExact_of_iso e hS

theorem compositionPullback_unit {T Y Z : Scheme}
    (g : T ⟶ Y) (f : Y ⟶ Z) (k : T ⟶ Z) (hk : g ≫ f = k) :
    (compositionPullback g f k hk (structureModule Z)).hom ≫ (unitPullbackIso k).hom =
      (Scheme.Modules.pullback g).map (unitPullbackIso f).hom ≫ (unitPullbackIso g).hom := by
  subst k
  simpa only [compositionPullback, Iso.trans_hom, Iso.app_hom, eqToIso.hom,
    eqToHom_refl, Category.comp_id, unitPullbackIso, asIso_hom] using
    unitPullbackMap_comp_hom g f

theorem pullSection_identity_unit {Y Z : Scheme} (f : Y ⟶ Z) :
    pullSection f (𝟙 (structureModule Z)) ≫ (unitPullbackIso f).hom =
      𝟙 (structureModule Y) := by
  change ((unitPullbackIso f).inv ≫
    (Scheme.Modules.pullback f).map (𝟙 (structureModule Z))) ≫ (unitPullbackIso f).hom = _
  have h := congrArg (fun k : pullbackModule f (structureModule Z) ⟶
      pullbackModule f (structureModule Z) =>
    ((unitPullbackIso f).inv ≫ k) ≫ (unitPullbackIso f).hom)
    ((Scheme.Modules.pullback f).map_id (structureModule Z))
  exact h.trans ((congrArg (fun k : structureModule Y ⟶
      pullbackModule f (structureModule Z) => k ≫ (unitPullbackIso f).hom)
    (Category.comp_id (unitPullbackIso f).inv)).trans (Iso.inv_hom_id (unitPullbackIso f)))

/-- A section lifting one remains a lift of one after the actual normalized
pullback to a specified composite, including its fixed base-map equality. -/
theorem lift_preserved {T Y Z : Scheme} (g : T ⟶ Y) (f : Y ⟶ Z)
    (k : T ⟶ Z) (hk : g ≫ f = k) {M : OModule Z}
    (q : M ⟶ structureModule Z) (a : AlgebraicSection (pullbackModule f M))
    (ha : a ≫ quotientPullback f q = 𝟙 (structureModule Y)) :
    (pullSection g a ≫ (compositionPullback g f k hk M).hom) ≫
      quotientPullback k q = 𝟙 (structureModule T) := by
  calc
    _ = pullSection g a ≫
        ((compositionPullback g f k hk M).hom ≫ (Scheme.Modules.pullback k).map q) ≫
          (unitPullbackIso k).hom := by simp only [quotientPullback, Category.assoc]
    _ = pullSection g a ≫
        (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback f).map q) ≫
          (compositionPullback g f k hk (structureModule Z)).hom ≫
            (unitPullbackIso k).hom := by
      rw [← BundleGluing.compositionPullback_naturality g f k hk q]
      simp only [Category.assoc]
    _ = pullSection g a ≫
        (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback f).map q) ≫
          (Scheme.Modules.pullback g).map (unitPullbackIso f).hom ≫
            (unitPullbackIso g).hom := by rw [compositionPullback_unit]
    _ = pullSection g (a ≫ quotientPullback f q) ≫ (unitPullbackIso g).hom := by
      simp only [pullSection_naturality, quotientPullback, Functor.map_comp, Category.assoc]
    _ = pullSection g (𝟙 (structureModule Y)) ≫ (unitPullbackIso g).hom := by rw [ha]
    _ = 𝟙 (structureModule T) := pullSection_identity_unit g

theorem leftAtNode_surjective {F : StandardSource} (m : SourceMarks F) {r : ℕ}
    (E : AlgebraicVectorBundle (CentralFiber F) r)
    (hE : IsGloballyGenerated (pullbackModule (leftBranch m) E.sheaf)) :
    Function.Surjective (BundleGluing.leftAtNode m E.sheaf) := by
  intro v
  let e := compositionPullback marking.map (leftBranch m) (node m) rfl E.sheaf
  let w := v ≫ e.inv
  obtain ⟨a, ha⟩ := GeneratedFiberEvaluation.evaluateSection_surjective_of_globallyGenerated
    P.structureMap (pullbackModule (leftBranch m) E.sheaf)
    marking.map marking.overC hE (sectionValue w)
  have hs : pullSection marking.map (sectionFromValue a) = w := by
    apply (sectionValue_bijective _).injective
    exact ha
  refine ⟨sectionFromValue a, ?_⟩
  rw [BundleGluing.leftAtNode, hs]
  change (v ≫ e.inv) ≫ e.hom = v
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The normalized quotient comparison on an arbitrary restriction. This
proof is shared without unfolding a particular extension or glued section. -/
theorem of_branches_quotient_restriction {Y Z : Scheme} (f : Y ⟶ Z)
    {M : OModule Z} (q : M ⟶ structureModule Z) (s : AlgebraicSection M)
    (a : AlgebraicSection (pullbackModule f M)) (ha : pullSection f s = a)
    (hq : a ≫ quotientPullback f q = 𝟙 (structureModule Y)) :
    pullSection f (s ≫ q) = pullSection f (𝟙 (structureModule Z)) := by
  apply (cancel_mono (unitPullbackIso f).hom).mp
  calc
    pullSection f (s ≫ q) ≫ (unitPullbackIso f).hom =
        (pullSection f s ≫ (Scheme.Modules.pullback f).map q) ≫
          (unitPullbackIso f).hom :=
      congrArg (fun b : AlgebraicSection (pullbackModule f (structureModule Z)) =>
        b ≫ (unitPullbackIso f).hom) (pullSection_naturality f s q)
    _ = pullSection f s ≫ quotientPullback f q :=
      Category.assoc (pullSection f s) ((Scheme.Modules.pullback f).map q)
        (unitPullbackIso f).hom
    _ = a ≫ quotientPullback f q :=
      congrArg (fun b : AlgebraicSection (pullbackModule f M) => b ≫ quotientPullback f q) ha
    _ = 𝟙 (structureModule Y) := hq
    _ = pullSection f (𝟙 (structureModule Z)) ≫ (unitPullbackIso f).hom :=
      (pullSection_identity_unit f).symm

namespace NodeCorrectionProof

/-- Subtraction commutes with the prescribed normalized pullback. -/
private theorem normalized_sub {N A Y : Scheme}
    (p : N ⟶ A) (f : A ⟶ Y) (z : N ⟶ Y) (h : p ≫ f = z)
    (M : OModule Y) (a b : AlgebraicSection (pullbackModule f M)) :
    pullSection p (a - b) ≫ (compositionPullback p f z h M).hom =
      (pullSection p a ≫ (compositionPullback p f z h M).hom) -
        (pullSection p b ≫ (compositionPullback p f z h M).hom) := by
  exact (congrArg (fun c : AlgebraicSection (pullbackModule p (pullbackModule f M)) =>
      c ≫ (compositionPullback p f z h M).hom)
    (BundleGluing.pullSection_sub p a b)).trans
      (Preadditive.sub_comp (pullSection p a) (pullSection p b)
        (compositionPullback p f z h M).hom)

/-- The actual sheaf map commutes with the prescribed normalized pullback. -/
private theorem normalized_map {N A Y : Scheme}
    (p : N ⟶ A) (f : A ⟶ Y) (z : N ⟶ Y) (h : p ≫ f = z)
    {E M : OModule Y} (i : E ⟶ M)
    (a : AlgebraicSection (pullbackModule f E)) :
    pullSection p (a ≫ (Scheme.Modules.pullback f).map i) ≫
        (compositionPullback p f z h M).hom =
      (pullSection p a ≫ (compositionPullback p f z h E).hom) ≫
        (Scheme.Modules.pullback z).map i := by
  calc
    _ = (pullSection p a ≫
          (Scheme.Modules.pullback p).map ((Scheme.Modules.pullback f).map i)) ≫
            (compositionPullback p f z h M).hom :=
      congrArg (fun b : AlgebraicSection (pullbackModule p (pullbackModule f M)) =>
        b ≫ (compositionPullback p f z h M).hom)
        (pullSection_naturality p a ((Scheme.Modules.pullback f).map i))
    _ = pullSection p a ≫
          ((Scheme.Modules.pullback p).map ((Scheme.Modules.pullback f).map i) ≫
            (compositionPullback p f z h M).hom) :=
      Category.assoc _ _ _
    _ = pullSection p a ≫
          ((compositionPullback p f z h E).hom ≫ (Scheme.Modules.pullback z).map i) :=
      congrArg (fun b : pullbackModule p (pullbackModule f E) ⟶ pullbackModule z M =>
        pullSection p a ≫ b)
        (BundleGluing.compositionPullback_naturality p f z h i)
    _ = _ := (Category.assoc _ _ _).symm

/-- Correct two actual branch lifts on abstract schemes. In particular,
the kernel lift and its correction are checked without unfolding a central fibre. -/
private theorem corrected_left {Y A B N : Scheme}
    (fL : A ⟶ Y) (fR : B ⟶ Y) (pL : N ⟶ A) (pR : N ⟶ B)
    (z : N ⟶ Y) (hLnode : pL ≫ fL = z) (hRnode : pR ≫ fR = z)
    {E M : OModule Y} (i : E ⟶ M) (q : M ⟶ structureModule Y)
    (hz : i ≫ q = 0)
    (hN : (ShortComplex.mk ((Scheme.Modules.pullback z).map i)
      (quotientPullback z q) (pullback_zero z i q hz)).ShortExact)
    (hnode : Function.Surjective (fun a : AlgebraicSection (pullbackModule fL E) =>
      pullSection pL a ≫ (compositionPullback pL fL z hLnode E).hom))
    (sL : AlgebraicSection (pullbackModule fL M))
    (sR : AlgebraicSection (pullbackModule fR M))
    (hsL : sL ≫ quotientPullback fL q = 𝟙 (structureModule A))
    (hsR : sR ≫ quotientPullback fR q = 𝟙 (structureModule B)) :
    ∃ v : AlgebraicSection (pullbackModule fL E),
      (sL - v ≫ (Scheme.Modules.pullback fL).map i) ≫
          quotientPullback fL q = 𝟙 (structureModule A) ∧
        pullSection pL (sL - v ≫ (Scheme.Modules.pullback fL).map i) ≫
            (compositionPullback pL fL z hLnode M).hom =
          pullSection pR sR ≫ (compositionPullback pR fR z hRnode M).hom := by
  let iL : pullbackModule fL E ⟶ pullbackModule fL M :=
    (Scheme.Modules.pullback fL).map i
  let iN : pullbackModule z E ⟶ pullbackModule z M :=
    (Scheme.Modules.pullback z).map i
  let qL : pullbackModule fL M ⟶ structureModule A := quotientPullback fL q
  let qN : pullbackModule z M ⟶ structureModule N := quotientPullback z q
  have hzL : iL ≫ qL = 0 := pullback_zero fL i q hz
  let bL : AlgebraicSection (pullbackModule z M) :=
    pullSection pL sL ≫ (compositionPullback pL fL z hLnode M).hom
  let bR : AlgebraicSection (pullbackModule z M) :=
    pullSection pR sR ≫ (compositionPullback pR fR z hRnode M).hom
  have hbL : bL ≫ qN = 𝟙 (structureModule N) :=
    lift_preserved pL fL z hLnode q sL hsL
  have hbR : bR ≫ qN = 𝟙 (structureModule N) :=
    lift_preserved pR fR z hRnode q sR hsR
  have hb : (bL - bR) ≫ qN = 0 :=
    (Preadditive.sub_comp bL bR qN).trans
      ((congrArg₂ (fun a b : AlgebraicSection (structureModule N) => a - b)
        hbL hbR).trans (sub_self (𝟙 (structureModule N))))
  letI : Mono iN := hN.mono_f
  let c : AlgebraicSection (pullbackModule z E) :=
    hN.exact.lift (bL - bR) hb
  have hc : c ≫ iN = bL - bR := hN.exact.lift_f (bL - bR) hb
  obtain ⟨v, hv⟩ := hnode c
  let sL' : AlgebraicSection (pullbackModule fL M) := sL - v ≫ iL
  have hcorrection : (v ≫ iL) ≫ qL = 0 :=
    (Category.assoc v iL qL).trans
      ((congrArg (fun a : pullbackModule fL E ⟶ structureModule A => v ≫ a)
        hzL).trans comp_zero)
  have hsL' : sL' ≫ qL = 𝟙 (structureModule A) :=
    (Preadditive.sub_comp sL (v ≫ iL) qL).trans
      ((congrArg₂ (fun a b : AlgebraicSection (structureModule A) => a - b)
        hsL hcorrection).trans (sub_zero (𝟙 (structureModule A))))
  have hcorrection_node :
      pullSection pL (v ≫ iL) ≫ (compositionPullback pL fL z hLnode M).hom =
        bL - bR :=
    (normalized_map pL fL z hLnode i v).trans
      ((congrArg (fun a : AlgebraicSection (pullbackModule z E) => a ≫ iN) hv).trans hc)
  have hmatch :
      pullSection pL sL' ≫ (compositionPullback pL fL z hLnode M).hom = bR :=
    (normalized_sub pL fL z hLnode M sL (v ≫ iL)).trans
      ((congrArg (fun a : AlgebraicSection (pullbackModule z M) => bL - a)
        hcorrection_node).trans (sub_sub_self bL bR))
  exact ⟨v, hsL', hmatch⟩

/-- The concrete node maps are compared with the named generic operation.
Its normalized expression is unfolded only over abstract schemes here. -/
private theorem corrected_left_named {Y A B N : Scheme}
    (fL : A ⟶ Y) (fR : B ⟶ Y) (pL : N ⟶ A) (pR : N ⟶ B)
    (z : N ⟶ Y) (hLnode : pL ≫ fL = z) (hRnode : pR ≫ fR = z)
    (atL : ∀ E : OModule Y, AlgebraicSection (pullbackModule fL E) →
      AlgebraicSection (pullbackModule z E))
    (atR : ∀ E : OModule Y, AlgebraicSection (pullbackModule fR E) →
      AlgebraicSection (pullbackModule z E))
    (hatL : ∀ (E : OModule Y) (s : AlgebraicSection (pullbackModule fL E)),
      atL E s = BundleGluing.nodeEval fL pL z hLnode E s)
    (hatR : ∀ (E : OModule Y) (s : AlgebraicSection (pullbackModule fR E)),
      atR E s = BundleGluing.nodeEval fR pR z hRnode E s)
    {E M : OModule Y} (i : E ⟶ M) (q : M ⟶ structureModule Y)
    (hz : i ≫ q = 0)
    (hN : (ShortComplex.mk ((Scheme.Modules.pullback z).map i)
      (quotientPullback z q) (pullback_zero z i q hz)).ShortExact)
    (hnode : Function.Surjective (atL E))
    (sL : AlgebraicSection (pullbackModule fL M))
    (sR : AlgebraicSection (pullbackModule fR M))
    (hsL : sL ≫ quotientPullback fL q = 𝟙 (structureModule A))
    (hsR : sR ≫ quotientPullback fR q = 𝟙 (structureModule B)) :
    ∃ v : AlgebraicSection (pullbackModule fL E),
      (sL - v ≫ (Scheme.Modules.pullback fL).map i) ≫
          quotientPullback fL q = 𝟙 (structureModule A) ∧
        atL M (sL - v ≫ (Scheme.Modules.pullback fL).map i) = atR M sR := by
  simp only [BundleGluing.nodeEval] at hatL hatR
  have hnode' : Function.Surjective
      (fun a : AlgebraicSection (pullbackModule fL E) =>
        pullSection pL a ≫ (compositionPullback pL fL z hLnode E).hom) := by
    intro c
    obtain ⟨a, ha⟩ := hnode c
    exact ⟨a, (hatL E a).symm.trans ha⟩
  obtain ⟨v, hquot, hmatch⟩ := corrected_left
    fL fR pL pR z hLnode hRnode i q hz hN hnode' sL sR hsL hsR
  exact ⟨v, hquot,
    (hatL M (sL - v ≫ (Scheme.Modules.pullback fL).map i)).trans
      (hmatch.trans (hatR M sR).symm)⟩


end NodeCorrectionProof


/-- Correct the actual left splitting by the lift of its difference from
the right splitting at the node. The middle sheaf and node exactness are
abstract parameters, so their construction is not duplicated in this proof. -/
theorem of_branches_corrected_left {F : StandardSource} (m : SourceMarks F)
    {E M : OModule (CentralFiber F)} (i : E ⟶ M)
    (q : M ⟶ structureModule (CentralFiber F)) (hz : i ≫ q = 0)
    (hN : (ShortComplex.mk ((Scheme.Modules.pullback (node m)).map i)
      (quotientPullback (node m) q) (pullback_zero (node m) i q hz)).ShortExact)
    (hnode : Function.Surjective (BundleGluing.leftAtNode m E))
    (sL : AlgebraicSection (pullbackModule (leftBranch m) M))
    (sR : AlgebraicSection (pullbackModule (rightBranch m) M))
    (hsL : sL ≫ quotientPullback (leftBranch m) q = 𝟙 (structureModule ProjectiveLine))
    (hsR : sR ≫ quotientPullback (rightBranch m) q = 𝟙 (structureModule ProjectiveLine)) :
    ∃ v : AlgebraicSection (pullbackModule (leftBranch m) E),
      (sL - v ≫ (Scheme.Modules.pullback (leftBranch m)).map i) ≫
          quotientPullback (leftBranch m) q = 𝟙 (structureModule ProjectiveLine) ∧
        BundleGluing.leftAtNode m M
            (sL - v ≫ (Scheme.Modules.pullback (leftBranch m)).map i) =
          BundleGluing.rightAtNode m M sR := by
  exact @NodeCorrectionProof.corrected_left_named
    (CentralFiber F) ProjectiveLine ProjectiveLine ComplexBase
    (leftBranch m) (rightBranch m) marking.map marking.map
    (node m) rfl (BundleGluing.rightBranch_to_node m)
    (BundleGluing.leftAtNode m) (BundleGluing.rightAtNode m)
    (BundleGluing.leftAtNode_explicit m) (BundleGluing.rightAtNode_explicit m)
    E M i q hz hN hnode sL sR hsL hsR

/-- Glue the specified branch lifts and prove the resulting section still
lifts one, using the actual branch pullbacks and unit comparisons. -/
theorem of_branches_glued_lift {F : StandardSource} (m : SourceMarks F) {r : ℕ}
    (M : AlgebraicVectorBundle (CentralFiber F) r)
    (q : M.sheaf ⟶ structureModule (CentralFiber F))
    (sL : AlgebraicSection (pullbackModule (leftBranch m) M.sheaf))
    (sR : AlgebraicSection (pullbackModule (rightBranch m) M.sheaf))
    (hmatch : BundleGluing.leftAtNode m M.sheaf sL = BundleGluing.rightAtNode m M.sheaf sR)
    (hsL : sL ≫ quotientPullback (leftBranch m) q = 𝟙 (structureModule ProjectiveLine))
    (hsR : sR ≫ quotientPullback (rightBranch m) q = 𝟙 (structureModule ProjectiveLine)) :
    ∃ s : AlgebraicSection M.sheaf, s ≫ q = 𝟙 (structureModule (CentralFiber F)) := by
  obtain ⟨s, hsl, hsr⟩ : ∃ s : AlgebraicSection M.sheaf,
      pullSection (leftBranch m) s = sL ∧ pullSection (rightBranch m) s = sR :=
    BundleGluing.glue_sections m M sL sR hmatch
  exact ⟨s, BundleGluing.sections_ext m (trivialLine (CentralFiber F))
    (of_branches_quotient_restriction (leftBranch m) q s sL hsl hsL)
    (of_branches_quotient_restriction (rightBranch m) q s sR hsr hsR)⟩


/-- Split an arbitrary original extension on the branches, correct one
splitting by a section of its kernel, and glue the resulting middle-bundle
sections. The middle sheaf's finite local freeness is derived, not assumed. -/
theorem of_branches {F : StandardSource} (m : SourceMarks F) {r : ℕ}
    (E : AlgebraicVectorBundle (CentralFiber F) r)
    (hL : HasVanishingFirstCohomology (pullbackModule (leftBranch m) E.sheaf))
    (hR : HasVanishingFirstCohomology (pullbackModule (rightBranch m) E.sheaf))
    (hnode : Function.Surjective (BundleGluing.leftAtNode m E.sheaf)) :
    HasVanishingFirstCohomology E.sheaf := by
  intro M i q hz hex
  let M' : AlgebraicVectorBundle (CentralFiber F) (r + 1) :=
    ⟨M, LocalExtensionSplitting.middle_locallyFree E.locallyFree i q hz hex⟩
  let iL : pullbackModule (leftBranch m) E.sheaf ⟶ pullbackModule (leftBranch m) M :=
    (Scheme.Modules.pullback (leftBranch m)).map i
  let iR : pullbackModule (rightBranch m) E.sheaf ⟶ pullbackModule (rightBranch m) M :=
    (Scheme.Modules.pullback (rightBranch m)).map i
  let qL : pullbackModule (leftBranch m) M ⟶ structureModule ProjectiveLine :=
    quotientPullback (leftBranch m) q
  let qR : pullbackModule (rightBranch m) M ⟶ structureModule ProjectiveLine :=
    quotientPullback (rightBranch m) q
  have hzL : iL ≫ qL = 0 := pullback_zero (leftBranch m) i q hz
  have hzR : iR ≫ qR = 0 := pullback_zero (rightBranch m) i q hz
  have hEL : (ShortComplex.mk iL qL hzL).ShortExact :=
    pullback_shortExact (leftBranch m) E M' i q hz hex
  have hER : (ShortComplex.mk iR qR hzR).ShortExact :=
    pullback_shortExact (rightBranch m) E M' i q hz hex
  obtain ⟨sL, hsL⟩ : ∃ sL : AlgebraicSection (pullbackModule (leftBranch m) M),
      sL ≫ qL = 𝟙 (structureModule ProjectiveLine) :=
    hL (pullbackModule (leftBranch m) M) iL qL hzL hEL
  obtain ⟨sR, hsR⟩ : ∃ sR : AlgebraicSection (pullbackModule (rightBranch m) M),
      sR ≫ qR = 𝟙 (structureModule ProjectiveLine) :=
    hR (pullbackModule (rightBranch m) M) iR qR hzR hER
  have hN : (ShortComplex.mk ((Scheme.Modules.pullback (node m)).map i)
      (quotientPullback (node m) q) (pullback_zero (node m) i q hz)).ShortExact :=
    pullback_shortExact (node m) E M' i q hz hex
  obtain ⟨v, hv, hmatch⟩ :=
    of_branches_corrected_left m i q hz hN hnode sL sR hsL hsR
  let sL' : AlgebraicSection (pullbackModule (leftBranch m) M) := sL - v ≫ iL
  exact of_branches_glued_lift m M' q sL' sR hmatch hv hsR


end NodeCohomology

end Normalization
end LeBrunSalamon.Construction
end
