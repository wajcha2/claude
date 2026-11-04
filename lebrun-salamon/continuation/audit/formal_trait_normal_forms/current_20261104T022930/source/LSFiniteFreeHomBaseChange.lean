import RecompileExtensionsPart01

/-!
Canonical internal-Hom base change, derived from the finite free dual-tensor
identification and the already normalized dual base-change comparison.

The sole proposed new published input is EGA I, chapitre 0, (5.4.2), printed
p.49: Eᵛ ⊗ F → Hom(E,F), λ⊗u ↦ (e ↦ λ(e)u), is an isomorphism for finite
locally free E and arbitrary F.  The map below is explicitly normalized by
that formula.  Hom base change itself is proved, not admitted under a new name.
Compiler receipts record the exact source and the scope of dependency verification.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton
open LeBrunSalamon.Refinement
open LeBrunSalamon.Skeleton.PullbackPairProof
open LeBrunSalamon.Refinement.TensorPullbackComparisonProof
open LeBrunSalamon.PhaseTwentyEight.ExternalExchangeCoherenceProof

namespace LeBrunSalamon.FiniteFreeHomBaseChange

def evaluationPair {X : Scheme.{0}} (E F : OModule X) :
    SheafBilinearMap (internalHomSheaf E F) E F :=
  (tensorPresentation (internalHomSheaf E F) E).pair.postcompose
    (internalHomPresentation E F).evaluate

theorem constructionIso_evaluation {X : Scheme.{0}} (E F : OModule X)
    (U : X.Opens) (φ : SectionsOn (internalHomSheaf E F) U) (e : SectionsOn E U) :
    HomConstruction.evaluationAt E F U ((internalHomConstructionIso E F).hom.app U φ) e =
      (evaluationPair E F).apply U φ e := by
  have hp := congrArg (fun b : SheafBilinearMap (HomConstruction.object E F) E F =>
    b.apply U ((internalHomConstructionIso E F).hom.app U φ) e)
      (tensorLift_pair (HomConstruction.evaluatePair E F))
  have h := congrArg (fun g : tensorSheaf (internalHomSheaf E F) E ⟶ F =>
    g.app U ((tensorPresentation (internalHomSheaf E F) E).pair.apply U φ e))
      (internalHomConstructionIso_evaluate E F)
  change (HomConstruction.presentation E F).evaluate.app U
    ((tensorMap (internalHomConstructionIso E F).hom (𝟙 E)).app U
      ((tensorPresentation (internalHomSheaf E F) E).pair.apply U φ e)) = _ at h
  rw [tensorMap_apply] at h
  exact hp.symm.trans h

theorem curry_evaluation {X : Scheme.{0}} {Z E F : OModule X}
    (a : tensorSheaf Z E ⟶ F) (U : X.Opens)
    (z : SectionsOn Z U) (e : SectionsOn E U) :
    (evaluationPair E F).apply U ((currySheaf a).app U z) e =
      a.app U ((tensorPresentation Z E).pair.apply U z e) := by
  have h := congrArg (fun g : tensorSheaf Z E ⟶ F =>
    g.app U ((tensorPresentation Z E).pair.apply U z e)) (currySheaf_evaluate a)
  change (internalHomPresentation E F).evaluate.app U
    ((tensorMap (currySheaf a) (𝟙 E)).app U
      ((tensorPresentation Z E).pair.apply U z e)) = _ at h
  rw [tensorMap_apply] at h
  exact h

theorem associativityIso_inv_pair {X : Scheme.{0}} (E F G : OModule X) (U : X.Opens)
    (e : SectionsOn E U) (f : SectionsOn F U) (g : SectionsOn G U) :
    (SheafTensor.associativityIso E F G).inv.app U
      ((tensorPresentation E (tensorSheaf F G)).pair.apply U e
        ((tensorPresentation F G).pair.apply U f g)) =
      (tensorPresentation (tensorSheaf E F) G).pair.apply U
        ((tensorPresentation E F).pair.apply U e f) g := by
  rw [← SheafTensor.associativityIso_hom_pair]
  exact congrArg (fun a => a.app U
    ((tensorPresentation (tensorSheaf E F) G).pair.apply U
      ((tensorPresentation E F).pair.apply U e f) g))
        (SheafTensor.associativityIso E F G).hom_inv_id

def dualTensorContract {X : Scheme.{0}} (E F : OModule X) :
    tensorSheaf (tensorSheaf (dualSheaf E) F) E ⟶ F :=
  (SheafTensor.associativityIso (dualSheaf E) F E).hom ≫
    tensorMap (𝟙 (dualSheaf E)) (TensorConstruction.commIso F E).hom ≫
      (SheafTensor.associativityIso (dualSheaf E) E F).inv ≫
        tensorMap (internalHomPresentation E (structureModule X)).evaluate (𝟙 F) ≫
          (TensorConstruction.leftUnitIso F).hom

/-- The canonical map of EGA 0(5.4.2), retaining the chosen internal Hom. -/
def dualTensorHomMap {X : Scheme.{0}} (E F : OModule X) :
    tensorSheaf (dualSheaf E) F ⟶ internalHomSheaf E F :=
  currySheaf (dualTensorContract E F)

/-- Keep the structure-sheaf coefficient typed as a scalar throughout the
tensor calculation. This is the original dual evaluation, with no transport. -/
def dualScalar {X : Scheme.{0}} (E : OModule X) (U : X.Opens)
    (ell : SectionsOn (dualSheaf E) U) (e : SectionsOn E U) : RingSections X U :=
  (dualEvaluation E).apply U ell e

theorem commIso_hom_pair {X : Scheme.{0}} (E F : OModule X) (U : X.Opens)
    (e : SectionsOn E U) (f : SectionsOn F U) :
    (TensorConstruction.commIso E F).hom.app U
      ((tensorPresentation E F).pair.apply U e f) =
      (tensorPresentation F E).pair.apply U f e :=
  TensorConstruction.commHom_pair E F U e f

theorem leftUnitIso_hom_pair {X : Scheme.{0}} (E : OModule X) (U : X.Opens)
    (a : RingSections X U) (e : SectionsOn E U) :
    (TensorConstruction.leftUnitIso E).hom.app U
      ((tensorPresentation (structureModule X) E).pair.apply U a e) = a • e :=
  TensorConstruction.leftUnitHom_pair E U a e

theorem dualTensorHomMap_evaluation {X : Scheme.{0}} (E F : OModule X) (U : X.Opens)
    (ell : SectionsOn (dualSheaf E) U) (u : SectionsOn F U) (e : SectionsOn E U) :
    (evaluationPair E F).apply U
      ((dualTensorHomMap E F).app U ((tensorPresentation (dualSheaf E) F).pair.apply U ell u)) e =
        dualScalar E U ell e • u := by
  rw [dualTensorHomMap, curry_evaluation]
  change (TensorConstruction.leftUnitIso F).hom.app U
    ((tensorMap (internalHomPresentation E (structureModule X)).evaluate (𝟙 F)).app U
      ((SheafTensor.associativityIso (dualSheaf E) E F).inv.app U
        ((tensorMap (𝟙 (dualSheaf E)) (TensorConstruction.commIso F E).hom).app U
          ((SheafTensor.associativityIso (dualSheaf E) F E).hom.app U
            ((tensorPresentation (tensorSheaf (dualSheaf E) F) E).pair.apply U
              ((tensorPresentation (dualSheaf E) F).pair.apply U ell u) e))))) = _
  rw [SheafTensor.associativityIso_hom_pair, tensorMap_apply,
    commIso_hom_pair, associativityIso_inv_pair, tensorMap_apply]
  change (TensorConstruction.leftUnitIso F).hom.app U
    ((tensorPresentation (structureModule X) F).pair.apply U (dualScalar E U ell e) u) = _
  exact leftUnitIso_hom_pair F U (dualScalar E U ell e) u

theorem dualScalar_baseChange_pullLocalSection {X Y : Scheme.{0}} (f : X ⟶ Y)
    (E : OModule Y) (U : Y.Opens) (ell : SectionsOn (dualSheaf E) U)
    (e : SectionsOn E U) :
    dualScalar (pullbackModule f E) (f ⁻¹ᵁ U)
      ((dualBaseChange f E).app (f ⁻¹ᵁ U) (pullLocalSection f (dualSheaf E) U ell))
      (pullLocalSection f E U e) = f.app U (dualScalar E U ell e) :=
  ContactDerivativeIsoProof.dualBaseChange_pullLocalSection f E U ell e

/-- EGA I (1960), chapitre 0, (5.4.2), printed p.49; finite rank is the
standing convention immediately preceding that paragraph.  The preceding
evaluation formula is exactly the canonical map displayed in the source.
https://numdam.org/item/PMIHES_1960__4__5_0/ -/
theorem _root_.LeBrunSalamon.PublishedInputs.FiniteFreeHom.dualTensorHomMap_isIso
    {X : Scheme.{0}} {E : OModule X} {r : ℕ}
    (hE : IsLocallyFreeOfRank E r) (F : OModule X) :
    IsIso (LeBrunSalamon.FiniteFreeHomBaseChange.dualTensorHomMap E F) := by
  sorry

def homComparison {X Y : Scheme.{0}} (f : X ⟶ Y) (E F : OModule Y) :
    pullbackModule f (internalHomSheaf E F) ⟶
      internalHomSheaf (pullbackModule f E) (pullbackModule f F) :=
  currySheaf (tensorLift (pullbackPair f (evaluationPair E F)))

theorem homComparison_evaluation {X Y : Scheme.{0}} (f : X ⟶ Y)
    (E F : OModule Y) (U : Y.Opens)
    (φ : SectionsOn (internalHomSheaf E F) U) (e : SectionsOn E U) :
    (evaluationPair (pullbackModule f E) (pullbackModule f F)).apply (f ⁻¹ᵁ U)
      ((homComparison f E F).app (f ⁻¹ᵁ U)
        (pullLocalSection f (internalHomSheaf E F) U φ))
      (pullLocalSection f E U e) =
      pullLocalSection f F U ((evaluationPair E F).apply U φ e) := by
  rw [homComparison, curry_evaluation]
  have h := congrArg (fun b : SheafBilinearMap
      (pullbackModule f (internalHomSheaf E F)) (pullbackModule f E) (pullbackModule f F) =>
    b.apply (f ⁻¹ᵁ U) (pullLocalSection f (internalHomSheaf E F) U φ)
      (pullLocalSection f E U e)) (tensorLift_pair (pullbackPair f (evaluationPair E F)))
  exact h.trans (pullbackPair_normalized f (evaluationPair E F) U φ e)

/-- A local section of the chosen Hom with pulled-back source is determined
by evaluation on pulled local sections over every smaller inverse-image open. -/
theorem pullbackHomSection_ext {X Y : Scheme.{0}} (f : X ⟶ Y) (E : OModule Y)
    (H : OModule X) (U : Y.Opens)
    (φ ψ : SectionsOn (internalHomSheaf (pullbackModule f E) H) (f ⁻¹ᵁ U))
    (h : ∀ (W : Over U) (e : SectionsOn E W.left),
      (evaluationPair (pullbackModule f E) H).apply (f ⁻¹ᵁ W.left)
        ((internalHomSheaf (pullbackModule f E) H).presheaf.map
          ((TopologicalSpace.Opens.map f.base).map W.hom).op φ)
        (pullLocalSection f E W.left e) =
      (evaluationPair (pullbackModule f E) H).apply (f ⁻¹ᵁ W.left)
        ((internalHomSheaf (pullbackModule f E) H).presheaf.map
          ((TopologicalSpace.Opens.map f.base).map W.hom).op ψ)
        (pullLocalSection f E W.left e)) : φ = ψ := by
  let c := internalHomConstructionIso (pullbackModule f E) H
  apply (ConcreteCategory.bijective_of_isIso (c.hom.app (f ⁻¹ᵁ U))).injective
  apply localSection_ext f E H U
  intro W e
  have hφ := sheafHom_naturality c.hom
    ((TopologicalSpace.Opens.map f.base).map W.hom) φ
  have hψ := sheafHom_naturality c.hom
    ((TopologicalSpace.Opens.map f.base).map W.hom) ψ
  change HomConstruction.restrictSection ((TopologicalSpace.Opens.map f.base).map W.hom)
    (c.hom.app (f ⁻¹ᵁ U) φ) =
    c.hom.app (f ⁻¹ᵁ W.left) ((internalHomSheaf (pullbackModule f E) H).presheaf.map
      ((TopologicalSpace.Opens.map f.base).map W.hom).op φ) at hφ
  change HomConstruction.restrictSection ((TopologicalSpace.Opens.map f.base).map W.hom)
    (c.hom.app (f ⁻¹ᵁ U) ψ) =
    c.hom.app (f ⁻¹ᵁ W.left) ((internalHomSheaf (pullbackModule f E) H).presheaf.map
      ((TopologicalSpace.Opens.map f.base).map W.hom).op ψ) at hψ
  change (c.hom.app (f ⁻¹ᵁ U) φ).app
    (op (Over.mk ((TopologicalSpace.Opens.map f.base).map W.hom)))
      (pullLocalSection f E W.left e) =
    (c.hom.app (f ⁻¹ᵁ U) ψ).app
      (op (Over.mk ((TopologicalSpace.Opens.map f.base).map W.hom)))
      (pullLocalSection f E W.left e)
  rw [← HomConstruction.evaluationAt_restrict, ← HomConstruction.evaluationAt_restrict,
    hφ, hψ, constructionIso_evaluation, constructionIso_evaluation]
  exact h W e

theorem homValued_bilinear_pullback_ext {X Y : Scheme.{0}} (f : X ⟶ Y)
    {A B E : OModule Y} {H : OModule X}
    (q r : SheafBilinearMap (pullbackModule f A) (pullbackModule f B)
      (internalHomSheaf (pullbackModule f E) H))
    (h : ∀ (U : Y.Opens) (a : SectionsOn A U) (b : SectionsOn B U) (e : SectionsOn E U),
      (evaluationPair (pullbackModule f E) H).apply (f ⁻¹ᵁ U)
        (q.apply (f ⁻¹ᵁ U) (pullLocalSection f A U a) (pullLocalSection f B U b))
        (pullLocalSection f E U e) =
      (evaluationPair (pullbackModule f E) H).apply (f ⁻¹ᵁ U)
        (r.apply (f ⁻¹ᵁ U) (pullLocalSection f A U a) (pullLocalSection f B U b))
        (pullLocalSection f E U e)) : q = r := by
  apply bilinear_pullback_ext f
  intro U a b
  apply pullbackHomSection_ext f E H U
  intro W e
  rw [q.naturality, r.naturality,
    pullLocalSection_restrict, pullLocalSection_restrict]
  exact h W.left (A.presheaf.map W.hom.op a) (B.presheaf.map W.hom.op b) e

/-- Compatibility of the two canonical maps, proved by the exact λ(e)u
formula on all pulled local sections and the normalized local adjunction. -/
theorem dualTensorHomMap_baseChange {X Y : Scheme.{0}} (f : X ⟶ Y) (E F : OModule Y) :
    tensorPullbackComparison f (dualSheaf E) F ≫
      (Scheme.Modules.pullback f).map (dualTensorHomMap E F) ≫ homComparison f E F =
    tensorMap (dualBaseChange f E) (𝟙 (pullbackModule f F)) ≫
      dualTensorHomMap (pullbackModule f E) (pullbackModule f F) := by
  apply ((tensorPresentation (pullbackModule f (dualSheaf E))
    (pullbackModule f F)).universal _).injective
  apply homValued_bilinear_pullback_ext f
  intro U ell u e
  change (evaluationPair (pullbackModule f E) (pullbackModule f F)).apply (f ⁻¹ᵁ U)
    ((homComparison f E F).app (f ⁻¹ᵁ U)
      (((Scheme.Modules.pullback f).map (dualTensorHomMap E F)).app (f ⁻¹ᵁ U)
        ((tensorPullbackComparison f (dualSheaf E) F).app (f ⁻¹ᵁ U)
          ((tensorPresentation (pullbackModule f (dualSheaf E))
            (pullbackModule f F)).pair.apply (f ⁻¹ᵁ U)
              (pullLocalSection f (dualSheaf E) U ell) (pullLocalSection f F U u)))))
    (pullLocalSection f E U e) =
    (evaluationPair (pullbackModule f E) (pullbackModule f F)).apply (f ⁻¹ᵁ U)
      ((dualTensorHomMap (pullbackModule f E) (pullbackModule f F)).app (f ⁻¹ᵁ U)
        ((tensorMap (dualBaseChange f E) (𝟙 (pullbackModule f F))).app (f ⁻¹ᵁ U)
          ((tensorPresentation (pullbackModule f (dualSheaf E))
            (pullbackModule f F)).pair.apply (f ⁻¹ᵁ U)
              (pullLocalSection f (dualSheaf E) U ell) (pullLocalSection f F U u))))
      (pullLocalSection f E U e)
  rw [comparison_pair, pullbackPair_normalized, pullLocalSection_map,
    homComparison_evaluation, dualTensorHomMap_evaluation, pullLocalSection_smul,
    tensorMap_apply, dualTensorHomMap_evaluation,
    dualScalar_baseChange_pullLocalSection]
  rfl

theorem homComparison_isIso {X Y : Scheme.{0}} (f : X ⟶ Y) {E : OModule Y} {r : ℕ}
    (hE : IsLocallyFreeOfRank E r) (F : OModule Y) : IsIso (homComparison f E F) := by
  letI := tensorPullbackComparison_isIso f (dualSheaf E) F
  letI := PublishedInputs.FiniteFreeHom.dualTensorHomMap_isIso hE F
  letI := PublishedInputs.FiniteFreeHom.dualTensorHomMap_isIso
    (pullback_locallyFree f hE) (pullbackModule f F)
  letI := dualBaseChange_isIso f hE
  let d := tensorIso (asIso (dualBaseChange f E)) (Iso.refl (pullbackModule f F))
  let a := tensorPullbackComparison f (dualSheaf E) F ≫
    (Scheme.Modules.pullback f).map (dualTensorHomMap E F)
  let b := d.hom ≫ dualTensorHomMap (pullbackModule f E) (pullbackModule f F)
  have hab : a ≫ homComparison f E F = b := dualTensorHomMap_baseChange f E F
  have heq : homComparison f E F = inv a ≫ b := by
    rw [← hab]
    simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [heq]
  infer_instance

end LeBrunSalamon.FiniteFreeHomBaseChange

end
