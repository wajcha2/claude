import LSFiniteFreeHomBaseChange
import RecompileExtensionsPart02

/-! Canonical Hom-fiber injectivity, with the actual evaluation map.
No new published input is introduced. Finite-free Hom base change is the
proved canonical comparison. Faithfulness of evaluation on Spec C follows
from its one-point topology, including the empty open.
Compiler receipts record the exact source and the scope of dependency verification. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton
open LeBrunSalamon.Construction
open LeBrunSalamon.FiniteFreeHomBaseChange

namespace LeBrunSalamon.HomFiberInjectivity

private theorem empty_section_eq_zero (M : OModule ComplexBase)
    (a : SectionsOn M ⊥) : a = 0 := by
  let F : TopCat.Sheaf AddCommGrpCat ComplexBase := ⟨M.presheaf, M.isSheaf⟩
  have h := (TopCat.Sheaf.isTerminalOfEmpty F).hom_ext (𝟙 _) 0
  have ha := congrArg
    (fun f : F.obj.obj (op ⊥) ⟶ F.obj.obj (op ⊥) => f a) h
  simpa using ha

private theorem open_bot_or_top (U : ComplexBase.Opens) : U = ⊥ ∨ U = ⊤ := by
  by_cases h : (U : Set ComplexBase).Nonempty
  · right
    apply top_unique
    intro x hx
    obtain ⟨y, hy⟩ := h
    change x ∈ (U : Set ComplexBase)
    have hxy : x = y := Subsingleton.elim _ _
    subst x
    exact hy
  · left
    apply SetLike.coe_injective
    exact Set.not_nonempty_iff_eq_empty.mp h

/-- A local sheaf morphism on the top open of Spec C is determined by its
actual action on global sections. The only other open is empty. -/
theorem constructedHom_top_ext (E F : OModule ComplexBase)
    (a b : HomConstruction.Section E F ⊤)
    (h : ∀ v, HomConstruction.evaluationAt E F ⊤ a v =
      HomConstruction.evaluationAt E F ⊤ b v) : a = b := by
  have hlocal (U : ComplexBase.Opens) (i : U ⟶ (⊤ : ComplexBase.Opens))
      (v : SectionsOn E U) :
      a.app (op (Over.mk i)) v = b.app (op (Over.mk i)) v := by
    rcases open_bot_or_top U with hU | hU
    · subst U
      exact (empty_section_eq_zero F _).trans (empty_section_eq_zero F _).symm
    · subst U
      have hi : i = 𝟙 (⊤ : ComplexBase.Opens) := Subsingleton.elim _ _
      subst i
      exact h v
  ext W v
  exact hlocal W.unop.left W.unop.hom v

/-- The project's chosen internal Hom inherits the same injectivity through
its proved canonical comparison to the constructed sheaf Hom. -/
theorem internalHom_top_ext (E F : OModule ComplexBase)
    (a b : SectionsOn (internalHomSheaf E F) ⊤)
    (h : ∀ v, (evaluationPair E F).apply ⊤ a v =
      (evaluationPair E F).apply ⊤ b v) : a = b := by
  let e := internalHomConstructionIso E F
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).injective
  apply constructedHom_top_ext E F
  intro v
  rw [constructionIso_evaluation, constructionIso_evaluation]
  exact h v

/-- Currying identifies the canonical Hom comparison with the actual
pulled-back evaluation pairing on all sections, not only on generators. -/
theorem homComparison_evaluation_all {X Y : Scheme.{0}} (f : X ⟶ Y)
    (E F : OModule Y) (U : X.Opens)
    (a : SectionsOn (pullbackModule f (internalHomSheaf E F)) U)
    (v : SectionsOn (pullbackModule f E) U) :
    (evaluationPair (pullbackModule f E) (pullbackModule f F)).apply U
      ((homComparison f E F).app U a) v =
    (pullbackPair f (evaluationPair E F)).apply U a v := by
  rw [homComparison, curry_evaluation]
  exact congrArg (fun b : SheafBilinearMap
    (pullbackModule f (internalHomSheaf E F)) (pullbackModule f E)
      (pullbackModule f F) => b.apply U a v)
        (tensorLift_pair (pullbackPair f (evaluationPair E F)))

/-- The canonical pulled evaluation on the original Hom fiber is injective.
This statement uses exactly the underlying function of homFiberEvaluation. -/
theorem homFiberEvaluation_injective {Y : Scheme.{0}} {r : ℕ}
    (E : AlgebraicVectorBundle Y r) (F : OModule Y) (x : ComplexBase ⟶ Y) :
    Function.Injective (fun a : Fiber (internalHomSheaf E.sheaf F) x =>
      fun v : Fiber E.sheaf x =>
        (pullbackPair x (evaluationPair E.sheaf F)).apply ⊤ a v) := by
  letI := homComparison_isIso x E.locallyFree F
  intro a b hab
  apply (ConcreteCategory.bijective_of_isIso ((homComparison x E.sheaf F).app ⊤)).injective
  apply internalHom_top_ext (pullbackModule x E.sheaf) (pullbackModule x F)
  intro v
  rw [homComparison_evaluation_all, homComparison_evaluation_all]
  exact congrFun hab v

end LeBrunSalamon.HomFiberInjectivity

end
