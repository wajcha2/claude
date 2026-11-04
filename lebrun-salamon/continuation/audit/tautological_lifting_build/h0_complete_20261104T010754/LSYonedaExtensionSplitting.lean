import Mathlib

/-!
The actual short-exact splitting criterion for the derived Ext class.
This Mathlib-only adapter contains no admission.  The final implication
takes representation of Ext1 classes by actual short exact sequences as an
explicit hypothesis; it does not silently identify Yoneda and derived Ext.
Off-graph draft, not yet native checked.
-/

noncomputable section
set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace LeBrunSalamon.YonedaExtensionSplitting

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Zero of the actual connecting Ext class is equivalent to a right
inverse of the actual quotient morphism. -/
theorem extClass_zero_iff {S : ShortComplex C} (hS : S.ShortExact) :
    hS.extClass = 0 ↔ ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 S.X₃ := by
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ S.X₃ hS
      (Ext.mk₀ (𝟙 S.X₃)) (rfl : 0 + 1 = 1) (by simp [hz])
    refine ⟨Ext.homEquiv₀ x, ?_⟩
    apply (Ext.mk₀_bijective S.X₃ S.X₃).injective
    rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
    exact hx
  · rintro ⟨s, hs⟩
    calc
      hS.extClass = (Ext.mk₀ (𝟙 S.X₃)).comp hS.extClass (zero_add 1) :=
        (Ext.mk₀_id_comp _).symm
      _ = (Ext.mk₀ (s ≫ S.g)).comp hS.extClass (zero_add 1) := by rw [hs]
      _ = (Ext.mk₀ s).comp ((Ext.mk₀ S.g).comp hS.extClass (zero_add 1))
          (zero_add 1) := (Ext.mk₀_comp_mk₀_assoc s S.g hS.extClass).symm
      _ = 0 := by rw [hS.comp_extClass]; simp

/-- The project-style Yoneda vanishing predicate, over an arbitrary abelian
category and a specified quotient object. -/
def AllExtensionsSplit (U E : C) : Prop :=
  ∀ (F : C) (i : E ⟶ F) (p : F ⟶ U) (hz : i ≫ p = 0),
    (ShortComplex.mk i p hz).ShortExact →
      ∃ s : U ⟶ F, s ≫ p = 𝟙 U

theorem allExtensionsSplit_of_subsingleton (U E : C)
    (h : Subsingleton (Ext.{w} U E 1)) : AllExtensionsSplit U E := by
  intro F i p hz hS
  exact (extClass_zero_iff hS).mp (h.elim _ _)

/-- This hypothesis is exactly the degree-one representation assertion of
Stacks13.27.5.  It is displayed as a hypothesis here, not admitted. -/
def ClassesRepresented (U E : C) : Prop :=
  ∀ ξ : Ext.{w} U E 1,
    ∃ (F : C) (i : E ⟶ F) (p : F ⟶ U) (hz : i ≫ p = 0)
      (hS : (ShortComplex.mk i p hz).ShortExact), hS.extClass = ξ

theorem subsingleton_of_allExtensionsSplit (U E : C)
    (hrep : ClassesRepresented U E) (h : AllExtensionsSplit U E) :
    Subsingleton (Ext.{w} U E 1) := by
  apply subsingleton_of_forall_eq 0
  intro ξ
  obtain ⟨F, i, p, hz, hS, hc⟩ := hrep ξ
  rw [← hc]
  exact (extClass_zero_iff hS).mpr (h F i p hz hS)

theorem allExtensionsSplit_iff_subsingleton (U E : C)
    (hrep : ClassesRepresented U E) :
    AllExtensionsSplit U E ↔ Subsingleton (Ext.{w} U E 1) :=
  ⟨subsingleton_of_allExtensionsSplit U E hrep,
    allExtensionsSplit_of_subsingleton U E⟩

/-- The exact global-section lifting step, written as an actual lift of the
given morphism through the given quotient.  For U=O this is H0 surjectivity.
No rank, dimension or replacement-map assertion is used. -/
theorem hom_lift_of_ext_subsingleton (U : C) {S : ShortComplex C}
    (hS : S.ShortExact) (h : Subsingleton (Ext.{w} U S.X₁ 1))
    (a : U ⟶ S.X₃) : ∃ b : U ⟶ S.X₂, b ≫ S.g = a := by
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ U hS
    (Ext.mk₀ a) (rfl : 0 + 1 = 1) (h.elim _ _)
  refine ⟨Ext.homEquiv₀ x, ?_⟩
  apply (Ext.mk₀_bijective U S.X₃).injective
  rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
  exact hx

theorem hom_lift_of_extensionsSplit (U : C) {S : ShortComplex C}
    (hS : S.ShortExact) (hrep : ClassesRepresented U S.X₁)
    (h : AllExtensionsSplit U S.X₁) (a : U ⟶ S.X₃) :
    ∃ b : U ⟶ S.X₂, b ≫ S.g = a :=
  hom_lift_of_ext_subsingleton U hS
    (subsingleton_of_allExtensionsSplit U S.X₁ hrep h) a

end LeBrunSalamon.YonedaExtensionSplitting

end
