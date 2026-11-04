import LSYonedaExtensionSplitting

/-!
Actual representation of degree-one Ext classes by short exact sequences
in an abelian category with enough injectives. Embed the given kernel
object into an injective, obtain a degree-zero lift by Ext exactness, and
pull back the resulting short exact sequence along that actual morphism.
The equality of Ext classes is proved by naturality.

There is no admission in this file. Off-graph native candidate.
-/

noncomputable section
set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace LeBrunSalamon.YonedaExtensionSplitting

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  [EnoughInjectives C]

/-- Every degree-one class is the class of the actual pullback extension.
This supplies the representation hypothesis of the already proved
extension-splitting criterion. -/
theorem classesRepresented (U E : C) : ClassesRepresented U E := by
  intro ξ
  let S := ShortComplex.mk (Injective.ι E) (cokernel.π (Injective.ι E))
    (cokernel.condition (Injective.ι E))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  obtain ⟨u, hu⟩ := Ext.covariant_sequence_exact₁ U hS ξ
    (Ext.eq_zero_of_injective _) (rfl : 0 + 1 = 1)
  let f : U ⟶ S.X₃ := Ext.homEquiv₀ u
  let T := S.pull f
  have hT : T.ShortExact := hS.pull f
  let φ : T ⟶ S :=
    { τ₁ := 𝟙 E
      τ₂ := pullback.snd f S.g
      τ₃ := f
      comm₁₂ := by simp [T, ShortComplex.pull]
      comm₂₃ := by
        dsimp [T, ShortComplex.pull]
        exact (pullback.condition (f := f) (g := S.g)).symm }
  refine ⟨T.X₂, T.f, T.g, T.zero, hT, ?_⟩
  change hT.extClass = ξ
  calc
    hT.extClass = (Ext.mk₀ f).comp hS.extClass (zero_add 1) := by
      simpa only [φ, Ext.comp_mk₀_id] using hT.extClass_naturality hS φ
    _ = ξ := by
      simpa only [f, Ext.mk₀_homEquiv₀_apply] using hu

theorem allExtensionsSplit_iff_ext1_subsingleton (U E : C) :
    AllExtensionsSplit U E ↔ Subsingleton (Ext.{w} U E 1) :=
  allExtensionsSplit_iff_subsingleton U E (classesRepresented U E)

end LeBrunSalamon.YonedaExtensionSplitting

end
