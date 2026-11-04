import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! Reducedness of an actual pushout of reduced schemes, proved through
the nilradical closed subscheme.  This avoids introducing a field-conic
reducedness input merely to handle the given nodal pushout. No admission. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LeBrunSalamon.ReducedPushout

abbrev reduction (Y : Scheme) : Scheme := Y.nilradical.subscheme

abbrev inclusion (Y : Scheme) : reduction Y ⟶ Y := Y.nilradical.subschemeι

instance reduction_reduced (Y : Scheme) : IsReduced (reduction Y) := by
  letI (U : Y.affineOpens) :
      _root_.IsReduced (Γ(Y, U) ⧸ Y.nilradical.ideal U) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (by
      change (⊥ : Ideal Γ(Y, U)).radical.IsRadical
      exact Ideal.radical_isRadical _)
  letI (U : Y.affineOpens) :
      IsReduced (Y.nilradical.subschemeCover.openCover.X U) := by
    change IsReduced (Spec (CommRingCat.of (Γ(Y, U) ⧸ Y.nilradical.ideal U)))
    infer_instance
  exact IsReduced.of_openCover _ Y.nilradical.subschemeCover.openCover

theorem nilradical_le_ker {X Y : Scheme} (f : X ⟶ Y)
    [QuasiCompact f] [IsReduced X] : Y.nilradical ≤ f.ker := by
  intro U a ha
  rw [Scheme.Hom.ker_apply]
  apply RingHom.mem_ker.mpr
  have hn : IsNilpotent a := by
    change a ∈ (⊥ : Ideal Γ(Y, U)).radical at ha
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp ha
    exact ⟨n, by simpa only [Ideal.mem_bot] using hn⟩
  exact (hn.map (f.app U).hom).eq_zero

def lift {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f] [IsReduced X] :
    X ⟶ reduction Y :=
  f.toImage ≫ Scheme.IdealSheafData.inclusion (nilradical_le_ker f)

@[reassoc] theorem lift_inclusion {X Y : Scheme} (f : X ⟶ Y)
    [QuasiCompact f] [IsReduced X] : lift f ≫ inclusion Y = f := by
  rw [lift, Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  exact f.toImage_imageι

/-- The actual pushout maps factor through the nilradical subscheme.
Their universal map is inverse to the reduction inclusion. -/
theorem isReduced_of_isPushout {A B N Y : Scheme}
    (p : N ⟶ A) (q : N ⟶ B) (i : A ⟶ Y) (j : B ⟶ Y)
    [QuasiCompact i] [QuasiCompact j] [IsReduced A] [IsReduced B]
    (h : IsPushout p q i j) : IsReduced Y := by
  have hnode : p ≫ lift i = q ≫ lift j := by
    apply (cancel_mono (inclusion Y)).mp
    rw [Category.assoc, lift_inclusion, Category.assoc, lift_inclusion, h.w]
  let r : Y ⟶ reduction Y := h.desc (lift i) (lift j) hnode
  have hr : r ≫ inclusion Y = 𝟙 Y := by
    apply h.hom_ext
    · rw [← Category.assoc, h.inl_desc, lift_inclusion, Category.comp_id]
    · rw [← Category.assoc, h.inr_desc, lift_inclusion, Category.comp_id]
  have hir : inclusion Y ≫ r = 𝟙 (reduction Y) := by
    apply (cancel_mono (inclusion Y)).mp
    rw [Category.assoc, hr, Category.comp_id, Category.id_comp]
  let e : Y ≅ reduction Y := ⟨r, inclusion Y, hr, hir⟩
  letI : IsIso e.hom := e.isIso_hom
  letI : IsOpenImmersion e.hom := inferInstance
  exact isReduced_of_isOpenImmersion e.hom

end LeBrunSalamon.ReducedPushout
end
