import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! Actual fibre comparison for an isomorphism over a fixed base. The
maps, both inverses and base projections are explicit. Smoothness and
reducedness are transported through these same maps, with no admission. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LeBrunSalamon.FibreIsomorphism

variable {X Y S T : Scheme} (p : X ⟶ S) (q : Y ⟶ S)
  (e : X ≅ Y) (he : e.hom ≫ q = p) (a : T ⟶ S)

include he in
theorem inverse_over : e.inv ≫ p = q := by
  rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]

def hom : pullback p a ⟶ pullback q a :=
  pullback.lift (pullback.fst p a ≫ e.hom) (pullback.snd p a)
    (by rw [Category.assoc, he, pullback.condition])

@[reassoc] theorem hom_fst : hom p q e he a ≫ pullback.fst q a = pullback.fst p a ≫ e.hom :=
  pullback.lift_fst _ _ _

@[reassoc] theorem hom_snd : hom p q e he a ≫ pullback.snd q a = pullback.snd p a :=
  pullback.lift_snd _ _ _

def iso : pullback p a ≅ pullback q a where
  hom := hom p q e he a
  inv := hom q p e.symm (inverse_over p q e he) a
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, hom_fst, ← Category.assoc, hom_fst]
      simp only [Iso.symm_hom, Category.assoc, e.hom_inv_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hom_snd, hom_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, hom_fst, ← Category.assoc, hom_fst]
      simp only [Iso.symm_hom, Category.assoc, e.inv_hom_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hom_snd, hom_snd, Category.id_comp]

@[reassoc] theorem iso_hom_snd : (iso p q e he a).hom ≫ pullback.snd q a = pullback.snd p a :=
  hom_snd p q e he a

@[reassoc] theorem iso_inv_snd : (iso p q e he a).inv ≫ pullback.snd p a = pullback.snd q a :=
  hom_snd q p e.symm (inverse_over p q e he) a

include he in
theorem smooth_target [Smooth (pullback.snd p a)] : Smooth (pullback.snd q a) := by
  let u := iso p q e he a
  letI : IsIso u.inv := u.isIso_inv
  rw [← iso_inv_snd p q e he a]
  infer_instance

include he in
theorem smooth_source [Smooth (pullback.snd q a)] : Smooth (pullback.snd p a) := by
  let u := iso p q e he a
  letI : IsIso u.hom := u.isIso_hom
  rw [← iso_hom_snd p q e he a]
  infer_instance

include he in
theorem reduced_target [IsReduced (pullback p a)] : IsReduced (pullback q a) := by
  let u := iso p q e he a
  letI : IsIso u.inv := u.isIso_inv
  letI : IsOpenImmersion u.inv := inferInstance
  exact isReduced_of_isOpenImmersion u.inv

include he in
theorem reduced_source [IsReduced (pullback q a)] : IsReduced (pullback p a) := by
  let u := iso p q e he a
  letI : IsIso u.hom := u.isIso_hom
  letI : IsOpenImmersion u.hom := inferInstance
  exact isReduced_of_isOpenImmersion u.hom

end LeBrunSalamon.FibreIsomorphism
end
