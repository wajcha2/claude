import Mathlib

/-! Closed unions and the actual map induced from a supplied pushout.
The only input is the literal closed-union theorem of Stacks 29.4.5--6
(0C4I/0C4J). The comparison with an independently supplied pushout and
the closed immersion of its induced map are proved here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LeBrunSalamon.ClosedUnionEmbedding

variable {A B S : Scheme} (f : A ⟶ S) (g : B ⟶ S)

/-- The literal scheme-theoretic union, cut out by the intersection of
the two actual kernel ideal sheaves. -/
abbrev unionScheme : Scheme := (f.ker ⊓ g.ker).subscheme

abbrev inclusion : unionScheme f g ⟶ S := (f.ker ⊓ g.ker).subschemeι

def left : A ⟶ unionScheme f g :=
  IsClosedImmersion.lift (inclusion f g) f (by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact inf_le_left)

def right : B ⟶ unionScheme f g :=
  IsClosedImmersion.lift (inclusion f g) g (by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact inf_le_right)

@[simp] theorem left_inclusion : left f g ≫ inclusion f g = f :=
  IsClosedImmersion.lift_fac _ _ _

@[simp] theorem right_inclusion : right f g ≫ inclusion f g = g :=
  IsClosedImmersion.lift_fac _ _ _

end LeBrunSalamon.ClosedUnionEmbedding

namespace LeBrunSalamon.PublishedInputs.ClosedUnions

/-- Stacks Project, Lemmas 29.4.5 (0C4I) and 29.4.6 (0C4J).
The first identifies the scheme-theoretic intersection with the fibre
product; the second says that its pushout is the literal union cut out by
I ∩ J. `hintersection` supplies precisely that cartesian intersection.
No genus, line bundle, chosen tuple or family construction occurs here.
-/
theorem union_isPushout {A B N S : Scheme}
    (f : A ⟶ S) (g : B ⟶ S) [IsClosedImmersion f] [IsClosedImmersion g]
    (p : N ⟶ A) (q : N ⟶ B) (hintersection : IsPullback p q f g) :
    IsPushout p q (ClosedUnionEmbedding.left f g) (ClosedUnionEmbedding.right f g) := by
  sorry

end LeBrunSalamon.PublishedInputs.ClosedUnions

namespace LeBrunSalamon.ClosedUnionEmbedding

/-- A supplied scheme pushout maps by a closed immersion into an ambient
scheme when its two branch maps are closed immersions and their actual
intersection is exactly the supplied node. -/
theorem induced_closedImmersion {A B N Y S : Scheme}
    (p : N ⟶ A) (q : N ⟶ B) (i : A ⟶ Y) (j : B ⟶ Y)
    (hpush : IsPushout p q i j)
    (f : A ⟶ S) (g : B ⟶ S) [IsClosedImmersion f] [IsClosedImmersion g]
    (hintersection : IsPullback p q f g) :
    IsClosedImmersion (hpush.desc f g hintersection.w) := by
  let hU := PublishedInputs.ClosedUnions.union_isPushout f g p q hintersection
  let a : Y ⟶ unionScheme f g := hpush.desc (left f g) (right f g) hU.w
  let b : unionScheme f g ⟶ Y := hU.desc i j hpush.w
  have hai : i ≫ a = left f g := hpush.inl_desc _ _ _
  have haj : j ≫ a = right f g := hpush.inr_desc _ _ _
  have hbl : left f g ≫ b = i := hU.inl_desc _ _ _
  have hbr : right f g ≫ b = j := hU.inr_desc _ _ _
  let e : Y ≅ unionScheme f g :=
    { hom := a
      inv := b
      hom_inv_id := by
        apply hpush.hom_ext
        · rw [← Category.assoc, hai, hbl, Category.comp_id]
        · rw [← Category.assoc, haj, hbr, Category.comp_id]
      inv_hom_id := by
        apply hU.hom_ext
        · rw [← Category.assoc, hbl, hai, Category.comp_id]
        · rw [← Category.assoc, hbr, haj, Category.comp_id] }
  have he : hpush.desc f g hintersection.w = e.hom ≫ inclusion f g := by
    apply hpush.hom_ext
    · rw [hpush.inl_desc, ← Category.assoc]
      exact (congrArg (fun t => t ≫ inclusion f g) hai).trans (left_inclusion f g) |>.symm
    · rw [hpush.inr_desc, ← Category.assoc]
      exact (congrArg (fun t => t ≫ inclusion f g) haj).trans (right_inclusion f g) |>.symm
  rw [he]
  infer_instance

end LeBrunSalamon.ClosedUnionEmbedding

end
