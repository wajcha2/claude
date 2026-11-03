import RecompileExtensionsPart02

/-!
# The canonical degree-zero finite free base-change map

The single published input in this file is the structure-sheaf, degree-zero
specialization of Stacks, Lemma 30.5.3 (tag 0CKW). Its source allows arbitrary
schemes: no quasi-compactness or separatedness assumption is omitted here.
Global finite freeness is a specialization of finite local freeness.
The map itself is defined below from the two actual scheme morphisms.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace LeBrunSalamon.FiniteFreeBaseChange

variable (K : Type) [CommRing K]

/-- Scalars on global functions are pulled back by the given structure map. -/
def sectionAlgebra {X : Scheme} (sX : X ⟶ Spec (CommRingCat.of K)) :
    Algebra K Γ(X, ⊤) :=
  (sX.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra

variable (B : Type) [CommRing B] [Algebra K B]
variable {X Y : Scheme} (sX : X ⟶ Spec (CommRingCat.of K))
  (p : Y ⟶ X) (q : Y ⟶ Spec (CommRingCat.of B))
  (h : p ≫ sX = q ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)))

/-- The actual map `a ⊗ b ↦ p*(a) q*(b)` on global functions. -/
def globalMap :
    letI := sectionAlgebra K sX
    Γ(X, ⊤) ⊗[K] B →+* Γ(Y, ⊤) := by
  letI := sectionAlgebra K sX
  letI := sectionAlgebra K (p ≫ sX)
  let fp : Γ(X, ⊤) →ₐ[K] Γ(Y, ⊤) :=
    { toRingHom := p.appTop.hom
      commutes' := fun _ => rfl }
  let fq : B →ₐ[K] Γ(Y, ⊤) :=
    { toRingHom := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
      commutes' := by
        intro c
        change q.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv
            (algebraMap K B c)) =
          (p ≫ sX).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)
        rw [h, Scheme.Hom.comp_appTop]
        exact congrArg (fun z => q.appTop z)
          (congrArg (fun k : CommRingCat.of K ⟶
            Γ(Spec (CommRingCat.of B), ⊤) => k c)
            (Scheme.ΓSpecIso_inv_naturality
              (CommRingCat.ofHom (algebraMap K B)))) }
  exact (Algebra.TensorProduct.lift fp fq (fun _ _ => Commute.all _ _)).toRingHom

@[simp] theorem globalMap_tmul (a : Γ(X, ⊤)) (b : B) :
    letI := sectionAlgebra K sX
    globalMap K B sX p q h (a ⊗ₜ[K] b) =
      p.appTop a * q.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) := rfl

end LeBrunSalamon.FiniteFreeBaseChange

namespace LeBrunSalamon.PublishedInputs.FiniteFreeBaseChange

/-- Stacks, Lemma 30.5.3, tag 0CKW, with `i = 0` and `F = O_X`.
The pullback of the structure sheaf is the structure sheaf; the displayed
map is its canonical base-change map, with both structure maps explicit.
Source: https://stacks.math.columbia.edu/tag/0CKW . -/
theorem structureH0_bijective
    (K B : Type) [CommRing K] [CommRing B] [Algebra K B]
    [Module.Free K B] [Module.Finite K B]
    {X Y : Scheme} (sX : X ⟶ Spec (CommRingCat.of K))
    (p : Y ⟶ X) (q : Y ⟶ Spec (CommRingCat.of B))
    (h : IsPullback p q sX (Spec.map (CommRingCat.ofHom (algebraMap K B)))) :
    Function.Bijective (LeBrunSalamon.FiniteFreeBaseChange.globalMap K B sX p q h.w) := by
  sorry

end LeBrunSalamon.PublishedInputs.FiniteFreeBaseChange

end
