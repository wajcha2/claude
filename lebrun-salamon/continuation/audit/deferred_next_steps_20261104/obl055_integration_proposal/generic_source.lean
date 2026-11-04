import Mathlib

/-! The genuine relative-morphism functor and one generic published
finite-presentation input. All comparison maps retain both projections. -/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace LeBrunSalamon.RelativeMorphismsFunctor

abbrev sourceOver {S Y : Scheme} (pi : Y ⟶ S) (T : Over S) : Over S :=
  Over.mk (pullback.snd pi T.hom ≫ T.hom)

def sourceMap {S Y : Scheme} (pi : Y ⟶ S) {T H : Over S} (a : T ⟶ H) :
    pullback pi T.hom ⟶ pullback pi H.hom :=
  pullback.lift (pullback.fst pi T.hom) (pullback.snd pi T.hom ≫ a.left)
    (by simpa [Category.assoc, a.w] using
      (pullback.condition (f := pi) (g := T.hom)))

@[simp]
theorem sourceMap_fst {S Y : Scheme} (pi : Y ⟶ S) {T H : Over S} (a : T ⟶ H) :
    sourceMap pi a ≫ pullback.fst pi H.hom = pullback.fst pi T.hom := by
  simp [sourceMap]

@[simp]
theorem sourceMap_snd {S Y : Scheme} (pi : Y ⟶ S) {T H : Over S} (a : T ⟶ H) :
    sourceMap pi a ≫ pullback.snd pi H.hom = pullback.snd pi T.hom ≫ a.left := by
  simp [sourceMap]

def sourceMapOver {S Y : Scheme} (pi : Y ⟶ S) {T H : Over S} (a : T ⟶ H) :
    sourceOver pi T ⟶ sourceOver pi H :=
  Over.homMk (sourceMap pi a) (by
    change sourceMap pi a ≫ (pullback.snd pi H.hom ≫ H.hom) =
      pullback.snd pi T.hom ≫ T.hom
    rw [← Category.assoc, sourceMap_snd, Category.assoc, a.w])

@[simp]
theorem sourceMap_id {S Y : Scheme} (pi : Y ⟶ S) (T : Over S) :
    sourceMap pi (𝟙 T) = 𝟙 (pullback pi T.hom) := by
  apply pullback.hom_ext <;> simp [sourceMap]

@[simp]
theorem sourceMap_comp {S Y : Scheme} (pi : Y ⟶ S) {T H V : Over S}
    (a : T ⟶ H) (b : H ⟶ V) :
    sourceMap pi (a ≫ b) = sourceMap pi a ≫ sourceMap pi b := by
  apply pullback.hom_ext <;> simp [sourceMap, Category.assoc]

@[simp]
theorem sourceMapOver_id {S Y : Scheme} (pi : Y ⟶ S) (T : Over S) :
    sourceMapOver pi (𝟙 T) = 𝟙 (sourceOver pi T) := by
  ext
  exact sourceMap_id pi T

@[simp]
theorem sourceMapOver_comp {S Y : Scheme} (pi : Y ⟶ S) {T H V : Over S}
    (a : T ⟶ H) (b : H ⟶ V) :
    sourceMapOver pi (a ≫ b) = sourceMapOver pi a ≫ sourceMapOver pi b := by
  ext
  exact sourceMap_comp pi a b

/-- The actual relative-morphism functor on every scheme over S. -/
def morphismFunctor {S Y Z : Scheme} (pi : Y ⟶ S) (q : Z ⟶ S) :
    (Over S)ᵒᵖ ⥤ Type _ where
  obj T := sourceOver pi T.unop ⟶ Over.mk q
  map a := ↾(fun f => sourceMapOver pi a.unop ≫ f)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro f
    simp
  map_comp a b := by
    apply ConcreteCategory.hom_ext
    intro f
    simp [Category.assoc]

/-- A map from the base-changed source to Z over S is exactly a map
to the base-changed target over T, by the actual pullback lift. -/
def homBaseChangeEquiv {S Y Z : Scheme.{0}} (pi : Y ⟶ S) (q : Z ⟶ S)
    (T : Over S) :
    (sourceOver pi T ⟶ Over.mk q) ≃
      ((Over.mk (pullback.snd pi T.hom) : Over T.left) ⟶
        Over.mk (pullback.snd q T.hom)) where
  toFun g := Over.homMk
    (pullback.lift g.left (pullback.snd pi T.hom) g.w)
    (by simp)
  invFun f := Over.homMk (f.left ≫ pullback.fst q T.hom) (by
    have hf : f.left ≫ pullback.snd q T.hom = pullback.snd pi T.hom := f.w
    change (f.left ≫ pullback.fst q T.hom) ≫ q =
      pullback.snd pi T.hom ≫ T.hom
    rw [Category.assoc, pullback.condition, ← Category.assoc, hf])
  left_inv g := by
    apply Over.OverMorphism.ext
    change pullback.lift g.left (pullback.snd pi T.hom) g.w ≫
      pullback.fst q T.hom = g.left
    simp
  right_inv f := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
      simp
    · change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
      simpa using f.w.symm

@[simp]
theorem homBaseChangeEquiv_fst {S Y Z : Scheme.{0}} (pi : Y ⟶ S)
    (q : Z ⟶ S) (T : Over S) (g : sourceOver pi T ⟶ Over.mk q) :
    (homBaseChangeEquiv pi q T g).left ≫ pullback.fst q T.hom = g.left := by
  simp [homBaseChangeEquiv]

@[simp]
theorem homBaseChangeEquiv_snd {S Y Z : Scheme.{0}} (pi : Y ⟶ S)
    (q : Z ⟶ S) (T : Over S) (g : sourceOver pi T ⟶ Over.mk q) :
    (homBaseChangeEquiv pi q T g).left ≫ pullback.snd q T.hom =
      pullback.snd pi T.hom := by
  simp [homBaseChangeEquiv]

/-- Target base change commutes with the actual source base-change maps.
This is the naturality square for Hom_S(Y_T,Z) ≃ Hom_T(Y_T,Z_T). -/
theorem homBaseChangeEquiv_naturality {S Y Z : Scheme.{0}}
    (pi : Y ⟶ S) (q : Z ⟶ S) {T H : Over S} (a : T ⟶ H)
    (g : sourceOver pi H ⟶ Over.mk q) :
    (homBaseChangeEquiv pi q T (sourceMapOver pi a ≫ g)).left ≫ sourceMap q a =
      sourceMap pi a ≫ (homBaseChangeEquiv pi q H g).left := by
  apply pullback.hom_ext
  · simp only [Category.assoc, sourceMap_fst, homBaseChangeEquiv_fst]
    rfl
  · calc
      ((homBaseChangeEquiv pi q T (sourceMapOver pi a ≫ g)).left ≫
          sourceMap q a) ≫ pullback.snd q H.hom =
          (homBaseChangeEquiv pi q T (sourceMapOver pi a ≫ g)).left ≫
            pullback.snd q T.hom ≫ a.left := by
              rw [Category.assoc, sourceMap_snd]
      _ = pullback.snd pi T.hom ≫ a.left := by
        rw [← Category.assoc, homBaseChangeEquiv_snd]
      _ = sourceMap pi a ≫ pullback.snd pi H.hom := (sourceMap_snd pi a).symm
      _ = (sourceMap pi a ≫ (homBaseChangeEquiv pi q H g).left) ≫
          pullback.snd q H.hom := by
            rw [Category.assoc, homBaseChangeEquiv_snd]

end LeBrunSalamon.RelativeMorphismsFunctor

namespace LeBrunSalamon.PublishedInputs.RelativeHom

open LeBrunSalamon.RelativeMorphismsFunctor

/-- **Published input (scheme-representer specialization):** Stacks Project,
Proposition 99.12.3 (0D1C), for the genuine all-test relative-morphism functor.
The source is proper, flat and of finite presentation; the target is separated
and of finite presentation. Finite presentation is written as local finite
presentation, quasi-compactness and quasi-separatedness (Definition29.22.1,
01TO). The theorem gives an algebraic-space representer locally of finite
presentation. A supplied scheme representing the same functor has that
property by Yoneda uniqueness and invariance under isomorphism. This input
asserts no scheme-existence conclusion from properness.

The displayed Stacks functor uses maps Y_T → Z_T over T. The actual functor
below uses maps Y_T → Z over S. Their explicit pullback equivalence, both
projection equations and naturality are proved in homBaseChangeEquiv above.
No contact, conic, project family or selected subfamily enters this input.
https://stacks.math.columbia.edu/tag/0D1C
https://stacks.math.columbia.edu/tag/0D19
https://stacks.math.columbia.edu/tag/01TO -/
theorem locallyOfFinitePresentation {S Y Z : Scheme.{0}}
    (pi : Y ⟶ S) (q : Z ⟶ S)
    (hproper : IsProper pi) (hflat : Flat pi)
    (hsourceLFP : LocallyOfFinitePresentation pi)
    (hsourceQC : QuasiCompact pi) (hsourceQS : QuasiSeparated pi)
    (hseparated : IsSeparated q) (htargetLFP : LocallyOfFinitePresentation q)
    (htargetQC : QuasiCompact q) (htargetQS : QuasiSeparated q)
    (H : Over S) (hrep : (morphismFunctor pi q).RepresentableBy H) :
    LocallyOfFinitePresentation H.hom := by
  sorry

end LeBrunSalamon.PublishedInputs.RelativeHom

end
