import LSRelativeHomFunctorTranslationProbe
import Lean

/-! Generic target-base-change normalization for the relative Hom functor.
The imported probe is the unchanged, completed conditional diagnostic 59cbcc58.
This file introduces no published input or project theorem assumption. -/

noncomputable section
set_option autoImplicit false
set_option stderrAsMessages false
set_option profiler true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.RelativeMorphismsFunctorPrototype

namespace LeBrunSalamon.RelativeHomBaseChangeNormalization

#eval (do let err ← IO.getStderr; err.putStrLn "HOM_NORMALIZATION_STAGE ENTER_01"; err.flush : IO Unit)

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

#eval (do let err ← IO.getStderr; err.putStrLn "HOM_NORMALIZATION_STAGE ENTER_02"; err.flush : IO Unit)

@[simp]
theorem homBaseChangeEquiv_fst {S Y Z : Scheme.{0}} (pi : Y ⟶ S)
    (q : Z ⟶ S) (T : Over S) (g : sourceOver pi T ⟶ Over.mk q) :
    (homBaseChangeEquiv pi q T g).left ≫ pullback.fst q T.hom = g.left := by
  simp [homBaseChangeEquiv]

#eval (do let err ← IO.getStderr; err.putStrLn "HOM_NORMALIZATION_STAGE ENTER_03"; err.flush : IO Unit)

@[simp]
theorem homBaseChangeEquiv_snd {S Y Z : Scheme.{0}} (pi : Y ⟶ S)
    (q : Z ⟶ S) (T : Over S) (g : sourceOver pi T ⟶ Over.mk q) :
    (homBaseChangeEquiv pi q T g).left ≫ pullback.snd q T.hom =
      pullback.snd pi T.hom := by
  simp [homBaseChangeEquiv]

#eval (do let err ← IO.getStderr; err.putStrLn "HOM_NORMALIZATION_STAGE ENTER_04"; err.flush : IO Unit)

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

#print axioms homBaseChangeEquiv
#print axioms homBaseChangeEquiv_naturality
#eval (do let err ← IO.getStderr; err.putStrLn "HOM_NORMALIZATION_COMPLETE"; err.flush : IO Unit)

end LeBrunSalamon.RelativeHomBaseChangeNormalization

end
