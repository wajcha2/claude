import LSFiniteTypeSpreading
import LSContactLineTests
import LSFamilyDescentReparametrization
import LSFamilyReparametrizationFibres

/-!
# Reparametrization in families and over arbitrary fields

Complex-point detection is used only on reduced schemes locally of
finite type over C.  A field-valued source automorphism is first spread
while retaining the original parameterized family; the tensor identities
then return along the actual field-valued base map.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction.FamilyBivectors


namespace FamilyReparametrization

open Parametrized

variable (P : ProjectiveLineOverC)

/-- Functoriality of the literal source-family map. -/
theorem sourceMap_comp {A B C : Scheme}
    {sA : A ⟶ ComplexBase} {sB : B ⟶ ComplexBase} {sC : C ⟶ ComplexBase}
    (a : PointsOver A sA B sB) (b : PointsOver B sB C sC)
    (c : PointsOver A sA C sC) (h : a.val ≫ b.val = c.val) :
    rationalSourceMap P a ≫ rationalSourceMap P b = rationalSourceMap P c := by
  apply pullback.hom_ext
  · simp only [rationalSourceMap, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [rationalSourceMap, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, h]

@[reassoc] theorem inclusion_sourceMap {A B : Scheme}
    (sA : A ⟶ ComplexBase) (sB : B ⟶ ComplexBase)
    (u : PointsOver A sA B sB) (t : BasePoint sA) :
    inclusion P sA t ≫ rationalSourceMap P u =
      inclusion P sB (⟨t.val ≫ u.val, by
        rw [Category.assoc, u.property, t.property]⟩ : BasePoint sB) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, rationalSourceMap, pullback.lift_fst, inclusion_projection]
  · simp only [Category.assoc, rationalSourceMap, pullback.lift_snd, inclusion_parameter]

theorem pulledEvaluation_overC {A B : Scheme}
    (sA : A ⟶ ComplexBase) (sB : B ⟶ ComplexBase)
    (u : PointsOver A sA B sB) {n : ℕ} (X : ContactFanoManifold n)
    (f : Source P sB ⟶ X.variety.scheme)
    (hf : f ≫ X.variety.structureMap = parameter P sB ≫ sB) :
    (rationalSourceMap P u ≫ f) ≫ X.variety.structureMap = parameter P sA ≫ sA := by
  rw [Category.assoc, hf, ← Category.assoc]
  simp only [rationalSourceMap, parameter, pullback.lift_snd_assoc,
    Category.assoc, u.property]

def pulledFamily {A B : Scheme}
    (sA : A ⟶ ComplexBase) (sB : B ⟶ ComplexBase)
    (u : PointsOver A sA B sB) {n : ℕ} (X : ContactFanoManifold n)
    (f : Source P sB ⟶ X.variety.scheme) (C : NonconstantFamily P sB X f) :
    NonconstantFamily P sA X (rationalSourceMap P u ≫ f) where
  curve t := C.curve ⟨t.val ≫ u.val, by rw [Category.assoc, u.property, t.property]⟩
  curve_spec t := by
    rw [← Category.assoc, inclusion_sourceMap]
    exact C.curve_spec _

/-- The entire square of a spread automorphism commutes with its
actual base-change map, including every diagonal point. -/
theorem squareMap_baseChange {A B : Scheme}
    (sA : A ⟶ ComplexBase) (sB : B ⟶ ComplexBase)
    (b : A ⟶ B) (k : Source P sA ⟶ Source P sB)
    (hk : k ≫ parameter P sB = parameter P sA ≫ b)
    (eA : Source P sA ≅ Source P sA)
    (heA : eA.hom ≫ parameter P sA = parameter P sA)
    (eB : Source P sB ≅ Source P sB)
    (heB : eB.hom ≫ parameter P sB = parameter P sB)
    (he : k ≫ eB.hom = eA.hom ≫ k) :
    RelativeSquare.map (parameter P sA) (parameter P sB) k b hk ≫
        squareMap P sB eB heB =
      squareMap P sA eA heA ≫
        RelativeSquare.map (parameter P sA) (parameter P sB) k b hk := by
  apply pullback.hom_ext
  · simp only [Category.assoc, squareMap_left, RelativeSquare.map_left,
      RelativeSquare.map_left_assoc, squareMap_left_assoc, he]
  · simp only [Category.assoc, squareMap_right, RelativeSquare.map_right,
      RelativeSquare.map_right_assoc, squareMap_right_assoc, he]

end FamilyReparametrization

end LeBrunSalamon.Construction.FamilyBivectors

end
