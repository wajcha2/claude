import RecompileExtensionsPart01
import LSRelativeHomCoreComparisonProbe

/-! Isolated categorical comparison for the original absolute Hom contract.
The relative-morphism functor is used with the target's actual structure map.
Only the pullback base equation changes between the Over and project notation.
There is no assertion that a representer exists. -/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.Skeleton
open LeBrunSalamon.RelativeMorphismsFunctor

namespace LeBrunSalamon.Next3i.AbsoluteHomEarlyConstruction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The two displayed base conditions agree by the actual pullback square. -/
def familyEquiv (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) (T : Over ComplexBase) :
    (sourceOver P.structureMap T ⟶ Over.mk X.structureMap) ≃
      PointsOver (RationalSourceOver P T.left T.hom)
        (pullback.fst P.structureMap T.hom ≫ P.structureMap)
        X.scheme X.structureMap where
  toFun g := ⟨g.left, g.w.trans (pullback.condition (f := P.structureMap)
    (g := T.hom)).symm⟩
  invFun f := Over.homMk f.val
    (f.property.trans (pullback.condition (f := P.structureMap) (g := T.hom)))
  left_inv g := by
    apply Over.OverMorphism.ext
    rfl
  right_inv f := by
    apply Subtype.ext
    rfl

/-- The original HomSpacePresentation, with its actual universal map on every
test scheme, follows from a representer of the genuine Hom functor. -/
def ofRepresentation (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) (H : Over ComplexBase)
    (R : (morphismFunctor P.structureMap X.structureMap).RepresentableBy H) :
    HomSpacePresentation P X where
  parameter := H.left
  toC := H.hom
  evaluation := (R.homEquiv (𝟙 H)).left
  overC := (R.homEquiv (𝟙 H)).w.trans
    (pullback.condition (f := P.structureMap) (g := H.hom)).symm
  universal T sT := by
    let e := (LeBrunSalamon.RelativeMorphismsFunctor.overHomEquiv H T sT).trans
      (R.homEquiv.trans (familyEquiv P X (Over.mk sT)))
    convert e.bijective using 1 <;> try rfl
    funext a
    apply Subtype.ext
    change rationalSourceMap P a ≫ (R.homEquiv (𝟙 H)).left =
      (R.homEquiv (Over.homMk a.val a.property : Over.mk sT ⟶ H)).left
    exact (universalElement_map P.structureMap X.structureMap H R
      (Over.homMk a.val a.property : Over.mk sT ⟶ H)).symm

end LeBrunSalamon.Next3i.AbsoluteHomEarlyConstruction

#print axioms LeBrunSalamon.Next3i.AbsoluteHomEarlyConstruction.familyEquiv
#print axioms LeBrunSalamon.Next3i.AbsoluteHomEarlyConstruction.ofRepresentation

end
