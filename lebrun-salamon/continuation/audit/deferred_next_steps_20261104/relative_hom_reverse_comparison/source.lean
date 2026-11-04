import LSRelativeHomFunctorTranslationProbe

/-! Isolated, zero-new-admission reverse comparison for OBL051/054.
An actual all-test representer supplies its evaluation by the universal
element at the identity. The project universal map is proved to be the
representing equivalence, retaining the actual source base-change map.
No representability theorem or project conclusion is admitted here. -/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.Construction
open LeBrunSalamon.Construction.Smoothing
open LeBrunSalamon.RelativeMorphismsFunctorPrototype

namespace LeBrunSalamon.Next3i.RelativeHomConstruction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Naturality identifies every represented family with the actual
base change of the universal element, not an arbitrary set bijection. -/
theorem universalElement_map {S Y Z : Scheme} (pi : Y ⟶ S) (q : Z ⟶ S)
    (H : Over S) (R : (morphismFunctor pi q).RepresentableBy H)
    {T : Over S} (a : T ⟶ H) :
    (R.homEquiv a).left =
      sourceMap pi a ≫ (R.homEquiv (𝟙 H)).left := by
  have h := congrArg (fun g : sourceOver pi T ⟶ Over.mk q => g.left)
    (R.homEquiv_comp a (𝟙 H))
  simp only [Category.comp_id] at h
  change (R.homEquiv a).left =
    sourceMap pi a ≫ (R.homEquiv (𝟙 H)).left at h
  exact h

/-- An all-test representer gives the exact project presentation. -/
def ofRepresentation {S Y : Scheme} (pi : Y ⟶ S) (sS : S ⟶ ComplexBase)
    {d : ℕ} (X : SmoothProperComplexVariety d) (H : Over S)
    (R : (morphismFunctor pi (pullback.snd X.structureMap sS)).RepresentableBy H) :
    HomDeformationInput.Presentation pi sS X where
  parameter := H.left
  toBase := H.hom
  evaluation := (R.homEquiv (𝟙 H)).left ≫ pullback.fst X.structureMap sS
  overC := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have h := (R.homEquiv (𝟙 H)).w
    change (R.homEquiv (𝟙 H)).left ≫ pullback.snd X.structureMap sS =
      pullback.snd pi H.hom ≫ H.hom at h
    rw [h, Category.assoc]
  universal T t := by
    let e := (SectionRepresentability.overHomEquiv H T t).trans
      (R.homEquiv.trans (targetChangeEquiv pi sS X (Over.mk t)).symm)
    convert e.bijective using 1 <;> try rfl
    funext a
    apply Subtype.ext
    change HomDeformationInput.familyChange pi t H.hom a.val a.property ≫
        ((R.homEquiv (𝟙 H)).left ≫ pullback.fst X.structureMap sS) =
      (R.homEquiv (Over.homMk a.val a.property : Over.mk t ⟶ H)).left ≫
        pullback.fst X.structureMap sS
    rw [universalElement_map pi (pullback.snd X.structureMap sS) H R
      (Over.homMk a.val a.property : Over.mk t ⟶ H)]
    change sourceMap pi (Over.homMk a.val a.property : Over.mk t ⟶ H) ≫
        ((R.homEquiv (𝟙 H)).left ≫ pullback.fst X.structureMap sS) = _
    exact (Category.assoc _ _ _).symm

/-- The resulting evaluation is the actual universal family projected
from the base-changed target. -/
theorem ofRepresentation_evaluation {S Y : Scheme}
    (pi : Y ⟶ S) (sS : S ⟶ ComplexBase)
    {d : ℕ} (X : SmoothProperComplexVariety d) (H : Over S)
    (R : (morphismFunctor pi (pullback.snd X.structureMap sS)).RepresentableBy H) :
    (ofRepresentation pi sS X H R).evaluation =
      (R.homEquiv (𝟙 H)).left ≫ pullback.fst X.structureMap sS := rfl

end LeBrunSalamon.Next3i.RelativeHomConstruction

#print axioms LeBrunSalamon.Next3i.RelativeHomConstruction.universalElement_map
#print axioms LeBrunSalamon.Next3i.RelativeHomConstruction.ofRepresentation

end
