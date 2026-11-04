import RecompileExtensionsPart02

/-!
# Transport of a composed pullback section across an equality of schemes

The equality of the middle schemes is eliminated before any concrete scheme
or sheaf is substituted.  No new geometric assertion is used.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction.FamilySchemeTransport

theorem pull_comp_congr {T Y Y' Z : Scheme}
    (hY : Y = Y') (k : T ⟶ Y) (k' : T ⟶ Y') (hk : HEq k k')
    (f : Y ⟶ Z) (f' : Y' ⟶ Z) (hf : HEq f f')
    (r : T ⟶ Z) (h : k ≫ f = r) (h' : k' ≫ f' = r)
    (E : OModule Z)
    (s : AlgebraicSection (pullbackModule f E))
    (s' : AlgebraicSection (pullbackModule f' E)) (hs : HEq s s') :
    pullSection k s ≫ (compositionPullback k f r h E).hom =
      pullSection k' s' ≫ (compositionPullback k' f' r h' E).hom := by
  cases hY
  have hk' : k = k' := eq_of_heq hk
  subst k'
  have hf' : f = f' := eq_of_heq hf
  subst f'
  have hs' : s = s' := eq_of_heq hs
  subst s'
  rfl

set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety

theorem projective_selfProduct (P : ProjectiveLineOverC) :
    SelfProduct (projectiveLineVariety P).structureMap = SelfProduct P.structureMap := by
  rfl

theorem projective_pull_comp (P : ProjectiveLineOverC) {T Z : Scheme}
    (k : T ⟶ SelfProduct (projectiveLineVariety P).structureMap)
    (f : SelfProduct P.structureMap ⟶ Z)
    (r : T ⟶ Z) (h : k ≫ f = r) (E : OModule Z)
    (s : AlgebraicSection (pullbackModule f E)) :
    @pullSection T (SelfProduct (projectiveLineVariety P).structureMap) k
        (pullbackModule f E) s ≫
      (@compositionPullback T (SelfProduct (projectiveLineVariety P).structureMap) Z
        k f r h E).hom =
    @pullSection T (SelfProduct P.structureMap) k (pullbackModule f E) s ≫
      (@compositionPullback T (SelfProduct P.structureMap) Z k f r h E).hom := by
  exact pull_comp_congr (projective_selfProduct P)
    k k HEq.rfl f f HEq.rfl r h h E s s HEq.rfl

end LeBrunSalamon.Construction.FamilySchemeTransport

end
