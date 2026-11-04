import LSRelativeDifferential

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.Skeleton.ContactDerivativeIsoProof

namespace LeBrunSalamon.Construction.FamilyDerivativeRestriction

/-- Restriction of a dualized pullback map along a genuine section.
All three cotangent modules and maps are arbitrary here. -/
theorem section_morphism {A B X : Scheme}
    (j : A ⟶ B) (p : B ⟶ A) (e : B ⟶ X) (hj : j ≫ p = 𝟙 A)
    (E : OModule A) (F : OModule X)
    (r : pullbackModule e F ⟶ pullbackModule p E)
    (f : pullbackModule (j ≫ e) F ⟶ E)
    [IsIso (dualBaseChange e F)] [IsIso (dualBaseChange (j ≫ e) F)]
    (hr : (Scheme.Modules.pullback j).map r ≫
        (RelativeDifferential.sectionPullbackIso j p hj E).hom =
      (Scheme.Modules.pullbackComp j e).hom.app F ≫ f) :
    (RelativeDifferential.sectionPullbackIso j p hj (dualSheaf E)).inv ≫
      (Scheme.Modules.pullback j).map
        (dualBaseChange p E ≫ dualMap r ≫ inv (dualBaseChange e F)) ≫
      (Scheme.Modules.pullbackComp j e).hom.app (dualSheaf F) =
        dualMap f ≫ inv (dualBaseChange (j ≫ e) F) := by
  let S := RelativeDifferential.sectionPullbackIso j p hj (dualSheaf E)
  apply (cancel_epi S.hom).mp
  simp only [← Category.assoc, S, Iso.hom_inv_id, Category.id_comp]
  apply (cancel_mono (dualBaseChange (j ≫ e) F)).mp
  simp only [Functor.map_comp, Functor.map_inv, Category.assoc,
    IsIso.inv_hom_id, Category.comp_id]
  rw [dualBaseChange_comp]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  rw [dualBaseChange_naturality_assoc]
  rw [← Category.assoc, RelativeDifferential.dualBaseChange_section j p hj E]
  simp only [Category.assoc, ← dualMap_comp]
  have ht := congrArg (fun k : pullbackModule j (pullbackModule e F) ⟶ E =>
    (Scheme.Modules.pullbackComp j e).inv.app F ≫ k) hr
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at ht
  simp only [Category.assoc] at ht
  rw [ht]

end LeBrunSalamon.Construction.FamilyDerivativeRestriction

end
