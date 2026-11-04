import RecompileExtensionsPart03

/-! The actual line comparison on a given smooth rational fibre.
All comparisons are constructed from the proved degree classifier and
the actual pullback functor. No normal-form input is admitted. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton

namespace LeBrunSalamon.SmoothFibreComparison

theorem pullback_square_iso (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {Y : Scheme.{0}} (i : ProjectiveLine ≅ Y) (L : LineBundle Y)
    (H : LineBundle ProjectiveLine) (hH : projectiveLineDegree P p H = 1)
    (hL : projectiveLineDegree P p (pullbackLine i.hom L) = 2) :
    Nonempty (L.sheaf ≅ pullbackModule i.inv (tensorLine H H).sheaf) := by
  have hHH : projectiveLineDegree P p (tensorLine H H) = 2 := by
    rw [projectiveLineDegree_tensor, hH]
    norm_num
  obtain ⟨eL⟩ := projectiveLineDegree_spec P p (pullbackLine i.hom L)
  obtain ⟨eH⟩ := projectiveLineDegree_spec P p (tensorLine H H)
  rw [hL] at eL
  rw [hHH] at eH
  let a : pullbackModule i.hom L.sheaf ≅ (tensorLine H H).sheaf := eL ≪≫ eH.symm
  let c : pullbackModule i.inv (pullbackModule i.hom L.sheaf) ≅ L.sheaf :=
    (Scheme.Modules.pullbackComp i.inv i.hom).app L.sheaf ≪≫
        (Scheme.Modules.pullbackCongr i.inv_hom_id).app L.sheaf ≪≫
        (Scheme.Modules.pullbackId Y).app L.sheaf
  exact ⟨c.symm ≪≫ (Scheme.Modules.pullback i.inv).mapIso a⟩

theorem inverse_over (P : ProjectiveLineOverC) {Y : Scheme}
    (s : Y ⟶ ComplexBase) (i : ProjectiveLine ≅ Y)
    (hi : i.hom ≫ s = P.structureMap) : i.inv ≫ P.structureMap = s := by
  rw [← hi, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end LeBrunSalamon.SmoothFibreComparison

end
