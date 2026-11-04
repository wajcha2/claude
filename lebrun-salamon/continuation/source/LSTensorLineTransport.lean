import RecompileExtensionsPart02

/-! Pullback of a tensor line along two specified composite maps,
including the exact normalization on tensor-product sections. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.Construction

namespace LeBrunSalamon.TensorLineTransport

def comparison {T X Y Z : Scheme} (f : T ⟶ X)
    (u : X ⟶ Y) (v : X ⟶ Z) (u' : T ⟶ Y) (v' : T ⟶ Z)
    (hu : f ≫ u = u') (hv : f ≫ v = v') (E : OModule Y) (G : OModule Z) :
    pullbackModule f (tensorSheaf (pullbackModule u E) (pullbackModule v G)) ≅
      tensorSheaf (pullbackModule u' E) (pullbackModule v' G) := by
  letI := tensorPullbackComparison_isIso f (pullbackModule u E) (pullbackModule v G)
  exact (asIso (tensorPullbackComparison f (pullbackModule u E) (pullbackModule v G))).symm ≪≫
    tensorIso (compositionPullback f u u' hu E) (compositionPullback f v v' hv G)

theorem sections {T X Y Z : Scheme} (f : T ⟶ X)
    (u : X ⟶ Y) (v : X ⟶ Z) (u' : T ⟶ Y) (v' : T ⟶ Z)
    (hu : f ≫ u = u') (hv : f ≫ v = v')
    {E : OModule Y} {G : OModule Z} (a : AlgebraicSection E) (b : AlgebraicSection G) :
    pullSection f (tensorSection (pullSection u a) (pullSection v b)) ≫
      (comparison f u v u' v' hu hv E G).hom =
        tensorSection (pullSection u' a) (pullSection v' b) := by
  letI := tensorPullbackComparison_isIso f (pullbackModule u E) (pullbackModule v G)
  rw [← tensorPullbackComparison_onSections]
  change (tensorSection _ _ ≫ tensorPullbackComparison f _ _) ≫
    ((asIso (tensorPullbackComparison f _ _)).inv ≫ tensorMap _ _) = _
  change (tensorSection _ _ ≫ (asIso (tensorPullbackComparison f _ _)).hom) ≫
    ((asIso (tensorPullbackComparison f _ _)).inv ≫ tensorMap _ _) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc, tensorSection_map,
    compositionPullback_sections, compositionPullback_sections]

end LeBrunSalamon.TensorLineTransport
end
