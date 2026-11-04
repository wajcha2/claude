import LSNodalTangent

/-! Isolated next-stage composition: the literal two-point generation
hypothesis interpolates actual first-order deformations. The production
source selection and accepted obligation ledger remain unchanged. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirty
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.Construction.Lines

namespace LeBrunSalamon.Next3i.TwoPointDeformations

theorem exists_deformation_section {Y : Scheme} {d : ℕ}
    (X : SmoothProperComplexVariety d) (sY : Y ⟶ ComplexBase)
    (f : Y ⟶ X.scheme) (hf : f ≫ X.structureMap = sY)
    (σ : AlgebraicSection (pullbackModule f (tangentSheaf X.structureMap))) :
    ∃ E : FamilyVariation.Deformation sY X.structureMap f, E.section X = σ := by
  obtain ⟨E, hE⟩ := (Normalization.NodalTangent.variation_bijective X hf).surjective
    (sectionValue σ)
  refine ⟨E, ?_⟩
  have h := congrArg sectionFromValue hE
  simpa only [FamilyVariation.Deformation.variation, sectionFromValue_sectionValue] using h

theorem deformation_eq_of_section_eq {Y : Scheme} {d : ℕ}
    (X : SmoothProperComplexVariety d) {sY : Y ⟶ ComplexBase}
    {f : Y ⟶ X.scheme} (hf : f ≫ X.structureMap = sY)
    (E F : FamilyVariation.Deformation sY X.structureMap f)
    (h : E.section X = F.section X) : E = F := by
  apply (Normalization.NodalTangent.variation_bijective X hf).injective
  exact congrArg sectionValue h

/-- Keep both unit and composition pullback normalizations explicit. -/
theorem normalized_restriction {Y Z W : Scheme} (p : Z ⟶ Y) (f : Y ⟶ W)
    (T : OModule W) (σ : AlgebraicSection (pullbackModule f T))
    (τ : AlgebraicSection (pullbackModule (p ≫ f) T))
    (h : restrictSection p σ = (unitPullbackIso p).hom ≫ τ ≫
      (compositionPullback p f (p ≫ f) rfl T).inv) :
    pullSection p σ ≫ (compositionPullback p f (p ≫ f) rfl T).hom = τ := by
  dsimp only [pullSection]
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id, Category.id_comp]

/-- Two arbitrary deformations at the two distinct marked points are
restrictions of a single actual deformation of the entire rational map. -/
theorem twoPointDeformations_surjective (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) (f : ProjectiveLine ⟶ X.scheme)
    (hf : f ≫ X.structureMap = P.structureMap)
    (hgen : IsTwoPointGloballyGenerated P
      (pullbackModule f (tangentSheaf X.structureMap)))
    (p q : ProjectiveLinePoint P) (hpq : p.map ≠ q.map) :
    Function.Surjective (fun E : FamilyVariation.Deformation P.structureMap X.structureMap f =>
      (E.pullback p.map p.overC, E.pullback q.map q.overC)) := by
  rintro ⟨Dp, Dq⟩
  let cp := compositionPullback p.map f (p.map ≫ f) rfl (tangentSheaf X.structureMap)
  let cq := compositionPullback q.map f (q.map ≫ f) rfl (tangentSheaf X.structureMap)
  obtain ⟨σ, hσ⟩ := hgen.2 p q hpq
    ((unitPullbackIso p.map).hom ≫ Dp.section X ≫ cp.inv,
      (unitPullbackIso q.map).hom ≫ Dq.section X ≫ cq.inv)
  have hp := congrArg Prod.fst hσ
  have hq := congrArg Prod.snd hσ
  obtain ⟨E, hE⟩ := exists_deformation_section X P.structureMap f hf σ
  refine ⟨E, Prod.ext ?_ ?_⟩
  · apply deformation_eq_of_section_eq X (by rw [Category.assoc, hf, p.overC])
    rw [← Normalization.NodalTangent.section_pullback, hE]
    exact normalized_restriction p.map f (tangentSheaf X.structureMap) σ (Dp.section X) hp
  · apply deformation_eq_of_section_eq X (by rw [Category.assoc, hf, q.overC])
    rw [← Normalization.NodalTangent.section_pullback, hE]
    exact normalized_restriction q.map f (tangentSheaf X.structureMap) σ (Dq.section X) hq

end LeBrunSalamon.Next3i.TwoPointDeformations

#print axioms LeBrunSalamon.Next3i.TwoPointDeformations.twoPointDeformations_surjective

end
