import LSFamilyDescentTransport

/-!
# Direct canonical product transport on a rational curve

These proofs use the literal curve-square map and its fixed external
comparison throughout. They expand the generic tensor/coherence proof
without first identifying a relative-square presentation with that map.
No additional geometric or algebraic input is admitted here.
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
open LeBrunSalamon.PhaseTwentyEight.ExternalExchangeCoherenceProof

namespace LeBrunSalamon.Construction.FamilyBivectors.CurveProductDirect

theorem product_comparison (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) (f : RationalCurve P X)
    {E F : OModule X.scheme}
    (a : AlgebraicSection (pullbackModule f.map E))
    (b : AlgebraicSection (pullbackModule f.map F)) :
    externalProductSection P.structureMap a b ≫ curveExternalComparison P f E F =
      SectionTransport.tensor (curveSquareMap P f)
        (pullSection (firstProjection P.structureMap) a ≫
          (pullbackSquareIso (firstProjection P.structureMap) f.map
            (curveSquareMap P f) (firstProjection X.structureMap)
            (curveSquareMap_first P f).symm E).hom)
        (pullSection (secondProjection P.structureMap) b ≫
          (pullbackSquareIso (secondProjection P.structureMap) f.map
            (curveSquareMap P f) (secondProjection X.structureMap)
            (curveSquareMap_second P f).symm F).hom) := by
  unfold externalProductSection curveExternalComparison SectionTransport.tensor
  rw [← Category.assoc, tensorSection_map]

theorem product_pullback (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) (f : RationalCurve P X)
    {T : Scheme} (q : T ⟶ SelfProduct P.structureMap)
    (r : T ⟶ SelfProduct X.structureMap)
    (hqr : q ≫ curveSquareMap P f = r)
    (x₁ x₂ : T ⟶ X.scheme)
    (hx₁ : r ≫ firstProjection X.structureMap = x₁)
    (hx₂ : r ≫ secondProjection X.structureMap = x₂)
    (hq₁ : (q ≫ firstProjection P.structureMap) ≫ f.map = x₁)
    (hq₂ : (q ≫ secondProjection P.structureMap) ≫ f.map = x₂)
    {E F : OModule X.scheme}
    (a : AlgebraicSection (pullbackModule f.map E))
    (b : AlgebraicSection (pullbackModule f.map F)) :
    pullSection q (externalProductSection P.structureMap a b ≫
      curveExternalComparison P f E F) ≫
        (compositionPullback q (curveSquareMap P f) r hqr
          (externalTensor X.structureMap E F)).hom ≫
        (Descent.LineValue.externalAlongIso X.structureMap r x₁ x₂ hx₁ hx₂ E F).inv =
      tensorSection
        (pullSection (q ≫ firstProjection P.structureMap) a ≫
          (compositionPullback (q ≫ firstProjection P.structureMap) f.map x₁ hq₁ E).hom)
        (pullSection (q ≫ secondProjection P.structureMap) b ≫
          (compositionPullback (q ≫ secondProjection P.structureMap) f.map x₂ hq₂ F).hom) := by
  letI := tensorPullbackComparison_isIso r
    (pullbackModule (firstProjection X.structureMap) E)
    (pullbackModule (secondProjection X.structureMap) F)
  rw [product_comparison, ← Category.assoc]
  erw [SectionTransport.tensor_pullback q (curveSquareMap P f) r hqr
    (E := pullbackModule (firstProjection X.structureMap) E)
    (F := pullbackModule (secondProjection X.structureMap) F)]
  simp only [SectionTransport.tensor, Descent.LineValue.externalAlongIso,
    Iso.trans_inv, Iso.symm_inv, tensorIso, asIso_inv,
    Category.assoc, IsIso.hom_inv_id_assoc]
  rw [tensorSection_map]
  congr 1
  · rw [pullSection_naturality]
    simp only [Category.assoc]
    rw [SectionTransport.square_comp q (firstProjection P.structureMap) f.map
      (curveSquareMap P f) (firstProjection X.structureMap)
      (curveSquareMap_first P f).symm r hqr x₁ hx₁ hq₁ E,
      ← Category.assoc, compositionPullback_sections]
  · rw [pullSection_naturality]
    simp only [Category.assoc]
    rw [SectionTransport.square_comp q (secondProjection P.structureMap) f.map
      (curveSquareMap P f) (secondProjection X.structureMap)
      (curveSquareMap_second P f).symm r hqr x₂ hx₂ hq₂ F,
      ← Category.assoc, compositionPullback_sections]

theorem product_normalize (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) (f : RationalCurve P X)
    {E F : OModule X.scheme}
    (a : AlgebraicSection (pullbackModule f.map E))
    (b : AlgebraicSection (pullbackModule f.map F)) :
    (externalProductSection P.structureMap a b ≫ curveExternalComparison P f E F) ≫
        (Descent.LineValue.externalAlongIso X.structureMap
          (curveSquareMap P f) (firstProjection P.structureMap ≫ f.map)
          (secondProjection P.structureMap ≫ f.map)
          (curveSquareMap_first P f) (curveSquareMap_second P f) E F).inv =
      tensorSection
        (pullSection (firstProjection P.structureMap) a ≫
          (compositionPullback (firstProjection P.structureMap) f.map
            (firstProjection P.structureMap ≫ f.map) rfl E).hom)
        (pullSection (secondProjection P.structureMap) b ≫
          (compositionPullback (secondProjection P.structureMap) f.map
            (secondProjection P.structureMap ≫ f.map) rfl F).hom) := by
  letI := tensorPullbackComparison_isIso (curveSquareMap P f)
    (pullbackModule (firstProjection X.structureMap) E)
    (pullbackModule (secondProjection X.structureMap) F)
  rw [product_comparison]
  simp only [SectionTransport.tensor, Descent.LineValue.externalAlongIso,
    Iso.trans_inv, Iso.symm_inv, tensorIso, asIso_inv,
    Category.assoc, IsIso.hom_inv_id_assoc]
  rw [tensorSection_map]
  congr 1
  · rw [Category.assoc]
    apply congrArg (fun h => pullSection (firstProjection P.structureMap) a ≫ h)
    simp [pullbackSquareIso, compositionPullback, Category.assoc]
  · rw [Category.assoc]
    apply congrArg (fun h => pullSection (secondProjection P.structureMap) b ≫ h)
    simp [pullbackSquareIso, compositionPullback, Category.assoc]

theorem product_atCurve (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) (f g : RationalCurve P X)
    (j : ProjectiveLine ⟶ ProjectiveLine) (hfg : j ≫ f.map = g.map)
    (k : SelfProduct P.structureMap ⟶ SelfProduct P.structureMap)
    (hk₁ : k ≫ firstProjection P.structureMap = firstProjection P.structureMap ≫ j)
    (hk₂ : k ≫ secondProjection P.structureMap = secondProjection P.structureMap ≫ j)
    (hk : k ≫ curveSquareMap P f = curveSquareMap P g)
    {E F : OModule X.scheme}
    (a : AlgebraicSection (pullbackModule f.map E))
    (b : AlgebraicSection (pullbackModule f.map F))
    (a₀ : AlgebraicSection (pullbackModule g.map E))
    (b₀ : AlgebraicSection (pullbackModule g.map F))
    (ha : pullSection j a ≫ (compositionPullback j f.map g.map hfg E).hom = a₀)
    (hb : pullSection j b ≫ (compositionPullback j f.map g.map hfg F).hom = b₀) :
    pullSection k (externalProductSection P.structureMap a b ≫
      curveExternalComparison P f E F) ≫
        (compositionPullback k (curveSquareMap P f) (curveSquareMap P g) hk
          (externalTensor X.structureMap E F)).hom =
      externalProductSection P.structureMap a₀ b₀ ≫ curveExternalComparison P g E F := by
  let A := Descent.LineValue.externalAlongIso X.structureMap (curveSquareMap P g)
    (firstProjection P.structureMap ≫ g.map) (secondProjection P.structureMap ≫ g.map)
    (curveSquareMap_first P g) (curveSquareMap_second P g) E F
  have hke₁ : (k ≫ firstProjection P.structureMap) ≫ f.map =
      firstProjection P.structureMap ≫ g.map := by
    rw [hk₁, Category.assoc, hfg]
  have hke₂ : (k ≫ secondProjection P.structureMap) ≫ f.map =
      secondProjection P.structureMap ≫ g.map := by
    rw [hk₂, Category.assoc, hfg]
  apply (cancel_mono A.inv).mp
  rw [Category.assoc]
  rw [product_pullback P X f k (curveSquareMap P g) hk
    (firstProjection P.structureMap ≫ g.map) (secondProjection P.structureMap ≫ g.map)
    (curveSquareMap_first P g) (curveSquareMap_second P g) hke₁ hke₂ a b]
  have ha' := SectionTransport.pull_specialization
    (firstProjection P.structureMap) j f.map (k ≫ firstProjection P.structureMap)
    g.map (firstProjection P.structureMap ≫ g.map) hk₁.symm hfg rfl hke₁ a a₀ ha
  have hb' := SectionTransport.pull_specialization
    (secondProjection P.structureMap) j f.map (k ≫ secondProjection P.structureMap)
    g.map (secondProjection P.structureMap ≫ g.map) hk₂.symm hfg rfl hke₂ b b₀ hb
  rw [ha', hb']
  exact (product_normalize P X g a₀ b₀).symm

end LeBrunSalamon.Construction.FamilyBivectors.CurveProductDirect

end
