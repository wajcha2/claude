import LSFamilyDescentFibres

/-!
# Source reparametrization and its canonical external comparison.

This namespace block is extracted verbatim from the candidate descent
source. Public names, statements and proof bodies are retained. The preceding
transport blocks are imported so each completed native output can be reused.
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

namespace LeBrunSalamon.Construction.FamilyBivectors


-- Normalize the existing P1/contact carrier aliases for the same actual maps.
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety identityCurveContact intrinsicTangentBundle

namespace Reparametrization

variable (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
variable (he : e.hom ≫ P.structureMap = P.structureMap)

theorem mixedPull_product {E F : OModule ProjectiveLine}
    (a : AlgebraicSection E) (b : AlgebraicSection F) :
    mixedPull P e he E F (externalProductSection P.structureMap a b) =
      externalProductSection P.structureMap (pullSection e.hom a) (pullSection e.hom b) := by
  letI := curveExternalComparison_isIso P (curve P e he) E F
  apply (cancel_mono (curveExternalComparison P (curve P e he) E F)).mp
  rw [mixedPull_comparison]
  exact (curveExternalComparison_onProducts P (curve P e he) a b).symm

theorem mixedPull_sum {E F : OModule ProjectiveLine} {N : ℕ}
    (a : Fin N → AlgebraicSection (externalTensor P.structureMap E F)) :
    mixedPull P e he E F (∑ i, a i) = ∑ i, mixedPull P e he E F (a i) := by
  simp only [mixedPull, SectionTransport.pull_sum, Preadditive.sum_comp]

variable {n : ℕ} (X : ContactFanoManifold n) (f g : RationalCurve P X.variety)
variable (hg : g.map = e.hom ≫ f.map)

include hg in
@[reassoc] theorem square_comp :
    curveSquareMap P (curve P e he) ≫ curveSquareMap P f = curveSquareMap P g := by
  apply pullback.hom_ext
  · rw [Category.assoc, curveSquareMap_first, ← Category.assoc,
      curveSquareMap_first, curveSquareMap_first]
    change (firstProjection P.structureMap ≫ e.hom) ≫ f.map =
      firstProjection P.structureMap ≫ g.map
    rw [Category.assoc, hg]
  · rw [Category.assoc, curveSquareMap_second, ← Category.assoc,
      curveSquareMap_second, curveSquareMap_second]
    change (secondProjection P.structureMap ≫ e.hom) ≫ f.map =
      secondProjection P.structureMap ≫ g.map
    rw [Category.assoc, hg]

/-- Comparison with the target external bundle commutes with an
actual source reparametrization. A finite expansion is used only to
prove canonical tensor coherence; the tensor itself remains fixed. -/
theorem compared_of_expansion {E F : OModule X.variety.scheme}
    (B : AlgebraicSection (externalTensor P.structureMap
      (pullbackModule f.map E) (pullbackModule f.map F)))
    {N : ℕ} (a : Fin N → AlgebraicSection (pullbackModule f.map E))
    (b : Fin N → AlgebraicSection (pullbackModule f.map F))
    (hB : B = ∑ i, externalProductSection P.structureMap (a i) (b i)) :
    pullSection (curveSquareMap P (curve P e he))
        (B ≫ curveExternalComparison P f E F) ≫
      (compositionPullback (curveSquareMap P (curve P e he)) (curveSquareMap P f)
        (curveSquareMap P g) (square_comp P e he X f g hg)
        (externalTensor X.variety.structureMap E F)).hom =
      (mixedPull P e he (pullbackModule f.map E) (pullbackModule f.map F) B ≫
        externalTensorMap P.structureMap
          (compositionPullback e.hom f.map g.map hg.symm E).hom
          (compositionPullback e.hom f.map g.map hg.symm F).hom) ≫
        curveExternalComparison P g E F := by
  rw [hB, mixedPull_sum]
  simp only [Preadditive.sum_comp, SectionTransport.pull_sum, mixedPull_product]
  apply Finset.sum_congr rfl
  intro i hi
  have hp := RelativeSquare.product_atCurve P.structureMap P X.variety
    (𝟙 ComplexBase) f.map (by simpa only [Category.comp_id] using f.overC)
    e.hom g hg.symm (curveSquareMap P (curve P e he))
    (curveSquareMap_first P (curve P e he))
    (curveSquareMap_second P (curve P e he))
    (square_comp P e he X f g hg) (a i) (b i)
    (pullSection e.hom (a i) ≫ (compositionPullback e.hom f.map g.map hg.symm E).hom)
    (pullSection e.hom (b i) ≫ (compositionPullback e.hom f.map g.map hg.symm F).hom)
    rfl rfl
  simpa only [externalProductSection, externalTensorMap, tensorSection_map,
    pullSection_naturality] using hp

/-- Reparametrization invariance in the actual target bundle, including
all the canonical composition and external-product comparisons. -/
theorem leftSection :
    pullSection (curveSquareMap P (curve P e he)) (Curve.leftSection P X f) ≫
      (compositionPullback (curveSquareMap P (curve P e he)) (curveSquareMap P f)
        (curveSquareMap P g) (square_comp P e he X f g hg)
        (movingPairBundleLeft X.variety X.contact)).hom = Curve.leftSection P X g := by
  obtain ⟨E⟩ := externalExpansion_exists (projectiveLineVariety P)
    (identityCurveContact P).sequence.line (sourceBivector P)
  have hB : Curve.leftRaw P X f = ∑ i,
      externalProductSection P.structureMap
        (E.left i ≫ Curve.differential P X f)
        (E.right i ≫ curveContactVelocity P X.contact f) := by
    rw [Curve.leftRaw]
    conv_lhs => rw [E.equation]
    simp only [Preadditive.sum_comp, externalProductSection, externalTensorMap,
      tensorSection_map, pullSection_naturality]
  rw [Curve.leftSection, compared_of_expansion P e he X f g hg
    (Curve.leftRaw P X f) _ _ hB, leftRaw P e he X f g hg]
  rfl

theorem rightSection :
    pullSection (curveSquareMap P (curve P e he)) (Curve.rightSection P X f) ≫
      (compositionPullback (curveSquareMap P (curve P e he)) (curveSquareMap P f)
        (curveSquareMap P g) (square_comp P e he X f g hg)
        (movingPairBundleRight X.variety X.contact)).hom = Curve.rightSection P X g := by
  obtain ⟨E⟩ := externalExpansion_exists (projectiveLineVariety P)
    (identityCurveContact P).sequence.line (sourceBivector P)
  have hB : Curve.rightRaw P X f = ∑ i,
      externalProductSection P.structureMap
        (E.left i ≫ curveContactVelocity P X.contact f)
        (E.right i ≫ Curve.differential P X f) := by
    rw [Curve.rightRaw]
    conv_lhs => rw [E.equation]
    simp only [Preadditive.sum_comp, externalProductSection, externalTensorMap,
      tensorSection_map, pullSection_naturality]
  rw [Curve.rightSection, compared_of_expansion P e he X f g hg
    (Curve.rightRaw P X f) _ _ hB, rightRaw P e he X f g hg]
  rfl

end Reparametrization

end LeBrunSalamon.Construction.FamilyBivectors

end
