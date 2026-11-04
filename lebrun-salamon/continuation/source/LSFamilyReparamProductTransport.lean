import LSFamilyCurveProductDirect
import LSFamilyExternalProductMap
import LSFamilySchemeTransport

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

namespace LeBrunSalamon.Construction.FamilyBivectors.ReparametrizationProductTransport

open LeBrunSalamon.Construction.FamilyBivectors.Reparametrization

set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety identityCurveContact intrinsicTangentBundle

theorem object_transport (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap)
    {n : ℕ} (X : ContactFanoManifold n) (f g : RationalCurve P X.variety)
    (hg : g.map = e.hom ≫ f.map)
    (hk : curveSquareMap P (curve P e he) ≫ curveSquareMap P f = curveSquareMap P g)
    {E F : OModule X.variety.scheme}
    (a : AlgebraicSection (pullbackModule f.map E))
    (b : AlgebraicSection (pullbackModule f.map F)) :
   pullSection (curveSquareMap P (curve P e he))
        (externalProductSection P.structureMap a b ≫ curveExternalComparison P f E F) ≫
      (compositionPullback (curveSquareMap P (curve P e he)) (curveSquareMap P f)
        (curveSquareMap P g) hk (externalTensor X.variety.structureMap E F)).hom =
    @pullSection (SelfProduct P.structureMap) (SelfProduct P.structureMap)
        (curveSquareMap P (curve P e he))
        (pullbackModule (curveSquareMap P f) (externalTensor X.variety.structureMap E F))
        (externalProductSection P.structureMap a b ≫ curveExternalComparison P f E F) ≫
      (@compositionPullback (SelfProduct P.structureMap) (SelfProduct P.structureMap)
        (SelfProduct X.variety.structureMap) (curveSquareMap P (curve P e he))
        (curveSquareMap P f) (curveSquareMap P g) hk
        (externalTensor X.variety.structureMap E F)).hom := by
  exact FamilySchemeTransport.projective_pull_comp P
    (curveSquareMap P (curve P e he)) (curveSquareMap P f) (curveSquareMap P g)
    hk (externalTensor X.variety.structureMap E F)
    (externalProductSection P.structureMap a b ≫ curveExternalComparison P f E F)

theorem direct_product (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap)
    {n : ℕ} (X : ContactFanoManifold n) (f g : RationalCurve P X.variety)
    (hg : g.map = e.hom ≫ f.map)
    (hk : curveSquareMap P (curve P e he) ≫ curveSquareMap P f = curveSquareMap P g)
    {E F : OModule X.variety.scheme}
    (a : AlgebraicSection (pullbackModule f.map E))
    (b : AlgebraicSection (pullbackModule f.map F)) :
    @pullSection (SelfProduct P.structureMap) (SelfProduct P.structureMap)
        (curveSquareMap P (curve P e he))
        (pullbackModule (curveSquareMap P f) (externalTensor X.variety.structureMap E F))
        (externalProductSection P.structureMap a b ≫ curveExternalComparison P f E F) ≫
      (@compositionPullback (SelfProduct P.structureMap) (SelfProduct P.structureMap)
        (SelfProduct X.variety.structureMap) (curveSquareMap P (curve P e he))
        (curveSquareMap P f) (curveSquareMap P g) hk
        (externalTensor X.variety.structureMap E F)).hom =
    externalProductSection P.structureMap
      (pullSection e.hom a ≫ (compositionPullback e.hom f.map g.map hg.symm E).hom)
      (pullSection e.hom b ≫ (compositionPullback e.hom f.map g.map hg.symm F).hom) ≫
        curveExternalComparison P g E F := by
  let k : SelfProduct P.structureMap ⟶ SelfProduct P.structureMap :=
    curveSquareMap P (curve P e he)
  have hk₁ : k ≫ firstProjection P.structureMap =
      firstProjection P.structureMap ≫ e.hom :=
    curveSquareMap_first P (curve P e he)
  have hk₂ : k ≫ secondProjection P.structureMap =
      secondProjection P.structureMap ≫ e.hom :=
    curveSquareMap_second P (curve P e he)
  have hk' : k ≫ curveSquareMap P f = curveSquareMap P g := hk
  exact CurveProductDirect.product_atCurve P X.variety f g e.hom
    hg.symm k hk₁ hk₂ hk' a b
    (pullSection e.hom a ≫ (compositionPullback e.hom f.map g.map hg.symm E).hom)
    (pullSection e.hom b ≫ (compositionPullback e.hom f.map g.map hg.symm F).hom)
    rfl rfl

theorem map_product (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap)
    {n : ℕ} (X : ContactFanoManifold n) (f g : RationalCurve P X.variety)
    (hg : g.map = e.hom ≫ f.map)
    (hk : curveSquareMap P (curve P e he) ≫ curveSquareMap P f = curveSquareMap P g)
    {E F : OModule X.variety.scheme}
    (a : AlgebraicSection (pullbackModule f.map E))
    (b : AlgebraicSection (pullbackModule f.map F)) :
    externalProductSection P.structureMap
      (pullSection e.hom a ≫ (compositionPullback e.hom f.map g.map hg.symm E).hom)
      (pullSection e.hom b ≫ (compositionPullback e.hom f.map g.map hg.symm F).hom) ≫
        curveExternalComparison P g E F =
     (externalProductSection P.structureMap (pullSection e.hom a) (pullSection e.hom b) ≫
        externalTensorMap P.structureMap
          (compositionPullback e.hom f.map g.map hg.symm E).hom
          (compositionPullback e.hom f.map g.map hg.symm F).hom) ≫
        curveExternalComparison P g E F := by
  have hm := congrArg
    (fun q : AlgebraicSection (externalTensor P.structureMap
        (pullbackModule g.map E) (pullbackModule g.map F)) =>
      q ≫ curveExternalComparison P g E F)
    (ExternalProductFunctoriality.product_map P.structureMap
      (pullSection e.hom a) (pullSection e.hom b)
      (compositionPullback e.hom f.map g.map hg.symm E).hom
      (compositionPullback e.hom f.map g.map hg.symm F).hom)
  exact hm.symm

theorem comparison (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap)
    {n : ℕ} (X : ContactFanoManifold n) (f g : RationalCurve P X.variety)
    (hg : g.map = e.hom ≫ f.map)
    (hk : curveSquareMap P (curve P e he) ≫ curveSquareMap P f = curveSquareMap P g)
    {E F : OModule X.variety.scheme}
    (a : AlgebraicSection (pullbackModule f.map E))
    (b : AlgebraicSection (pullbackModule f.map F)) :
   pullSection (curveSquareMap P (curve P e he))
        (externalProductSection P.structureMap a b ≫ curveExternalComparison P f E F) ≫
      (compositionPullback (curveSquareMap P (curve P e he)) (curveSquareMap P f)
        (curveSquareMap P g) hk (externalTensor X.variety.structureMap E F)).hom =
      (externalProductSection P.structureMap (pullSection e.hom a) (pullSection e.hom b) ≫
        externalTensorMap P.structureMap
          (compositionPullback e.hom f.map g.map hg.symm E).hom
          (compositionPullback e.hom f.map g.map hg.symm F).hom) ≫
        curveExternalComparison P g E F := by
  exact (object_transport P e he X f g hg hk a b).trans
    ((direct_product P e he X f g hg hk a b).trans
      (map_product P e he X f g hg hk a b))

end LeBrunSalamon.Construction.FamilyBivectors.ReparametrizationProductTransport

end
