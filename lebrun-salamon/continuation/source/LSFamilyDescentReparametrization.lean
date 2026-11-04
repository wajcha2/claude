import LSFamilyReparamExpansionStages

/-!
# The two actual target-section reparametrization identities.

The comparison prefix is imported byte-for-byte. Each final identity uses
closed comparison, raw-tensor transport, and definition equalities.
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

variable {n : ℕ} (X : ContactFanoManifold n) (f g : RationalCurve P X.variety)
variable (hg : g.map = e.hom ≫ f.map)

namespace FinalSectionProof

theorem left_raw_expansion
    (E : ExternalExpansion (projectiveLineVariety P)
      (identityCurveContact P).sequence.line (sourceBivector P)) :
    Curve.leftRaw P X f = ∑ i,
      externalProductSection P.structureMap
        (E.left i ≫ Curve.differential P X f)
        (E.right i ≫ curveContactVelocity P X.contact f) := by
  letI := curveExternalComparison_isIso P f
    (tangentSheaf X.variety.structureMap) X.contact.sequence.line.sheaf
  apply (cancel_mono (curveExternalComparison P f
    (tangentSheaf X.variety.structureMap) X.contact.sequence.line.sheaf)).mp
  simpa only [Curve.leftSection, Preadditive.sum_comp] using
    Curve.leftSection_expansion P X f E

theorem left_comparison
    (A : ExternalExpansion (projectiveLineVariety P)
      (identityCurveContact P).sequence.line (sourceBivector P)) :
    pullSection (curveSquareMap P (curve P e he)) (Curve.leftSection P X f) ≫
      (compositionPullback (curveSquareMap P (curve P e he)) (curveSquareMap P f)
        (curveSquareMap P g) (square_comp P e he X f g hg)
        (movingPairBundleLeft X.variety X.contact)).hom =
    (mixedPull P e he (pullbackModule f.map (tangentSheaf X.variety.structureMap))
        (pullbackModule f.map X.contact.sequence.line.sheaf) (Curve.leftRaw P X f) ≫
      externalTensorMap P.structureMap
        (compositionPullback e.hom f.map g.map hg.symm (tangentSheaf X.variety.structureMap)).hom
        (compositionPullback e.hom f.map g.map hg.symm X.contact.sequence.line.sheaf).hom) ≫
      curveExternalComparison P g (tangentSheaf X.variety.structureMap) X.contact.sequence.line.sheaf := by
  exact compared_of_expansion P e he X f g hg
    (E := (tangentSheaf X.variety.structureMap)) (F := X.contact.sequence.line.sheaf)
    (Curve.leftRaw P X f) (N := A.size)
    (fun i => A.left i ≫ Curve.differential P X f)
    (fun i => A.right i ≫ curveContactVelocity P X.contact f)
    (left_raw_expansion P X f A)

theorem left_transport :
    (mixedPull P e he (pullbackModule f.map (tangentSheaf X.variety.structureMap))
        (pullbackModule f.map X.contact.sequence.line.sheaf) (Curve.leftRaw P X f) ≫
      externalTensorMap P.structureMap
        (compositionPullback e.hom f.map g.map hg.symm (tangentSheaf X.variety.structureMap)).hom
        (compositionPullback e.hom f.map g.map hg.symm X.contact.sequence.line.sheaf).hom) ≫
      curveExternalComparison P g (tangentSheaf X.variety.structureMap) X.contact.sequence.line.sheaf =
    Curve.leftRaw P X g ≫
      curveExternalComparison P g (tangentSheaf X.variety.structureMap) X.contact.sequence.line.sheaf := by
  exact congrArg
    (fun q : AlgebraicSection (externalTensor P.structureMap
        (pullbackModule g.map (tangentSheaf X.variety.structureMap)) (pullbackModule g.map X.contact.sequence.line.sheaf)) =>
      q ≫ curveExternalComparison P g (tangentSheaf X.variety.structureMap) X.contact.sequence.line.sheaf)
    (LeBrunSalamon.Construction.FamilyBivectors.Reparametrization.leftRaw
      P e he X f g hg)

theorem left_definition :
    Curve.leftRaw P X g ≫
      curveExternalComparison P g (tangentSheaf X.variety.structureMap) X.contact.sequence.line.sheaf = Curve.leftSection P X g := by
  rfl

theorem right_raw_expansion
    (E : ExternalExpansion (projectiveLineVariety P)
      (identityCurveContact P).sequence.line (sourceBivector P)) :
    Curve.rightRaw P X f = ∑ i,
      externalProductSection P.structureMap
        (E.left i ≫ curveContactVelocity P X.contact f)
        (E.right i ≫ Curve.differential P X f) := by
  letI := curveExternalComparison_isIso P f
    X.contact.sequence.line.sheaf (tangentSheaf X.variety.structureMap)
  apply (cancel_mono (curveExternalComparison P f
    X.contact.sequence.line.sheaf (tangentSheaf X.variety.structureMap))).mp
  simpa only [Curve.rightSection, Preadditive.sum_comp] using
    Curve.rightSection_expansion P X f E

theorem right_comparison
    (A : ExternalExpansion (projectiveLineVariety P)
      (identityCurveContact P).sequence.line (sourceBivector P)) :
    pullSection (curveSquareMap P (curve P e he)) (Curve.rightSection P X f) ≫
      (compositionPullback (curveSquareMap P (curve P e he)) (curveSquareMap P f)
        (curveSquareMap P g) (square_comp P e he X f g hg)
        (movingPairBundleRight X.variety X.contact)).hom =
    (mixedPull P e he (pullbackModule f.map X.contact.sequence.line.sheaf)
        (pullbackModule f.map (tangentSheaf X.variety.structureMap)) (Curve.rightRaw P X f) ≫
      externalTensorMap P.structureMap
        (compositionPullback e.hom f.map g.map hg.symm X.contact.sequence.line.sheaf).hom
        (compositionPullback e.hom f.map g.map hg.symm (tangentSheaf X.variety.structureMap)).hom) ≫
      curveExternalComparison P g X.contact.sequence.line.sheaf (tangentSheaf X.variety.structureMap) := by
  exact compared_of_expansion P e he X f g hg
    (E := X.contact.sequence.line.sheaf) (F := (tangentSheaf X.variety.structureMap))
    (Curve.rightRaw P X f) (N := A.size)
    (fun i => A.left i ≫ curveContactVelocity P X.contact f)
    (fun i => A.right i ≫ Curve.differential P X f)
    (right_raw_expansion P X f A)

theorem right_transport :
    (mixedPull P e he (pullbackModule f.map X.contact.sequence.line.sheaf)
        (pullbackModule f.map (tangentSheaf X.variety.structureMap)) (Curve.rightRaw P X f) ≫
      externalTensorMap P.structureMap
        (compositionPullback e.hom f.map g.map hg.symm X.contact.sequence.line.sheaf).hom
        (compositionPullback e.hom f.map g.map hg.symm (tangentSheaf X.variety.structureMap)).hom) ≫
      curveExternalComparison P g X.contact.sequence.line.sheaf (tangentSheaf X.variety.structureMap) =
    Curve.rightRaw P X g ≫
      curveExternalComparison P g X.contact.sequence.line.sheaf (tangentSheaf X.variety.structureMap) := by
  exact congrArg
    (fun q : AlgebraicSection (externalTensor P.structureMap
        (pullbackModule g.map X.contact.sequence.line.sheaf) (pullbackModule g.map (tangentSheaf X.variety.structureMap))) =>
      q ≫ curveExternalComparison P g X.contact.sequence.line.sheaf (tangentSheaf X.variety.structureMap))
    (LeBrunSalamon.Construction.FamilyBivectors.Reparametrization.rightRaw
      P e he X f g hg)

theorem right_definition :
    Curve.rightRaw P X g ≫
      curveExternalComparison P g X.contact.sequence.line.sheaf (tangentSheaf X.variety.structureMap) = Curve.rightSection P X g := by
  rfl

end FinalSectionProof

/-- Reparametrization invariance in the actual target bundle, including
all the canonical composition and external-product comparisons. -/
theorem leftSection :
    pullSection (curveSquareMap P (curve P e he)) (Curve.leftSection P X f) ≫
      (compositionPullback (curveSquareMap P (curve P e he)) (curveSquareMap P f)
        (curveSquareMap P g) (square_comp P e he X f g hg)
        (movingPairBundleLeft X.variety X.contact)).hom = Curve.leftSection P X g := by
  obtain ⟨A⟩ := externalExpansion_exists (projectiveLineVariety P)
    (identityCurveContact P).sequence.line (sourceBivector P)
  exact (FinalSectionProof.left_comparison P e he X f g hg A).trans
    ((FinalSectionProof.left_transport P e he X f g hg).trans
      (FinalSectionProof.left_definition P X g))

theorem rightSection :
    pullSection (curveSquareMap P (curve P e he)) (Curve.rightSection P X f) ≫
      (compositionPullback (curveSquareMap P (curve P e he)) (curveSquareMap P f)
        (curveSquareMap P g) (square_comp P e he X f g hg)
        (movingPairBundleRight X.variety X.contact)).hom = Curve.rightSection P X g := by
  obtain ⟨A⟩ := externalExpansion_exists (projectiveLineVariety P)
    (identityCurveContact P).sequence.line (sourceBivector P)
  exact (FinalSectionProof.right_comparison P e he X f g hg A).trans
    ((FinalSectionProof.right_transport P e he X f g hg).trans
      (FinalSectionProof.right_definition P X g))

end Reparametrization

end LeBrunSalamon.Construction.FamilyBivectors

end
