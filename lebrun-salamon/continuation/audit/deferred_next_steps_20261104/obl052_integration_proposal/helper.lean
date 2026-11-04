import LSNodalTangent
import LSHomDegree
import LSChartSmoothnessCriteria
import LSGeometricIntegrality

/-!
# Dominance of the actual two-point Hom evaluation

The proof constructs parameter lifts from interpolated section values,
compares their actual marked evaluations, and applies the rational-point
smoothness criterion. Fixed markings then transfer density to the full
two-point source. The original full-family detection consequences follow.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.Construction.Lines

namespace LeBrunSalamon.HomDominanceProof.HomPointDeformations

theorem pointLift_ext {Y : Scheme} {sY : Y ⟶ ComplexBase}
    {t : PointsOver ComplexBase (𝟙 ComplexBase) Y sY}
    (v w : Infinitesimal.PointLift Y sY t) (h : v.map = w.map) : v = w := by
  cases v
  cases w
  dsimp only at h
  cases h
  rfl

def reducedParameter {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (v : PointsOver Infinitesimal.DualScheme Infinitesimal.dualToC Y sY) :
    PointsOver ComplexBase (𝟙 ComplexBase) Y sY :=
  ⟨Infinitesimal.origin ≫ v.val, by
    rw [Category.assoc, v.property, DualThickening.origin_overC]⟩

theorem zeroSection_sourceMap (P : ProjectiveLineOverC)
    {Y : Scheme} {sY : Y ⟶ ComplexBase}
    (v : PointsOver Infinitesimal.DualScheme Infinitesimal.dualToC Y sY) :
    DualThickening.zeroSection P.structureMap ≫ rationalSourceMap P v =
      HomDeformation.sourceAtPoint P (reducedParameter v) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, rationalSourceMap, pullback.lift_fst,
      HomDeformation.sourceAtPoint_fst]
    exact DualThickening.zeroSection_projection P.structureMap
  · simp only [Category.assoc, rationalSourceMap, pullback.lift_snd,
      HomDeformation.sourceAtPoint_snd]
    rw [← Category.assoc]
    change (DualThickening.zeroSection P.structureMap ≫
      DualThickening.parameter P.structureMap) ≫ v.val = _
    rw [DualThickening.zeroSection_parameter, Category.assoc]
    rfl

variable (P : ProjectiveLineOverC) {d : ℕ} {X : SmoothProperComplexVariety d}
variable (H : HomSpacePresentation P X)
variable (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)

/-- A parameter lift induces the actual universal first-order family. -/
def deformationOfLift (v : Infinitesimal.PointLift H.parameter H.toC t) :
    FamilyVariation.Deformation P.structureMap X.structureMap (H.mapAt P t) where
  map := rationalSourceMap P (⟨v.map, v.overC⟩ :
    PointsOver Infinitesimal.DualScheme Infinitesimal.dualToC H.parameter H.toC) ≫
    H.evaluation
  overC := by
    rw [Category.assoc, H.overC, ← Category.assoc]
    change (rationalSourceMap P _ ≫ pullback.fst P.structureMap H.toC) ≫
      P.structureMap = _
    rw [show rationalSourceMap P _ ≫ pullback.fst P.structureMap H.toC =
      pullback.fst P.structureMap Infinitesimal.dualToC from pullback.lift_fst _ _ _]
    rfl
  reduces := by
    rw [← Category.assoc, zeroSection_sourceMap]
    have ht : reducedParameter (⟨v.map, v.overC⟩ :
        PointsOver Infinitesimal.DualScheme Infinitesimal.dualToC H.parameter H.toC) = t := by
      apply Subtype.ext
      exact v.reduces
    rw [ht]
    rfl

theorem deformationOfLift_injective : Function.Injective (deformationOfLift P H t) := by
  intro v w h
  apply pointLift_ext
  have he : (⟨v.map, v.overC⟩ :
      PointsOver Infinitesimal.DualScheme Infinitesimal.dualToC H.parameter H.toC) =
      ⟨w.map, w.overC⟩ := by
    apply (H.universal Infinitesimal.DualScheme Infinitesimal.dualToC).injective
    apply Subtype.ext
    exact congrArg FamilyVariation.Deformation.map h
  exact congrArg Subtype.val he

/-- Full representability on the nilpotent test scheme supplies every
deformation, and injectivity at the closed fiber fixes the actual center. -/
theorem deformationOfLift_surjective : Function.Surjective (deformationOfLift P H t) := by
  intro D
  obtain ⟨v, hv⟩ := (H.universal Infinitesimal.DualScheme Infinitesimal.dualToC).surjective
    (⟨D.map, D.overC⟩ : PointsOver (RationalSourceOver P Infinitesimal.DualScheme
      Infinitesimal.dualToC) (pullback.fst P.structureMap Infinitesimal.dualToC ≫
        P.structureMap) X.scheme X.structureMap)
  have hmap : rationalSourceMap P v ≫ H.evaluation = D.map := congrArg Subtype.val hv
  have hcenter : reducedParameter v = t := by
    apply HomDegree.mapAt_injective P H
    change HomDeformation.sourceAtPoint P (reducedParameter v) ≫ H.evaluation = H.mapAt P t
    rw [← zeroSection_sourceMap P v, Category.assoc, hmap]
    exact D.reduces
  let w : Infinitesimal.PointLift H.parameter H.toC t :=
    ⟨v.val, v.property, congrArg Subtype.val hcenter⟩
  refine ⟨w, ?_⟩
  apply FamilyVariation.Deformation.ext
  exact hmap

def homPointDeformationEquiv :
    Infinitesimal.PointLift H.parameter H.toC t ≃
      FamilyVariation.Deformation P.structureMap X.structureMap (H.mapAt P t) :=
  Equiv.ofBijective (deformationOfLift P H t)
    ⟨deformationOfLift_injective P H t, deformationOfLift_surjective P H t⟩

/-- An infinitesimal lift whose center belongs to an open factors through
that very open. This is proved using the actual surjective reduction map. -/
theorem pointLift_in_open {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (u : PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ sY))
    (v : Infinitesimal.PointLift Y sY
      ⟨u.val ≫ U.ι, by simpa only [Category.assoc] using u.property⟩) :
    ∃ w : Infinitesimal.PointLift U.toScheme (U.ι ≫ sY) u,
      w.map ≫ U.ι = v.map := by
  have hrange : Set.range v.map ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨x, hx⟩ := DualThickening.origin_surjective z
    subst z
    have h := congrArg (fun k : ComplexBase ⟶ Y => k x) v.reduces
    exact ⟨u.val x, h.symm⟩
  let l := IsOpenImmersion.lift U.ι v.map hrange
  have hl : l ≫ U.ι = v.map := IsOpenImmersion.lift_fac U.ι v.map hrange
  refine ⟨⟨l, ?_, ?_⟩, hl⟩
  · rw [← Category.assoc, hl, v.overC]
  · apply (cancel_mono U.ι).mp
    rw [Category.assoc, hl, v.reduces]

end LeBrunSalamon.HomDominanceProof.HomPointDeformations


end

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.Construction.Lines
open LeBrunSalamon.HomDominanceProof.HomPointDeformations

namespace LeBrunSalamon.HomDominanceProof.HomMarkedEvaluation

variable (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
variable {d : ℕ} {X : SmoothProperComplexVariety d}
variable (H : HomSpacePresentation P X)
variable (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)

/-- The actual central point of marked universal evaluation is the marked
point of the actual central curve. -/
theorem markedEvaluation_atCenter :
    t.val ≫ FixedNodeHom.markedEvaluation P p H = p.map ≫ H.mapAt P t := by
  change t.val ≫ (FixedNodeHom.markingSection P p H.toC ≫ H.evaluation) =
    p.map ≫ (HomDeformation.sourceAtPoint P t ≫ H.evaluation)
  rw [← Category.assoc, ← HomDeformation.sourceAtPoint_marking, Category.assoc]

/-- The same central point, with its original map written explicitly. -/
def evaluationPoint : PointsOver ComplexBase (𝟙 ComplexBase) X.scheme X.structureMap :=
  ⟨p.map ≫ H.mapAt P t, by
    rw [← markedEvaluation_atCenter P p H t, Category.assoc,
      FixedNodeHom.markedEvaluation_overC, t.property]⟩

/-- Push the given parameter lift through the actual marked evaluation. -/
def evaluatedLift (v : Infinitesimal.PointLift H.parameter H.toC t) :
    Infinitesimal.PointLift X.scheme X.structureMap (evaluationPoint P p H t) :=
  Charts.AffineTangentLift.push
    (s := t) (t := evaluationPoint P p H t)
    (FixedNodeHom.markedEvaluation P p H)
    (FixedNodeHom.markedEvaluation_overC P p H)
    (markedEvaluation_atCenter P p H t) v

/-- The thickened source point is the constant marked section after the
canonical projection from the thickening of Spec C to the dual numbers. -/
theorem thickening_map_marking :
    DualThickening.map p.map p.overC =
      DualThickening.parameter (𝟙 ComplexBase) ≫
        FixedNodeHom.markingSection P p Infinitesimal.dualToC := by
  apply pullback.hom_ext
  · change DualThickening.map p.map p.overC ≫ DualThickening.projection P.structureMap =
      (DualThickening.parameter (𝟙 ComplexBase) ≫
        FixedNodeHom.markingSection P p Infinitesimal.dualToC) ≫
          pullback.fst P.structureMap Infinitesimal.dualToC
    rw [DualThickening.map_projection, Category.assoc,
      FixedNodeHom.markingSection_fst, ← Category.assoc, DualThickening.parameter_overC]
    simp only [DualThickening.toC, Category.comp_id]
  · change DualThickening.map p.map p.overC ≫ DualThickening.parameter P.structureMap =
      (DualThickening.parameter (𝟙 ComplexBase) ≫
        FixedNodeHom.markingSection P p Infinitesimal.dualToC) ≫
          pullback.snd P.structureMap Infinitesimal.dualToC
    rw [DualThickening.map_parameter, Category.assoc,
      FixedNodeHom.markingSection_snd, Category.comp_id]

/-- Equality of the actual maps on the whole nonreduced test scheme. -/
theorem deformationOfLift_marked_map
    (v : Infinitesimal.PointLift H.parameter H.toC t) :
    DualThickening.map p.map p.overC ≫ (deformationOfLift P H t v).map =
      DualThickening.parameter (𝟙 ComplexBase) ≫ (evaluatedLift P p H t v).map := by
  let v' : PointsOver Infinitesimal.DualScheme Infinitesimal.dualToC
      H.parameter H.toC := ⟨v.map, v.overC⟩
  change DualThickening.map p.map p.overC ≫
      (rationalSourceMap P v' ≫ H.evaluation) =
    DualThickening.parameter (𝟙 ComplexBase) ≫
      (v'.val ≫ (FixedNodeHom.markingSection P p H.toC ≫ H.evaluation))
  rw [thickening_map_marking P p]
  simp only [Category.assoc]
  rw [← Category.assoc (FixedNodeHom.markingSection P p Infinitesimal.dualToC)
    (rationalSourceMap P v') H.evaluation,
    FixedNodeHom.markingSection_naturality P p v']
  simp only [Category.assoc]

/-- Restricting the universal deformation to p is exactly the point
deformation obtained by pushing its Hom-parameter lift through evaluation. -/
theorem deformationOfLift_marked
    (v : Infinitesimal.PointLift H.parameter H.toC t) :
    (deformationOfLift P H t v).pullback p.map p.overC =
      SourceTangent.pointDeformation (evaluatedLift P p H t v) := by
  apply FamilyVariation.Deformation.ext
  exact deformationOfLift_marked_map P p H t v

end LeBrunSalamon.HomDominanceProof.HomMarkedEvaluation

end

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

namespace LeBrunSalamon.HomDominanceProof.TwoPointDeformations

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

end LeBrunSalamon.HomDominanceProof.TwoPointDeformations


end

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
open LeBrunSalamon.HomDominanceProof.HomPointDeformations
open LeBrunSalamon.HomDominanceProof.HomMarkedEvaluation
open LeBrunSalamon.HomDominanceProof.TwoPointDeformations

namespace LeBrunSalamon.HomDominanceProof.TwoMarkedHomLifts

theorem pointDeformation_injective {Y : Scheme} {sY : Y ⟶ ComplexBase}
    {y : PointsOver ComplexBase (𝟙 ComplexBase) Y sY} :
    Function.Injective (SourceTangent.pointDeformation (y := y)) := by
  intro v w h
  apply pointLift_ext
  have hm := congrArg (fun E : FamilyVariation.Deformation (𝟙 ComplexBase) sY y.val =>
    LocalVelocityComparison.dualBaseInclusion ≫ E.map) h
  simpa only [SourceTangent.pointDeformation_onDual] using hm

/-- Arbitrary first-order motions at two distinct marked target points
are obtained from one actual infinitesimal Hom parameter. -/
theorem twoMarkedEvaluatedLifts_surjective (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H : HomSpacePresentation P X)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)
    (hgen : IsTwoPointGloballyGenerated P
      (pullbackModule (H.mapAt P t) (tangentSheaf X.structureMap)))
    (p q : ProjectiveLinePoint P) (hpq : p.map ≠ q.map) :
    Function.Surjective (fun v : Infinitesimal.PointLift H.parameter H.toC t =>
      (evaluatedLift P p H t v, evaluatedLift P q H t v)) := by
  rintro ⟨τp, τq⟩
  have hf : H.mapAt P t ≫ X.structureMap = P.structureMap := by
    change (HomDeformation.sourceAtPoint P t ≫ H.evaluation) ≫ X.structureMap = _
    rw [Category.assoc, H.overC, ← Category.assoc,
      HomDeformation.sourceAtPoint_fst, Category.id_comp]
  obtain ⟨D, hD⟩ := twoPointDeformations_surjective P X (H.mapAt P t) hf hgen p q hpq
    (SourceTangent.pointDeformation τp, SourceTangent.pointDeformation τq)
  obtain ⟨v, hv⟩ := deformationOfLift_surjective P H t D
  refine ⟨v, Prod.ext ?_ ?_⟩
  · apply pointDeformation_injective
    rw [← deformationOfLift_marked P p H t v, hv]
    exact congrArg Prod.fst hD
  · apply pointDeformation_injective
    rw [← deformationOfLift_marked P q H t v, hv]
    exact congrArg Prod.snd hD

end LeBrunSalamon.HomDominanceProof.TwoMarkedHomLifts


end

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
open LeBrunSalamon.HomDominanceProof.HomPointDeformations
open LeBrunSalamon.HomDominanceProof.HomMarkedEvaluation
open LeBrunSalamon.HomDominanceProof.TwoMarkedHomLifts

namespace LeBrunSalamon.HomDominanceProof.TwoPointProductLifts

/-- The two actual product projections determine the entire target lift. -/
theorem product_evaluation_lifts (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H : HomSpacePresentation P X)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)
    (hgen : IsTwoPointGloballyGenerated P
      (pullbackModule (H.mapAt P t) (tangentSheaf X.structureMap)))
    (p q : ProjectiveLinePoint P) (hpq : p.map ≠ q.map)
    (F : H.parameter ⟶ SelfProduct X.structureMap)
    (hfirst : F ≫ firstProjection X.structureMap = FixedNodeHom.markedEvaluation P p H)
    (hsecond : F ≫ secondProjection X.structureMap = FixedNodeHom.markedEvaluation P q H)
    (z : PointsOver ComplexBase (𝟙 ComplexBase) (SelfProduct X.structureMap)
      (firstProjection X.structureMap ≫ X.structureMap))
    (hz : t.val ≫ F = z.val)
    (τ : Infinitesimal.PointLift (SelfProduct X.structureMap)
      (firstProjection X.structureMap ≫ X.structureMap) z) :
    ∃ v : Infinitesimal.PointLift H.parameter H.toC t, v.map ≫ F = τ.map := by
  have hzp : z.val ≫ firstProjection X.structureMap = (evaluationPoint P p H t).val := by
    change z.val ≫ firstProjection X.structureMap = p.map ≫ H.mapAt P t
    rw [← hz, Category.assoc, hfirst, markedEvaluation_atCenter]
  have hzq : z.val ≫ secondProjection X.structureMap = (evaluationPoint P q H t).val := by
    change z.val ≫ secondProjection X.structureMap = q.map ≫ H.mapAt P t
    rw [← hz, Category.assoc, hsecond, markedEvaluation_atCenter]
  let τp := Charts.AffineTangentLift.push
    (s := z) (t := evaluationPoint P p H t) (firstProjection X.structureMap) rfl hzp τ
  let τq := Charts.AffineTangentLift.push
    (s := z) (t := evaluationPoint P q H t) (secondProjection X.structureMap)
    (pullback.condition (f := X.structureMap) (g := X.structureMap)).symm hzq τ
  obtain ⟨v, hv⟩ := twoMarkedEvaluatedLifts_surjective P H t hgen p q hpq (τp, τq)
  have hp := congrArg Infinitesimal.PointLift.map (congrArg Prod.fst hv)
  have hq := congrArg Infinitesimal.PointLift.map (congrArg Prod.snd hv)
  refine ⟨v, ?_⟩
  apply pullback.hom_ext
  · change (v.map ≫ F) ≫ firstProjection X.structureMap = τ.map ≫ firstProjection X.structureMap
    rw [Category.assoc, hfirst]
    exact hp
  · change (v.map ≫ F) ≫ secondProjection X.structureMap = τ.map ≫ secondProjection X.structureMap
    rw [Category.assoc, hsecond]
    exact hq

/-- Once a lift is centered at the chosen open, the original open
factorization preserves its entire composite into the target. -/
theorem lift_in_open_with_composite {Y Z : Scheme}
    (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (u : PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ sY))
    (F : Y ⟶ Z) (b : Infinitesimal.DualScheme ⟶ Z)
    (v : Infinitesimal.PointLift Y sY
      ⟨u.val ≫ U.ι, by simpa only [Category.assoc] using u.property⟩)
    (hv : v.map ≫ F = b) :
    ∃ w : Infinitesimal.PointLift U.toScheme (U.ι ≫ sY) u,
      w.map ≫ (U.ι ≫ F) = b := by
  obtain ⟨w, hw⟩ := pointLift_in_open sY U u v
  refine ⟨w, ?_⟩
  rw [← Category.assoc, hw, hv]

end LeBrunSalamon.HomDominanceProof.TwoPointProductLifts


end

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.Construction.Lines

/-! Ordinary scheme-map comparisons for fixed markings in the actual
two-point source. No smoothness of the projective line, Hom smoothness,
target irreducibility, infinitesimal comparison, or dominance theorem is used.
-/

namespace LeBrunSalamon.HomDominanceProof.FixedMarkings

variable (P : ProjectiveLineOverC) (p q : ProjectiveLinePoint P)
variable {d : ℕ} {X : SmoothProperComplexVariety d}
variable (H : HomSpacePresentation P X) (U : H.parameter.Opens)


def pairMap : ComplexBase ⟶ SelfProduct P.structureMap :=
  pullback.lift p.map q.map (p.overC.trans q.overC.symm)

theorem pairMap_first :
    pairMap P p q ≫ firstProjection P.structureMap = p.map :=
  pullback.lift_fst _ _ _

theorem pairMap_second :
    pairMap P p q ≫ secondProjection P.structureMap = q.map :=
  pullback.lift_snd _ _ _

theorem pairMap_overC :
    pairMap P p q ≫ HomTwoPointEvaluation.squareStructure P = 𝟙 ComplexBase := by
  rw [HomTwoPointEvaluation.squareStructure, ← Category.assoc,
    pairMap_first, p.overC]

/-- Two marked evaluations on the original representing parameter. -/
def pairedEvaluation : H.parameter ⟶ SelfProduct X.structureMap :=
  pullback.lift (FixedNodeHom.markedEvaluation P p H)
    (FixedNodeHom.markedEvaluation P q H) (by
      rw [FixedNodeHom.markedEvaluation_overC,
        FixedNodeHom.markedEvaluation_overC])

theorem pairedEvaluation_first :
    pairedEvaluation P p q H ≫ firstProjection X.structureMap =
      FixedNodeHom.markedEvaluation P p H :=
  pullback.lift_fst _ _ _

theorem pairedEvaluation_second :
    pairedEvaluation P p q H ≫ secondProjection X.structureMap =
      FixedNodeHom.markedEvaluation P q H :=
  pullback.lift_snd _ _ _

theorem pairedEvaluation_overC :
    pairedEvaluation P p q H ≫ (firstProjection X.structureMap ≫ X.structureMap) =
      H.toC := by
  rw [← Category.assoc, pairedEvaluation_first, FixedNodeHom.markedEvaluation_overC]


/-- Keep both markings fixed and vary the actual open Hom parameter. -/
def markingSection : U.toScheme ⟶ HomTwoPointEvaluation.Source P H U :=
  pullback.lift ((U.ι ≫ H.toC) ≫ pairMap P p q) (𝟙 U.toScheme) (by
    simp only [Category.assoc, pairMap_overC, Category.comp_id, Category.id_comp])

theorem markingSection_fst :
    markingSection P p q H U ≫
      pullback.fst (HomTwoPointEvaluation.squareStructure P) (U.ι ≫ H.toC) =
      (U.ι ≫ H.toC) ≫ pairMap P p q :=
  pullback.lift_fst _ _ _

theorem markingSection_snd :
    markingSection P p q H U ≫
      pullback.snd (HomTwoPointEvaluation.squareStructure P) (U.ι ≫ H.toC) =
      𝟙 U.toScheme :=
  pullback.lift_snd _ _ _

theorem markingSection_overC :
    markingSection P p q H U ≫ HomTwoPointEvaluation.structureMap P H U =
      U.ι ≫ H.toC := by
  simp only [markingSection, HomTwoPointEvaluation.structureMap,
    pullback.lift_snd_assoc, Category.id_comp]

theorem markingSection_leftSource :
    markingSection P p q H U ≫ HomTwoPointEvaluation.leftSource P H U =
      U.ι ≫ FixedNodeHom.markingSection P p H.toC := by
  apply pullback.hom_ext
  · simp only [Category.assoc, HomTwoPointEvaluation.leftSource,
      pullback.lift_fst, FixedNodeHom.markingSection_fst]
    rw [← Category.assoc, markingSection_fst]
    simp only [Category.assoc, pairMap_first]
  · simp only [Category.assoc, HomTwoPointEvaluation.leftSource,
      pullback.lift_snd, FixedNodeHom.markingSection_snd, Category.comp_id]
    rw [← Category.assoc, markingSection_snd, Category.id_comp]

theorem markingSection_rightSource :
    markingSection P p q H U ≫ HomTwoPointEvaluation.rightSource P H U =
      U.ι ≫ FixedNodeHom.markingSection P q H.toC := by
  apply pullback.hom_ext
  · simp only [Category.assoc, HomTwoPointEvaluation.rightSource,
      pullback.lift_fst, FixedNodeHom.markingSection_fst]
    rw [← Category.assoc, markingSection_fst]
    simp only [Category.assoc, pairMap_second]
  · simp only [Category.assoc, HomTwoPointEvaluation.rightSource,
      pullback.lift_snd, FixedNodeHom.markingSection_snd, Category.comp_id]
    rw [← Category.assoc, markingSection_snd, Category.id_comp]


theorem markingSection_evaluation_first :
    (markingSection P p q H U ≫ HomTwoPointEvaluation.evaluation P H U) ≫
      firstProjection X.structureMap = U.ι ≫ FixedNodeHom.markedEvaluation P p H := by
  rw [Category.assoc, HomTwoPointEvaluation.evaluation_first]
  simpa only [Category.assoc, FixedNodeHom.markedEvaluation] using
    congrArg (fun m => m ≫ H.evaluation) (markingSection_leftSource P p q H U)

theorem markingSection_evaluation_second :
    (markingSection P p q H U ≫ HomTwoPointEvaluation.evaluation P H U) ≫
      secondProjection X.structureMap = U.ι ≫ FixedNodeHom.markedEvaluation P q H := by
  rw [Category.assoc, HomTwoPointEvaluation.evaluation_second]
  simpa only [Category.assoc, FixedNodeHom.markedEvaluation] using
    congrArg (fun m => m ≫ H.evaluation) (markingSection_rightSource P p q H U)

theorem markingSection_evaluation :
    markingSection P p q H U ≫ HomTwoPointEvaluation.evaluation P H U =
      U.ι ≫ pairedEvaluation P p q H := by
  apply pullback.hom_ext
  · change (markingSection P p q H U ≫ HomTwoPointEvaluation.evaluation P H U) ≫
      firstProjection X.structureMap =
      (U.ι ≫ pairedEvaluation P p q H) ≫ firstProjection X.structureMap
    rw [markingSection_evaluation_first, Category.assoc, pairedEvaluation_first]
  · change (markingSection P p q H U ≫ HomTwoPointEvaluation.evaluation P H U) ≫
      secondProjection X.structureMap =
      (U.ι ≫ pairedEvaluation P p q H) ≫ secondProjection X.structureMap
    rw [markingSection_evaluation_second, Category.assoc, pairedEvaluation_second]

/-- The literal paired map on the open, with no parameter-scheme abbreviation. -/
theorem markingSection_evaluation_lift :
    markingSection P p q H U ≫ HomTwoPointEvaluation.evaluation P H U =
      pullback.lift (U.ι ≫ FixedNodeHom.markedEvaluation P p H)
        (U.ι ≫ FixedNodeHom.markedEvaluation P q H) (by
          simp only [Category.assoc, FixedNodeHom.markedEvaluation_overC]) := by
  apply pullback.hom_ext
  · simpa only [pullback.lift_fst, firstProjection] using
      markingSection_evaluation_first P p q H U
  · simpa only [pullback.lift_snd, secondProjection] using
      markingSection_evaluation_second P p q H U

/-- This applies equally to complex parameters and whole nonreduced test maps. -/
def liftParameter {T : Scheme} (sT : T ⟶ ComplexBase)
    (t : PointsOver T sT U.toScheme (U.ι ≫ H.toC)) :
    PointsOver T sT (HomTwoPointEvaluation.Source P H U)
      (HomTwoPointEvaluation.structureMap P H U) :=
  ⟨t.val ≫ markingSection P p q H U, by
    rw [Category.assoc, markingSection_overC, t.property]⟩

/-- Density of the fixed-pair map already forces density of the full evaluation. -/
theorem denseRange_of_markedPair
    (h : DenseRange (U.ι ≫ pairedEvaluation P p q H).base) :
    DenseRange (HomTwoPointEvaluation.evaluation P H U).base := by
  have hc : DenseRange
      (markingSection P p q H U ≫ HomTwoPointEvaluation.evaluation P H U).base := by
    rw [markingSection_evaluation]
    exact h
  exact DenseRange.of_comp (g := (markingSection P p q H U).base) hc



end LeBrunSalamon.HomDominanceProof.FixedMarkings
end

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace LeBrunSalamon.HomDominanceProof.SmoothRestrictionDensity

/-! Generic topology/scheme bridge only.  No Hom presentation, original052,
original057, or external published input occurs in these declarations. -/


theorem denseRange_of_smooth_composite {W X Y : Scheme}
    [Nonempty W] [PreirreducibleSpace Y]
    (j : W ⟶ X) (f : X ⟶ Y) [Smooth (j ≫ f)] :
    DenseRange f.base := by
  have hd : DenseRange (j ≫ f).base :=
    IsOpenMap.denseRange_of_isPreirreducibleSpace
      (j ≫ f).base (j ≫ f).isOpenMap
  exact DenseRange.of_comp (g := j.base) hd


theorem denseRange_of_smooth_neighborhood {X Y : Scheme}
    [PreirreducibleSpace Y] (f : X ⟶ Y) (x : X)
    (h : ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)) :
    DenseRange f.base := by
  obtain ⟨U, hx, hsmooth⟩ := h
  letI : Nonempty U.toScheme := ⟨⟨x, hx⟩⟩
  letI : Smooth (U.ι ≫ f) := hsmooth
  exact denseRange_of_smooth_composite U.ι f


/-- This matches the open-neighborhood conclusion of the tangent-lift criterion. -/
theorem denseRange_of_smooth_pointMap_neighborhood {T X Y : Scheme}
    [Nonempty T] [PreirreducibleSpace Y] (f : X ⟶ Y) (x : T ⟶ X)
    (h : ∃ U : X.Opens, Set.range x ⊆ U ∧ Smooth (U.ι ≫ f)) :
    DenseRange f.base := by
  obtain ⟨U, hx, hsmooth⟩ := h
  let t : T := Classical.choice inferInstance
  exact denseRange_of_smooth_neighborhood f (x t)
    ⟨U, hx ⟨t, rfl⟩, hsmooth⟩



end LeBrunSalamon.HomDominanceProof.SmoothRestrictionDensity
end

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
open LeBrunSalamon.HomDominanceProof.TwoPointProductLifts

namespace LeBrunSalamon.HomDominanceProof.TwoPointDominance

/-- The complex specialization of the generic rational-point tangent-lift
criterion reviewed in3h, expressed using the project's identical dual ring.
It mentions no Hom space, rational curve, contact geometry, or dominance. -/
def ComplexTangentLiftCriterion : Prop :=
  ∀ (A B : Scheme) (sA : A ⟶ ComplexBase) (sB : B ⟶ ComplexBase)
    (F : A ⟶ B), F ≫ sB = sA →
    ∀ (a : ComplexBase ⟶ A), a ≫ sA = 𝟙 ComplexBase →
    Smooth sA → Smooth sB →
    (∀ b : Infinitesimal.DualScheme ⟶ B,
      b ≫ sB = Infinitesimal.dualToC → Infinitesimal.origin ≫ b = a ≫ F →
      ∃ l : Infinitesimal.DualScheme ⟶ A,
        l ≫ sA = Infinitesimal.dualToC ∧ Infinitesimal.origin ≫ l = a ∧ l ≫ F = b) →
    ∃ V : A.Opens, Set.range a ⊆ V ∧ Smooth (V.ι ≫ F)

/-- Fixed source markings reduce dominance of the actual universal evaluation
to the rational-point tangent-lift criterion. The target-square integrality
is supplied by the generic geometric-integrality theorem. -/
theorem homOpen_twoPointEvaluation_dominant_of_tangent_lifts
    (hcriterion : ComplexTangentLiftCriterion)
    (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) (H : HomSpacePresentation P X)
    (U : H.parameter.Opens) (hU : Smooth (U.ι ≫ H.toC))
    (t : PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ H.toC))
    (f : RationalCurve P X)
    (hf : f.map = H.mapAt P
      ⟨t.val ≫ U.ι, by simpa only [Category.assoc] using t.property⟩)
    (hfree : IsVeryFreeRationalCurve P X (intrinsicTangentBundle X) f) :
    DenseRange (Refinement.HomTwoPointEvaluation.evaluation P H U).base := by
  let u := Refinement.HomTwoPointEvaluation.parameterPoint P H U t
  have hgen : IsTwoPointGloballyGenerated P
      (pullbackModule (H.mapAt P u) (tangentSheaf X.structureMap)) := by
    change IsTwoPointGloballyGenerated P
      (pullbackModule f.map (tangentSheaf X.structureMap)) at hfree
    rw [hf] at hfree
    exact hfree
  obtain ⟨p, q, hpq⟩ := hgen.1
  let F := FixedMarkings.pairedEvaluation P p q H
  let sZ := firstProjection X.structureMap ≫ X.structureMap
  have hF : F ≫ sZ = H.toC := FixedMarkings.pairedEvaluation_overC P p q H
  have hopen : (U.ι ≫ F) ≫ sZ = U.ι ≫ H.toC := by rw [Category.assoc, hF]
  let z : PointsOver ComplexBase (𝟙 ComplexBase) (SelfProduct X.structureMap) sZ :=
    ⟨t.val ≫ (U.ι ≫ F), by rw [Category.assoc, hopen, t.property]⟩
  have hz : u.val ≫ F = z.val := by
    change (t.val ≫ U.ι) ≫ F = t.val ≫ (U.ι ≫ F)
    exact Category.assoc _ _ _
  have hlifts : ∀ b : Infinitesimal.DualScheme ⟶ SelfProduct X.structureMap,
      b ≫ sZ = Infinitesimal.dualToC →
      Infinitesimal.origin ≫ b = t.val ≫ (U.ι ≫ F) →
      ∃ a : Infinitesimal.DualScheme ⟶ U.toScheme,
        a ≫ (U.ι ≫ H.toC) = Infinitesimal.dualToC ∧
        Infinitesimal.origin ≫ a = t.val ∧ a ≫ (U.ι ≫ F) = b := by
    intro b hb hc
    let τ : Infinitesimal.PointLift (SelfProduct X.structureMap) sZ z := ⟨b, hb, hc⟩
    obtain ⟨v, hv⟩ := product_evaluation_lifts P H u hgen p q hpq F
      (FixedMarkings.pairedEvaluation_first P p q H)
      (FixedMarkings.pairedEvaluation_second P p q H) z hz τ
    obtain ⟨w, hw⟩ := lift_in_open_with_composite H.toC U t F b v hv
    exact ⟨w.map, w.overC, w.reduces, hw⟩
  have hsmooth : ∃ V : U.toScheme.Opens,
      Set.range t.val ⊆ V ∧ Smooth (V.ι ≫ (U.ι ≫ F)) :=
    hcriterion U.toScheme (SelfProduct X.structureMap) (U.ι ≫ H.toC) sZ
      (U.ι ≫ F) hopen t.val t.property hU inferInstance hlifts
  letI : IrreducibleSpace (SelfProduct X.structureMap : Scheme) :=
    GeometricIntegrality.complex_selfProduct_irreducible X.structureMap
  have hdense : DenseRange (U.ι ≫ F).base :=
    SmoothRestrictionDensity.denseRange_of_smooth_pointMap_neighborhood
      (U.ι ≫ F) t.val hsmooth
  exact FixedMarkings.denseRange_of_markedPair P p q H U hdense

end LeBrunSalamon.HomDominanceProof.TwoPointDominance


end

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.HomDominanceProof.ComplexCriterionSpecialization


theorem dualScheme_eq :
    Spec (CommRingCat.of (DualNumberGeometry.Dual ℂ)) = Infinitesimal.DualScheme := rfl

theorem dualToBase_eq :
    DualNumberGeometry.dualToBase ℂ = Infinitesimal.dualToC := rfl

theorem origin_eq :
    DualNumberGeometry.origin ℂ = Infinitesimal.origin := rfl


/-- Every map, center equation, neighborhood, and smoothness premise is retained. -/
theorem complexCriterion_of_generic
    (h : DualNumberGeometry.RationalPointDifferentialCriterion) :
    TwoPointDominance.ComplexTangentLiftCriterion := by
  intro A B sA sB F hF a ha hA hB hlifts
  apply h ℂ A B sA sB F hF a ha hA hB
  intro b hb hb0
  rw [dualToBase_eq] at hb
  rw [origin_eq] at hb0
  obtain ⟨l, hl, hl0, hlF⟩ := hlifts b hb hb0
  refine ⟨l, ?_, ?_, hlF⟩
  · simpa only [dualToBase_eq] using hl
  · simpa only [origin_eq] using hl0

/-- Apply precisely the existing3h published leaf after the proved translation. -/
theorem complexCriterion : TwoPointDominance.ComplexTangentLiftCriterion :=
  complexCriterion_of_generic
    @PublishedInputs.Smoothness.smooth_of_surjective_tangent_lifts



end LeBrunSalamon.HomDominanceProof.ComplexCriterionSpecialization
end

noncomputable section

set_option autoImplicit false
open Bundle
open scoped Bundle ContDiff ENNReal
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing
open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.Limits

namespace LeBrunSalamon.Refinement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseTen
open LeBrunSalamon.PhaseTwentyOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFive LeBrunSalamon.Core LeBrunSalamon.Skeleton

open LeBrunSalamon.PhaseSeven in
/-- Kollár, Rational Curves on Algebraic Varieties II.3.5; explicit
two-point version in Gounelas, Free Curves on Varieties,
Documenta Mathematica 21 (2016), Proposition 4.7, p.299.
The source and map are the actual P1-square times the Hom open and
the given universal evaluation, not a contact or section detector. -/
theorem _root_.LeBrunSalamon.StandardInputs.homOpen_twoPointEvaluation_dominant
    (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) (H : HomSpacePresentation P X)
    (U : H.parameter.Opens) (hU : Smooth (U.ι ≫ H.toC))
    (t : PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ H.toC))
    (f : RationalCurve P X)
    (hf : f.map = H.mapAt P
      ⟨t.val ≫ U.ι, by simpa only [Category.assoc] using t.property⟩)
    (hfree : IsVeryFreeRationalCurve P X (intrinsicTangentBundle X) f) :
    DenseRange (Refinement.HomTwoPointEvaluation.evaluation P H U).base := by
  exact LeBrunSalamon.HomDominanceProof.TwoPointDominance.homOpen_twoPointEvaluation_dominant_of_tangent_lifts
    LeBrunSalamon.HomDominanceProof.ComplexCriterionSpecialization.complexCriterion
    P X H U hU t f hf hfree

/-- The actual full Hom family detects sections of any finite-rank
bundle on the target square, through its universal two-point evaluation. -/
theorem fullFamily_detects_bundle_section (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X)
    (H : FullConicNeighborhood P p X g) {r : ℕ}
    (L : AlgebraicVectorBundle (SelfProduct X.variety.structureMap) r)
    (B C : AlgebraicSection L.sheaf)
    (h : ∀ t, pullSection (curveSquareMap P (H.curveAt t)) B =
      pullSection (curveSquareMap P (H.curveAt t)) C) : B = C := by
  let Z := HomTwoPointEvaluation.Source P H.homSpace H.neighborhood
  let s : Z ⟶ ComplexBase :=
    HomTwoPointEvaluation.structureMap P H.homSpace H.neighborhood
  let e : Z ⟶ SelfProduct X.variety.structureMap :=
    HomTwoPointEvaluation.evaluation P H.homSpace H.neighborhood
  letI : Smooth s := HomTwoPointEvaluation.source_smooth P H.homSpace H.neighborhood H.smooth
  letI : AlgebraicGeometry.IsReduced Z :=
    LeBrunSalamon.SchemeStandardInputs.smooth_complex_reduced s
  letI : Smooth (firstProjection X.variety.structureMap ≫ X.variety.structureMap) :=
    inferInstance
  letI : AlgebraicGeometry.IsReduced (SelfProduct X.variety.structureMap) :=
    LeBrunSalamon.SchemeStandardInputs.smooth_complex_reduced
      (firstProjection X.variety.structureMap ≫ X.variety.structureMap)
  have he : DenseRange e.base :=
    LeBrunSalamon.StandardInputs.homOpen_twoPointEvaluation_dominant P X.variety
      H.homSpace H.neighborhood H.smooth H.marked (H.curveAt H.marked)
      (H.curveAt_spec H.marked) (H.veryFree H.marked)
  apply dominant_pullSection_injective e he (fun U => inferInstance) L
  apply ComplexPointSectionDetection.section_eq s (pullbackBundle e L)
  intro q
  let t := HomTwoPointEvaluation.pointParameter P H.homSpace H.neighborhood q
  let z : ComplexBase ⟶ SelfProduct P.structureMap :=
    q.val ≫ pullback.fst (HomTwoPointEvaluation.squareStructure P)
      (H.neighborhood.ι ≫ H.homSpace.toC)
  have hF : HomTwoPointEvaluation.fiberInclusion P H.homSpace H.neighborhood t ≫ e =
      curveSquareMap P (H.curveAt t) :=
    HomTwoPointEvaluation.fiberInclusion_evaluation P H.homSpace H.neighborhood t
      (H.curveAt t) (H.curveAt_spec t)
  have hq : z ≫ HomTwoPointEvaluation.fiberInclusion P H.homSpace H.neighborhood t = q.val :=
    HomTwoPointEvaluation.point_factorization P H.homSpace H.neighborhood q
  have hsquare : z ≫ curveSquareMap P (H.curveAt t) = q.val ≫ e := by
    rw [← hF, ← Category.assoc, hq]
  calc
    pullSection q.val (pullSection e B) =
        pullSection z (pullSection (curveSquareMap P (H.curveAt t)) B) ≫
          (pullbackSquareIso z (curveSquareMap P (H.curveAt t)) q.val e hsquare L.sheaf).hom :=
      (pullbackSquareIso_onSections z (curveSquareMap P (H.curveAt t)) q.val e hsquare B).symm
    _ = pullSection z (pullSection (curveSquareMap P (H.curveAt t)) C) ≫
          (pullbackSquareIso z (curveSquareMap P (H.curveAt t)) q.val e hsquare L.sheaf).hom := by
      rw [h t]
    _ = pullSection q.val (pullSection e C) :=
      pullbackSquareIso_onSections z (curveSquareMap P (H.curveAt t)) q.val e hsquare C

/-- Very-freeness and FULLNESS of the open Hom family imply that its
moving-pair evaluation is dominant. Thus its curve-square tests detect a
section on X x X. This is false for an arbitrary single chosen curve. -/
theorem fullFamily_detects_section (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X)
    (H : FullConicNeighborhood P p X g)
    (B C : ExternalSquareSections X.variety X.contact.sequence.line)
    (h : ∀ t, pullSection (curveSquareMap P (H.curveAt t)) B =
      pullSection (curveSquareMap P (H.curveAt t)) C) : B = C := by
  exact fullFamily_detects_bundle_section P p X g H
    (externalSquareLine X.variety.structureMap X.contact.sequence.line) B C h

/-- Symmetry may be recovered from the symmetric source formula on the full family. This avoids demanding
that a chosen scheme cover lift the coarse-space involution. Source: ext:bivector and des:family. -/
theorem fullFamilyIdentity_symmetric (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X)
    (H : FullConicNeighborhood P p X g)
    (B : ExternalSquareSections X.variety X.contact.sequence.line)
    (h : ∀ t, CurveKernelIdentity P X.contact (H.curveAt t) B) :
    IsSymmetricExternalSection X.variety.structureMap X.contact.sequence.line B := by
  change (chosenExternalExchange X.variety.structureMap X.contact.sequence.line).identification.swapSection
    B = B
  apply fullFamily_detects_section P p X g H
  intro t
  have he := CurveExchangeProof.curveKernelIdentity_exchange P X.contact (H.curveAt t) B (h t)
  exact ((curveKernelIdentity_iff P X.contact (H.curveAt t) _).mp he).trans
    ((curveKernelIdentity_iff P X.contact (H.curveAt t) B).mp (h t)).symm

/-- Independent proper-source choices produce the same kernel when tested
on the SAME full neighborhood; no global uniqueness of normalized kernels
is asserted. Higher-order terms need not be fixed by the quadratic symbol. -/
theorem fullFamilyKernel_unique (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X)
    (H : FullConicNeighborhood P p X g)
    (B C : ExternalSquareSections X.variety X.contact.sequence.line)
    (hB : ∀ t, CurveKernelIdentity P X.contact (H.curveAt t) B)
    (hC : ∀ t, CurveKernelIdentity P X.contact (H.curveAt t) C) : B = C := by
  apply fullFamily_detects_section P p X g H B C
  intro t
  exact ((curveKernelIdentity_iff P X.contact (H.curveAt t) B).mp (hB t)).trans
    (((curveKernelIdentity_iff P X.contact (H.curveAt t) C).mp (hC t)).symm)

namespace FullFamilyDiagonalProof

/-- The same full family detects bundle sections on X: pull back to
the first projection, whose diagonal section makes it surjective, then
use the already proved detection theorem on the target square. -/
theorem detects_base_section (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X)
    (H : FullConicNeighborhood P p X g) {r : ℕ}
    (E : AlgebraicVectorBundle X.variety.scheme r) (a b : AlgebraicSection E.sheaf)
    (h : ∀ t, pullSection (H.curveAt t).map a = pullSection (H.curveAt t).map b) : a = b := by
  have hsurj : Function.Surjective (firstProjection X.variety.structureMap) := by
    intro x
    refine ⟨diagonal X.variety.structureMap x, ?_⟩
    exact congrArg (fun k : X.variety.scheme ⟶ X.variety.scheme => k x)
      (pullback.diagonal_fst X.variety.structureMap)
  letI : AlgebraicGeometry.IsReduced X.variety.scheme :=
    LeBrunSalamon.SchemeStandardInputs.smooth_complex_reduced X.variety.structureMap
  apply dominant_pullSection_injective (firstProjection X.variety.structureMap)
    hsurj.denseRange (fun U => inferInstance) E
  apply fullFamily_detects_bundle_section P p X g H
    (pullbackBundle (firstProjection X.variety.structureMap) E)
  intro t
  let e := pullbackSquareIso (curveSquareMap P (H.curveAt t))
    (firstProjection X.variety.structureMap) (firstProjection P.structureMap)
    (H.curveAt t).map (curveSquareMap_first P (H.curveAt t)) E.sheaf
  apply (cancel_mono e.hom).mp
  change pullSection (curveSquareMap P (H.curveAt t))
      (pullSection (firstProjection X.variety.structureMap) a) ≫ e.hom =
    pullSection (curveSquareMap P (H.curveAt t))
      (pullSection (firstProjection X.variety.structureMap) b) ≫ e.hom
  dsimp only [e]
  rw [pullbackSquareIso_onSections, pullbackSquareIso_onSections, h t]

end FullFamilyDiagonalProof

/-- SOURCE jet:curve-expansion, constant term followed by continuation. -/
theorem fullFamily_diagonalValue (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X)
    (D : FamilyKernel P p X g) : FamilyKernel.HasZeroValue P p D := by
  have hz : pullSection (diagonal X.variety.structureMap) D.kernel = 0 := by
    apply FullFamilyDiagonalProof.detects_base_section P p X g D.family
      (pullbackBundle (diagonal X.variety.structureMap)
        (externalSquareLine X.variety.structureMap X.contact.sequence.line))
    intro t
    set_option backward.isDefEq.respectTransparency false in
      exact (FullFamilyDiagonalProof.curve_diagonal_zero P X.contact
        (D.family.curveAt t) D.kernel (D.fullIdentity t)).trans
          (FullFamilyDiagonalProof.pullSection_zero (D.family.curveAt t).map
            (E := pullbackModule (diagonal X.variety.structureMap)
              (externalSquareLine X.variety.structureMap X.contact.sequence.line).sheaf)).symm
  exact FullFamilyDiagonalProof.orderOne_of_diagonal_zero X.variety.structureMap D.kernel hz

end LeBrunSalamon.Refinement

end
