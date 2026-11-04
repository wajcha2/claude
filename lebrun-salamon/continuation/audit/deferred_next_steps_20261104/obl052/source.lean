import LSCotangentDeformations
import LSHomDegree

/-! Isolated project comparison for the two-point evaluation argument.
No original evaluation-dominance theorem or new admitted input is used.
The production source snapshot remains unchanged. -/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.Construction.Lines

namespace LeBrunSalamon.Next3i.HomPointDeformations

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

end LeBrunSalamon.Next3i.HomPointDeformations

#print axioms LeBrunSalamon.Next3i.HomPointDeformations.homPointDeformationEquiv
#print axioms LeBrunSalamon.Next3i.HomPointDeformations.pointLift_in_open

end
