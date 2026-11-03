import LSNodalTangent
import LSRelativeGenericSmoothness

/-!
# Extracting a very free conic from the actual smoothing

The smooth-source family is obtained from the explicit punctured-source
isomorphism. Parameter tangent directions give actual first-order maps
from P1; their two values are compared with the actual endpoint maps.
All declarations in this initial construction block are ordinary proofs.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTen
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFive LeBrunSalamon.Core LeBrunSalamon.Skeleton
open LeBrunSalamon.Refinement LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Smoothing.DegreeSpecialization.StandardInputs

/-- Classical degree-specialization corollary of Stacks 0B9T,
Lemma 36.32.2, applied to L and O, together with degree additivity
under the supplied closed pushout (0AYQ, Definition 33.44.1 and
Lemma 33.44.4; 0BEI, Lemma 33.33.2). The original P1 degree is the
O(1) exponent, identified by the cohomology calculation 01XS,
Lemma 30.8.1. The actual central gluing and every smooth-fibre
isomorphism are hypotheses. No existence of a smooth fibre is asserted.
This is a standard corollary, not a verbatim statement of one tag. -/
theorem degree_near_twoComponent_fibre
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {S Y : Scheme} [IsLocallyNoetherian S]
    (pi : Y ⟶ S) (sS : S ⟶ ComplexBase)
    [IsProper pi] [Flat pi] [LocallyOfFinitePresentation pi]
    (b0 : PointsOver ComplexBase (𝟙 ComplexBase) S sS)
    (i1 i2 : ProjectiveLine ⟶ pullback pi b0.val)
    [IsClosedImmersion i1] [IsClosedImmersion i2]
    (hi1 : i1 ≫ pullback.snd pi b0.val = P.structureMap)
    (hi2 : i2 ≫ pullback.snd pi b0.val = P.structureMap)
    (hpush : IsPushout p.map p.map i1 i2)
    (L : LineBundle Y) :
    ∃ U : S.Opens, Set.range b0.val ⊆ (U : Set S) ∧
      ∀ b : PointsOver ComplexBase (𝟙 ComplexBase) S sS,
        Set.range b.val ⊆ (U : Set S) →
        ∀ e : ProjectiveLine ≅ pullback pi b.val,
          e.hom ≫ pullback.snd pi b.val = P.structureMap →
          projectiveLineDegree P p
              (pullbackLine (e.hom ≫ pullback.fst pi b.val) L) =
            projectiveLineDegree P p
              (pullbackLine (i1 ≫ pullback.fst pi b0.val) L) +
            projectiveLineDegree P p
              (pullbackLine (i2 ≫ pullback.fst pi b0.val) L) := by
  sorry

end LeBrunSalamon.Construction.Smoothing.DegreeSpecialization.StandardInputs

namespace LeBrunSalamon.Construction.Smoothing.ConicExtraction

open Lines Charts.AffineTangentLift Normalization.NodalTangent

namespace AffineProduct

def product (A B : Charts.PointedAffine) : Charts.PointedAffine where
  scheme := pullback A.toC B.toC
  affine := inferInstance
  toC := pullback.fst A.toC B.toC ≫ A.toC
  point := ⟨pullback.lift A.point.val B.point.val
    (A.point.property.trans B.point.property.symm), by
      rw [pullback.lift_fst_assoc, A.point.property]⟩

def first (A B : Charts.PointedAffine) : Charts.Hom (product A B) A where
  map := pullback.fst A.toC B.toC
  overC := rfl
  atCentre := pullback.lift_fst _ _ _

def second (A B : Charts.PointedAffine) : Charts.Hom (product A B) B where
  map := pullback.snd A.toC B.toC
  overC := (pullback.condition (f := A.toC) (g := B.toC)).symm
  atCentre := pullback.lift_snd _ _ _

def pair {A B C : Charts.PointedAffine} (f : Charts.Hom A B)
    (g : Charts.Hom A C) : Charts.Hom A (product B C) where
  map := pullback.lift f.map g.map (f.overC.trans g.overC.symm)
  overC := by
    change pullback.lift f.map g.map (f.overC.trans g.overC.symm) ≫
      (pullback.fst B.toC C.toC ≫ B.toC) = A.toC
    rw [pullback.lift_fst_assoc, f.overC]
  atCentre := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc,
        f.atCentre, g.atCentre, product]

def compose {A B C : Charts.PointedAffine}
    (f : Charts.Hom A B) (g : Charts.Hom B C) : Charts.Hom A C where
  map := f.map ≫ g.map
  overC := by rw [Category.assoc, g.overC, f.overC]
  atCentre := by rw [← Category.assoc, f.atCentre, g.atCentre]

theorem compose_differential {A B C : Charts.PointedAffine}
    (f : Charts.Hom A B) (g : Charts.Hom B C) :
    (compose f g).differential = g.differential.comp f.differential := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  apply LinearMap.ext
  intro a
  rfl

def tangentCoordinates (A B : Charts.PointedAffine) :
    (product A B).Tangent →ₗ[ℂ] (A.Tangent × B.Tangent) :=
  (first A B).differential.prod (second A B).differential

theorem tangentCoordinates_bijective (A B : Charts.PointedAffine) :
    Function.Bijective (tangentCoordinates A B) := by
  constructor
  · intro v w h
    apply lift_injective (product A B)
    apply pointLift_ext_general
    apply pullback.hom_ext
    · change (lift (product A B) v).map ≫ (first A B).map =
        (lift (product A B) w).map ≫ (first A B).map
      rw [lift_natural (first A B), lift_natural (first A B)]
      exact congrArg (fun z : A.Tangent => (lift A z).map) (congrArg Prod.fst h)
    · change (lift (product A B) v).map ≫ (second A B).map =
        (lift (product A B) w).map ≫ (second A B).map
      rw [lift_natural (second A B), lift_natural (second A B)]
      exact congrArg (fun z : B.Tangent => (lift B z).map) (congrArg Prod.snd h)
  · rintro ⟨v, w⟩
    let t : Infinitesimal.PointLift (product A B).scheme
        (product A B).toC (product A B).point :=
      { map := pullback.lift (lift A v).map (lift B w).map
          ((lift A v).overC.trans (lift B w).overC.symm)
        overC := by
          change pullback.lift (lift A v).map (lift B w).map
              ((lift A v).overC.trans (lift B w).overC.symm) ≫
            (pullback.fst A.toC B.toC ≫ A.toC) = Infinitesimal.dualToC
          rw [pullback.lift_fst_assoc, (lift A v).overC]
        reduces := by
          apply pullback.hom_ext <;>
            simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
              pullback.lift_fst_assoc, pullback.lift_snd_assoc,
              (lift A v).reduces, (lift B w).reduces, product] }
    obtain ⟨z, hz⟩ := lift_surjective (product A B) t
    have hzmap : (lift (product A B) z).map = t.map :=
      congrArg
        (fun τ : Infinitesimal.PointLift (product A B).scheme
          (product A B).toC (product A B).point => τ.map) hz
    refine ⟨z, Prod.ext ?_ ?_⟩
    · apply lift_injective A
      apply pointLift_ext_general
      change (lift A ((first A B).differential z)).map = (lift A v).map
      calc
        _ = (lift (product A B) z).map ≫ (first A B).map :=
          (lift_natural (first A B) z).symm
        _ = t.map ≫ (first A B).map :=
          congrArg (fun k : Infinitesimal.DualScheme ⟶ (product A B).scheme =>
            k ≫ (first A B).map) hzmap
        _ = (lift A v).map := pullback.lift_fst _ _ _
    · apply lift_injective B
      apply pointLift_ext_general
      change (lift B ((second A B).differential z)).map = (lift B w).map
      calc
        _ = (lift (product A B) z).map ≫ (second A B).map :=
          (lift_natural (second A B) z).symm
        _ = t.map ≫ (second A B).map :=
          congrArg (fun k : Infinitesimal.DualScheme ⟶ (product A B).scheme =>
            k ≫ (second A B).map) hzmap
        _ = (lift B w).map := pullback.lift_snd _ _ _

def tangentEquiv (A B : Charts.PointedAffine) :
    (product A B).Tangent ≃ₗ[ℂ] (A.Tangent × B.Tangent) :=
  LinearEquiv.ofBijective (tangentCoordinates A B) (tangentCoordinates_bijective A B)

theorem pair_differential {A B C : Charts.PointedAffine}
    (f : Charts.Hom A B) (g : Charts.Hom A C) (v : A.Tangent) :
    tangentCoordinates B C ((pair f g).differential v) =
      (f.differential v, g.differential v) := by
  apply Prod.ext <;> apply Subtype.ext <;> apply LinearMap.ext
  · intro a
    change v.val (((pair f g).map ≫ (first B C).map).appTop a) = _
    rw [show (pair f g).map ≫ (first B C).map = f.map from
      pullback.lift_fst _ _ _]
    rfl
  · intro a
    change v.val (((pair f g).map ≫ (second B C).map).appTop a) = _
    rw [show (pair f g).map ≫ (second B C).map = g.map from
      pullback.lift_snd _ _ _]
    rfl

theorem pair_surjective_iff {A B C : Charts.PointedAffine}
    (f : Charts.Hom A B) (g : Charts.Hom A C) :
    Function.Surjective (pair f g).differential ↔
      Function.Surjective (f.differential.prod g.differential) := by
  constructor
  · intro h w
    obtain ⟨v, hv⟩ := h ((tangentEquiv B C).symm w)
    refine ⟨v, ?_⟩
    change (f.differential v, g.differential v) = w
    rw [← pair_differential f g, hv]
    exact (tangentEquiv B C).apply_symm_apply w
  · intro h w
    obtain ⟨v, hv⟩ := h (tangentCoordinates B C w)
    refine ⟨v, (tangentCoordinates_bijective B C).injective ?_⟩
    rw [pair_differential]
    exact hv

theorem smooth_pair_of_surjective {A B C : Charts.PointedAffine}
    (f : Charts.Hom A B) (g : Charts.Hom A C)
    (hA : Smooth A.toC) (hB : Smooth B.toC) (hC : Smooth C.toC)
    (h : Function.Surjective (f.differential.prod g.differential)) :
    Charts.SmoothAtCentre (pair f g) := by
  letI : Smooth B.toC := hB
  letI : Smooth C.toC := hC
  exact Charts.differential_surjective_implies_smooth (pair f g) hA
    (inferInstanceAs (Smooth (pullback.fst B.toC C.toC ≫ B.toC)))
    ((pair_surjective_iff f g).mpr h)

theorem surjective_pair_of_smooth {A B C : Charts.PointedAffine}
    (f : Charts.Hom A B) (g : Charts.Hom A C)
    (h : Smooth (pair f g).map) :
    Function.Surjective (f.differential.prod g.differential) := by
  apply (pair_surjective_iff f g).mp
  apply Charts.smooth_differential_surjective (pair f g)
  letI : Smooth (pair f g).map := h
  exact ⟨⊤, Set.subset_univ _, by infer_instance⟩

end AffineProduct

namespace ProductFamily

variable (Q : ProjectiveLineOverC) (A : Charts.PointedAffine)
variable {d : ℕ} (X : SmoothProperComplexVariety d)
variable (F : RationalSourceOver Q A.scheme A.toC ⟶ X.scheme)
variable (hF : F ≫ X.structureMap = pullback.fst Q.structureMap A.toC ≫ Q.structureMap)

def centralInclusion : ProjectiveLine ⟶ RationalSourceOver Q A.scheme A.toC :=
  pullback.lift (𝟙 ProjectiveLine) (Q.structureMap ≫ A.point.val)
    (by simp [Category.assoc, A.point.property])

def curveMap : ProjectiveLine ⟶ X.scheme := centralInclusion Q A ≫ F

include hF in
theorem curveMap_over : curveMap Q A X F ≫ X.structureMap = Q.structureMap := by
  rw [curveMap, Category.assoc, hF, centralInclusion,
    pullback.lift_fst_assoc, Category.id_comp]

def markedInclusion (p : ProjectiveLinePoint Q) :
    A.scheme ⟶ RationalSourceOver Q A.scheme A.toC :=
  pullback.lift (A.toC ≫ p.map) (𝟙 A.scheme)
    (by simp [Category.assoc, p.overC])

def evaluation (p : ProjectiveLinePoint Q) : A.scheme ⟶ X.scheme :=
  markedInclusion Q A p ≫ F

include hF in
theorem evaluation_over (p : ProjectiveLinePoint Q) :
    evaluation Q A X F p ≫ X.structureMap = A.toC := by
  rw [evaluation, Category.assoc, hF, markedInclusion, pullback.lift_fst_assoc,
    Category.assoc, p.overC, Category.comp_id]

theorem evaluation_centre (p : ProjectiveLinePoint Q) :
    A.point.val ≫ evaluation Q A X F p = p.map ≫ curveMap Q A X F := by
  dsimp only [evaluation, curveMap]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simpa only [markedInclusion, centralInclusion, Category.assoc,
      pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id, Category.id_comp] using
      congrArg (fun k : ComplexBase ⟶ ComplexBase => k ≫ p.map) A.point.property
  · simpa only [markedInclusion, centralInclusion, Category.assoc,
      pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp] using
      (congrArg (fun k : ComplexBase ⟶ ComplexBase => k ≫ A.point.val) p.overC).symm

def imagePoint (p : ProjectiveLinePoint Q) : ComplexPoint X where
  map := p.map ≫ curveMap Q A X F
  overC := by rw [Category.assoc, curveMap_over Q A X F hF, p.overC]

def deformation (v : A.Tangent) :
    FamilyVariation.Deformation Q.structureMap X.structureMap (curveMap Q A X F) where
  map := rationalSourceMap Q ⟨(lift A v).map, (lift A v).overC⟩ ≫ F
  overC := by
    rw [Category.assoc, hF, ← Category.assoc]
    congr 1
    exact pullback.lift_fst _ _ _
  reduces := by
    dsimp only [curveMap]
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp [rationalSourceMap, centralInclusion, DualThickening.zeroSection,
        Category.assoc]
    · simp only [Category.assoc, rationalSourceMap, pullback.lift_snd,
        pullback.lift_snd_assoc]
      change DualThickening.zeroSection Q.structureMap ≫
          DualThickening.parameter Q.structureMap ≫ (lift A v).map =
        centralInclusion Q A ≫ pullback.snd Q.structureMap A.toC
      rw [← Category.assoc, DualThickening.zeroSection_parameter,
        Category.assoc, (lift A v).reduces]
      exact (pullback.lift_snd _ _ _).symm

/-- Infer the original target point from its supplied morphism, retaining the actual push. -/
private def pushToMap {S T : Scheme} {sS : S ⟶ ComplexBase} {sT : T ⟶ ComplexBase}
    {s : PointsOver ComplexBase (𝟙 ComplexBase) S sS} {t : ComplexBase ⟶ T}
    (g : S ⟶ T) (hg : g ≫ sT = sS) (hat : s.val ≫ g = t)
    (v : Infinitesimal.PointLift S sS s) :
    Infinitesimal.PointLift T sT
      ⟨t, by rw [← hat, Category.assoc, hg, s.property]⟩ :=
  Charts.AffineTangentLift.push (s := s)
    (t := ⟨t, by rw [← hat, Category.assoc, hg, s.property]⟩) g hg hat v

private theorem pushToMap_eq_push {S T : Scheme}
    {sS : S ⟶ ComplexBase} {sT : T ⟶ ComplexBase}
    {s : PointsOver ComplexBase (𝟙 ComplexBase) S sS}
    {t : PointsOver ComplexBase (𝟙 ComplexBase) T sT}
    (g : S ⟶ T) (hg : g ≫ sT = sS) (hat : s.val ≫ g = t.val)
    (v : Infinitesimal.PointLift S sS s) :
    pushToMap (s := s) (t := t.val) g hg hat v =
      Charts.AffineTangentLift.push (s := s) (t := t) g hg hat v := by
  rfl

section DeformationAtPointTarget

local notation "push" => pushToMap

theorem deformation_atPoint (p : ProjectiveLinePoint Q) (v : A.Tangent) :
    (deformation Q A X F hF v).pullback p.map p.overC =
      SourceTangent.pointDeformation
        (push (evaluation Q A X F p) (evaluation_over Q A X F hF p)
          (evaluation_centre Q A X F p) (lift A v)) := by
  apply FamilyVariation.Deformation.ext
  change DualThickening.map p.map p.overC ≫
      (rationalSourceMap Q ⟨(lift A v).map, (lift A v).overC⟩ ≫ F) =
    DualThickening.parameter (𝟙 ComplexBase) ≫
      ((lift A v).map ≫ (markedInclusion Q A p ≫ F))
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, rationalSourceMap, pullback.lift_fst,
      pullback.lift_fst_assoc, markedInclusion]
    change DualThickening.map p.map p.overC ≫ DualThickening.projection Q.structureMap =
      DualThickening.parameter (𝟙 ComplexBase) ≫ (lift A v).map ≫ A.toC ≫ p.map
    rw [DualThickening.map_projection]
    have hc : (lift A v).map ≫ A.toC ≫ p.map = Infinitesimal.dualToC ≫ p.map := by
      rw [← Category.assoc, (lift A v).overC]
    rw [hc, ← Category.assoc, DualThickening.parameter_overC]
    rfl
  · simp only [Category.assoc, rationalSourceMap, pullback.lift_snd,
      pullback.lift_snd_assoc, markedInclusion, Category.comp_id]
    change DualThickening.map p.map p.overC ≫
        DualThickening.parameter Q.structureMap ≫ (lift A v).map =
      DualThickening.parameter (𝟙 ComplexBase) ≫ (lift A v).map
    simpa only [Category.assoc] using
      congrArg
        (fun k : DualThickening.space (𝟙 ComplexBase) ⟶ Infinitesimal.DualScheme =>
          k ≫ (lift A v).map)
        (DualThickening.map_parameter p.map p.overC)

end DeformationAtPointTarget

theorem variation_atPoint (p : ProjectiveLinePoint Q) (v : A.Tangent) :
    fiberComposition (curveMap Q A X F) p.map (imagePoint Q A X F hF p).map rfl
        (tangentSheaf X.structureMap)
        (evaluateSection Q.structureMap
          (pullbackModule (curveMap Q A X F) (tangentSheaf X.structureMap))
          p.map p.overC ((deformation Q A X F hF v).variation X)) =
      SourceTangent.pointVector X (imagePoint Q A X F hF p)
        (push (evaluation Q A X F p) (evaluation_over Q A X F hF p)
          (evaluation_centre Q A X F p) (lift A v)) := by
  change onCSections (𝟙 ComplexBase)
      (compositionPullback p.map (curveMap Q A X F)
        (p.map ≫ curveMap Q A X F) rfl (tangentSheaf X.structureMap)).hom
      (Normalization.pullCSections p.map (𝟙 ComplexBase) Q.structureMap p.overC
        (pullbackModule (curveMap Q A X F) (tangentSheaf X.structureMap))
        ((deformation Q A X F hF v).variation X)) = _
  rw [variation_pullback, deformation_atPoint]
  rfl

def endpointFibre (p : ProjectiveLinePoint Q)
    (B : Charts.PointedAffine) (j : B.scheme ⟶ X.scheme)
    [IsOpenImmersion j] (hj : j ≫ X.structureMap = B.toC)
    (e : Charts.Hom A B) (he : evaluation Q A X F p = e.map ≫ j) :
    B.Tangent ≃ₗ[ℂ]
      Fiber (pullbackModule (curveMap Q A X F) (tangentSheaf X.structureMap)) p.map :=
  (AffineIntrinsic.tangentEquiv B X (imagePoint Q A X F hF p) j hj
    (by rw [← e.atCentre, Category.assoc, ← he]; exact evaluation_centre Q A X F p)).trans
    (LinearEquiv.ofBijective
      (fiberComposition (curveMap Q A X F) p.map (imagePoint Q A X F hF p).map
        rfl (tangentSheaf X.structureMap))
      (fiberComposition_bijective (curveMap Q A X F) p.map
        (imagePoint Q A X F hF p).map rfl (tangentSheaf X.structureMap))).symm

theorem endpointFibre_value (p : ProjectiveLinePoint Q)
    (B : Charts.PointedAffine) (j : B.scheme ⟶ X.scheme)
    [IsOpenImmersion j] (hj : j ≫ X.structureMap = B.toC)
    (e : Charts.Hom A B) (he : evaluation Q A X F p = e.map ≫ j)
    (v : A.Tangent) :
    endpointFibre Q A X F hF p B j hj e he (e.differential v) =
      evaluateSection Q.structureMap
        (pullbackModule (curveMap Q A X F) (tangentSheaf X.structureMap))
        p.map p.overC ((deformation Q A X F hF v).variation X) := by
  apply (fiberComposition_bijective (curveMap Q A X F) p.map
    (imagePoint Q A X F hF p).map rfl (tangentSheaf X.structureMap)).injective
  let c := LinearEquiv.ofBijective
    (fiberComposition (curveMap Q A X F) p.map (imagePoint Q A X F hF p).map
      rfl (tangentSheaf X.structureMap))
    (fiberComposition_bijective (curveMap Q A X F) p.map
      (imagePoint Q A X F hF p).map rfl (tangentSheaf X.structureMap))
  change c (c.symm (AffineIntrinsic.tangentEquiv B X
    (imagePoint Q A X F hF p) j hj _ (e.differential v))) = _
  rw [LinearEquiv.apply_symm_apply]
  rw [AffineIntrinsic.tangentEquiv_pointVector, variation_atPoint]
  congr 1
  apply pointLift_ext_general
  change (lift B (e.differential v)).map ≫ j =
    (lift A v).map ≫ evaluation Q A X F p
  rw [he, ← Category.assoc, lift_natural]

include hF in
theorem twoPointEvaluation_surjective
    (p q : ProjectiveLinePoint Q)
    (B C : Charts.PointedAffine) (j : B.scheme ⟶ X.scheme) (k : C.scheme ⟶ X.scheme)
    [IsOpenImmersion j] [IsOpenImmersion k]
    (hj : j ≫ X.structureMap = B.toC) (hk : k ≫ X.structureMap = C.toC)
    (e : Charts.Hom A B) (f : Charts.Hom A C)
    (he : evaluation Q A X F p = e.map ≫ j)
    (hf : evaluation Q A X F q = f.map ≫ k)
    (hs : Function.Surjective (e.differential.prod f.differential)) :
    Function.Surjective (twoPointBundleEvaluation Q p q
      (pullbackModule (curveMap Q A X F) (tangentSheaf X.structureMap))) := by
  apply (PositiveNodeImage.suppliedPairEvaluation_surjective_iff_restriction Q _ p q).mp
  rintro ⟨a, b⟩
  let ep := endpointFibre Q A X F hF p B j hj e he
  let eq := endpointFibre Q A X F hF q C k hk f hf
  obtain ⟨v, hv⟩ := hs (ep.symm a, eq.symm b)
  refine ⟨(deformation Q A X F hF v).variation X, Prod.ext ?_ ?_⟩
  · change evaluateSection Q.structureMap _ p.map p.overC _ = a
    rw [← endpointFibre_value Q A X F hF p B j hj e he,
      show e.differential v = ep.symm a from congrArg Prod.fst hv]
    exact ep.apply_symm_apply a
  · change evaluateSection Q.structureMap _ q.map q.overC _ = b
    rw [← endpointFibre_value Q A X F hF q C k hk f hf,
      show f.differential v = eq.symm b from congrArg Prod.snd hv]
    exact eq.apply_symm_apply b

end ProductFamily

/-- Interpolation at one actual distinct pair implies interpolation at
every pair, by the existing actual Birkhoff--Grothendieck splitting. -/
theorem twoPointGeneration_of_onePair (Q : ProjectiveLineOverC)
    (p q : ProjectiveLinePoint Q) (hpq : p.map ≠ q.map)
    {r : ℕ} (E : AlgebraicVectorBundle ProjectiveLine r)
    (h : Function.Surjective (twoPointBundleEvaluation Q p q E.sheaf)) :
    IsTwoPointGloballyGenerated Q E.sheaf := by
  obtain ⟨a, ha⟩ := birkhoffGrothendieck Q p E
  have hpos := (splitBundle_twoPointEvaluation_iff Q p q hpq E a ha).mp h
  refine ⟨⟨p, q, hpq⟩, ?_⟩
  intro x y hxy
  apply (DirectSumEvaluation.twoPointBundleEvaluation_iso_iff Q x y (Classical.choice ha)).mpr
  exact (LeBrunSalamon.P1SplitBundles.splitSheaf_twoPointEvaluation_iff
    Q p a Q x y hxy).mpr hpos

theorem affineLine_smooth : Smooth affineLineToC := by
  change Smooth (Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ)))
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  apply RingHom.smooth_algebraMap.mpr
  constructor <;> infer_instance

theorem smooth_on_smaller_open {Y Z : Scheme} (f : Y ⟶ Z)
    (U V : Y.Opens) (hVU : V ≤ U) (h : Smooth (U.ι ≫ f)) :
    Smooth (V.ι ≫ f) := by
  letI : Smooth (U.ι ≫ f) := h
  have hs : Smooth (Y.homOfLE hVU ≫ (U.ι ≫ f)) := inferInstance
  simpa only [← Category.assoc, Scheme.homOfLE_ι] using hs

variable {n : ℕ} {X : ContactFanoManifold n} {D : SuitablePair X}

/-- An actual affine neighborhood, obtained by shrinking the given
Hom chart; the two smooth morphisms are its original parameter and
endpoint maps. This package is constructed below, never admitted. -/
structure Neighborhood (G : Germ D) where
  chart : Charts.PointedAffine
  inclusion : Charts.Hom chart G.chart
  immersion : IsOpenImmersion inclusion.map
  baseSmooth : Smooth (inclusion.map ≫ G.inclusion ≫ G.hom.toBase)
  endpointSmooth : Smooth
    (AffineProduct.pair (AffineProduct.compose inclusion G.firstEval)
      (AffineProduct.compose inclusion G.secondEval)).map

theorem neighborhood_exists (G : Germ D)
    (he : Function.Surjective G.endpointDifferential) : Nonempty (Neighborhood G) := by
  letI : Smooth affineLineToC := affineLine_smooth
  letI : IsOpenImmersion G.firstOpen := G.firstOpen_immersion
  letI : IsOpenImmersion G.secondOpen := G.secondOpen_immersion
  have hfirst : Smooth G.firstTarget.toC := by
    rw [← G.firstOpen_over]
    infer_instance
  have hsecond : Smooth G.secondTarget.toC := by
    rw [← G.secondOpen_over]
    infer_instance
  obtain ⟨U, hpU, hU⟩ := germ_smoothingMap_smooth G
  obtain ⟨V, hV, hpV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (X := G.chart.scheme) (x := G.chart.point.val (default : PrimeSpectrum ℂ))
    (U := U) (by
      change G.chart.point.val (default : PrimeSpectrum ℂ) ∈ (U : Set G.chart.scheme)
      exact hpU (Set.mem_range_self (default : PrimeSpectrum ℂ)))
  have hpr := GermProof.point_range_in_open G.chart.point.val V hpV
  let A := GermProof.chartOfOpen G.chart.toC G.chart.point V hV hpr
  let i : Charts.Hom A G.chart :=
    { map := V.ι
      overC := rfl
      atCentre := GermProof.chartOfOpen_point G.chart.toC G.chart.point V hV hpr }
  letI : IsOpenImmersion i.map := inferInstanceAs (IsOpenImmersion V.ι)
  have hs : Smooth (i.map ≫ G.inclusion ≫ G.hom.toBase) :=
    smooth_on_smaller_open (G.inclusion ≫ G.hom.toBase) U V hVU hU
  letI : Smooth (i.map ≫ G.inclusion ≫ G.hom.toBase) := hs
  have hA : Smooth A.toC := by
    have h : Smooth ((i.map ≫ G.inclusion ≫ G.hom.toBase) ≫ affineLineToC) :=
      inferInstance
    simpa only [Category.assoc, G.chart_overC, i.overC] using h
  let e := AffineProduct.compose i G.firstEval
  let f := AffineProduct.compose i G.secondEval
  have hpair : Function.Surjective (e.differential.prod f.differential) := by
    intro w
    obtain ⟨v, hv⟩ := he w
    obtain ⟨u, hu⟩ := (open_differential_bijective i).surjective v
    refine ⟨u, ?_⟩
    change (e.differential u, f.differential u) = w
    simp only [e, f, AffineProduct.compose_differential, LinearMap.comp_apply, hu]
    exact hv
  obtain ⟨W, hpW, hW⟩ :=
    AffineProduct.smooth_pair_of_surjective e f hA hfirst hsecond hpair
  obtain ⟨Z, hZ, hpZ, hZW⟩ := exists_isAffineOpen_mem_and_subset
    (X := A.scheme) (x := A.point.val (default : PrimeSpectrum ℂ))
    (U := W) (by
      change A.point.val (default : PrimeSpectrum ℂ) ∈ (W : Set A.scheme)
      exact hpW (Set.mem_range_self (default : PrimeSpectrum ℂ)))
  have hpZr := GermProof.point_range_in_open A.point.val Z hpZ
  let B := GermProof.chartOfOpen A.toC A.point Z hZ hpZr
  let j : Charts.Hom B A :=
    { map := Z.ι
      overC := rfl
      atCentre := GermProof.chartOfOpen_point A.toC A.point Z hZ hpZr }
  let k := AffineProduct.compose j i
  have hk : IsOpenImmersion k.map := by
    change IsOpenImmersion (Z.ι ≫ V.ι)
    infer_instance
  have hbase : Smooth (k.map ≫ G.inclusion ≫ G.hom.toBase) := by
    have h : Smooth (Z.ι ≫ (i.map ≫ G.inclusion ≫ G.hom.toBase)) := inferInstance
    simpa only [k, AffineProduct.compose, Category.assoc] using h
  have hmap : (AffineProduct.pair (AffineProduct.compose k G.firstEval)
      (AffineProduct.compose k G.secondEval)).map =
      Z.ι ≫ (AffineProduct.pair e f).map := by
    apply pullback.hom_ext <;>
      simp [AffineProduct.pair, AffineProduct.compose, k, e, f, Category.assoc, j]
  refine ⟨⟨B, k, hk, hbase, ?_⟩⟩
  rw [hmap]
  exact smooth_on_smaller_open (AffineProduct.pair e f).map W Z hZW hW

namespace Neighborhood

variable {G : Germ D} (N : Neighborhood G)

def toHom : N.chart.scheme ⟶ G.hom.parameter := N.inclusion.map ≫ G.inclusion

def toBase : N.chart.scheme ⟶ AffineLine := N.toHom ≫ G.hom.toBase

theorem overC : N.toBase ≫ affineLineToC = N.chart.toC := by
  rw [toBase, toHom, Category.assoc, Category.assoc, G.chart_overC,
    N.inclusion.overC]

theorem centre_base : N.chart.point.val ≫ N.toBase = scalarPoint 0 := by
  rw [toBase, toHom, ← Category.assoc, ← Category.assoc,
    N.inclusion.atCentre, Category.assoc, G.centre_base]

theorem smooth : Smooth N.chart.toC := by
  letI : Smooth N.toBase := N.baseSmooth
  letI : Smooth affineLineToC := affineLine_smooth
  rw [← N.overC]
  infer_instance

def firstEval : Charts.Hom N.chart G.firstTarget :=
  AffineProduct.compose N.inclusion G.firstEval

def secondEval : Charts.Hom N.chart G.secondTarget :=
  AffineProduct.compose N.inclusion G.secondEval

theorem firstEval_spec : N.firstEval.map ≫ G.firstOpen =
    N.toHom ≫ markedEvaluation G.hom G.marks.first G.marks.first_base := by
  simp only [firstEval, AffineProduct.compose, toHom, Category.assoc, G.firstEval_spec]

theorem secondEval_spec : N.secondEval.map ≫ G.secondOpen =
    N.toHom ≫ markedEvaluation G.hom G.marks.second G.marks.second_base := by
  simp only [secondEval, AffineProduct.compose, toHom, Category.assoc, G.secondEval_spec]

end Neighborhood

/-- The literal fibre of a base-changed source, with both projections
fixed. No identification of fibres is made only up to their points. -/
def baseChangedFibreIso (F : StandardSource) {T : Scheme}
    (t : T ⟶ AffineLine) (x : ComplexBase ⟶ T)
    (c : ComplexBase ⟶ AffineLine) (hx : x ≫ t = c) :
    SourceOver F c ≅ pullback (pullback.snd F.parameter t) x where
  hom := pullback.lift (sourceBaseChangeMap F c t x hx)
    (pullback.snd F.parameter c) (by simp [sourceBaseChangeMap])
  inv := pullback.lift
    (pullback.fst (pullback.snd F.parameter t) x ≫ pullback.fst F.parameter t)
    (pullback.snd (pullback.snd F.parameter t) x) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc,
        pullback.condition, Category.assoc, hx])
  hom_inv_id := by
    apply pullback.hom_ext <;>
      simp [sourceBaseChangeMap, Category.assoc]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;>
        simp [sourceBaseChangeMap, Category.assoc, pullback.condition]
    · simp

@[reassoc] theorem baseChangedFibreIso_first (F : StandardSource) {T : Scheme}
    (t : T ⟶ AffineLine) (x : ComplexBase ⟶ T)
    (c : ComplexBase ⟶ AffineLine) (hx : x ≫ t = c) :
    (baseChangedFibreIso F t x c hx).hom ≫
      pullback.fst (pullback.snd F.parameter t) x = sourceBaseChangeMap F c t x hx :=
  pullback.lift_fst _ _ _

@[reassoc] theorem baseChangedFibreIso_base (F : StandardSource) {T : Scheme}
    (t : T ⟶ AffineLine) (x : ComplexBase ⟶ T)
    (c : ComplexBase ⟶ AffineLine) (hx : x ≫ t = c) :
    (baseChangedFibreIso F t x c hx).hom ≫
      pullback.snd (pullback.snd F.parameter t) x = pullback.snd F.parameter c :=
  pullback.lift_snd _ _ _

theorem degree_composite (Q : ProjectiveLineOverC) (p : ProjectiveLinePoint Q)
    {Y Z : Scheme} (f : ProjectiveLine ⟶ Y) (g : Y ⟶ Z) (L : LineBundle Z) :
    projectiveLineDegree Q p (pullbackLine f (pullbackLine g L)) =
      projectiveLineDegree Q p (pullbackLine (f ≫ g) L) :=
  projectiveLineDegree_iso Q p _ _ (compositionPullback f g (f ≫ g) rfl L.sheaf)

namespace Neighborhood

variable {G : Germ D} (N : Neighborhood G)

abbrev familySource := SourceOver G.source N.toBase

def familyParameter : N.familySource ⟶ N.chart.scheme :=
  pullback.snd G.source.parameter N.toBase

def familyEvaluation : N.familySource ⟶ X.variety.scheme :=
  sourceBaseChangeMap G.source N.toBase G.hom.toBase N.toHom rfl ≫ G.hom.evaluation

theorem familyEvaluation_over :
    N.familyEvaluation ≫ X.variety.structureMap = N.familyParameter ≫ N.chart.toC := by
  calc
    N.familyEvaluation ≫ X.variety.structureMap =
        N.familyParameter ≫ N.toBase ≫ affineLineToC := by
      simp only [familyEvaluation, Category.assoc, G.hom.overC, sourceBaseChangeMap,
        pullback.lift_snd_assoc, familyParameter, toBase]
    _ = N.familyParameter ≫ N.chart.toC :=
      congrArg (fun k : N.chart.scheme ⟶ ComplexBase => N.familyParameter ≫ k) N.overC

def centralIso : Normalization.CentralFiber G.source ≅
    pullback N.familyParameter N.chart.point.val :=
  baseChangedFibreIso G.source N.toBase N.chart.point.val (scalarPoint 0) N.centre_base

def centralFirst : ProjectiveLine ⟶ pullback N.familyParameter N.chart.point.val :=
  Normalization.leftBranch G.marks ≫ N.centralIso.hom

def centralSecond : ProjectiveLine ⟶ pullback N.familyParameter N.chart.point.val :=
  Normalization.rightBranch G.marks ≫ N.centralIso.hom

theorem centralFirst_over :
    N.centralFirst ≫ pullback.snd N.familyParameter N.chart.point.val = P.structureMap := by
  have h : N.centralIso.hom ≫ pullback.snd N.familyParameter N.chart.point.val =
      pullback.snd G.source.parameter (scalarPoint 0) :=
    baseChangedFibreIso_base G.source N.toBase N.chart.point.val (scalarPoint 0)
      N.centre_base
  change (Normalization.leftBranch G.marks ≫ N.centralIso.hom) ≫
    pullback.snd N.familyParameter N.chart.point.val = P.structureMap
  rw [Category.assoc, h]
  exact Normalization.leftBranch_over G.marks

theorem centralSecond_over :
    N.centralSecond ≫ pullback.snd N.familyParameter N.chart.point.val = P.structureMap := by
  have h : N.centralIso.hom ≫ pullback.snd N.familyParameter N.chart.point.val =
      pullback.snd G.source.parameter (scalarPoint 0) :=
    baseChangedFibreIso_base G.source N.toBase N.chart.point.val (scalarPoint 0)
      N.centre_base
  change (Normalization.rightBranch G.marks ≫ N.centralIso.hom) ≫
    pullback.snd N.familyParameter N.chart.point.val = P.structureMap
  rw [Category.assoc, h]
  exact Normalization.rightBranch_over G.marks

theorem central_pushout :
    IsPushout marking.map marking.map N.centralFirst N.centralSecond := by
  apply IsPushout.mk'
  · rw [centralFirst, centralSecond, ← Category.assoc, ← Category.assoc,
      Normalization.branches_meet]
  · intro Z f g hf hg
    apply (cancel_epi N.centralIso.hom).mp
    exact Normalization.centralFiber_hom_ext G.marks
      (by simpa only [centralFirst, Category.assoc] using hf)
      (by simpa only [centralSecond, Category.assoc] using hg)
  · intro Z f g h
    obtain ⟨u, hu, _⟩ := Normalization.centralFiber_pushout G.marks Z f g h
    refine ⟨N.centralIso.inv ≫ u, ?_, ?_⟩
    · simpa only [centralFirst, Category.assoc, Iso.hom_inv_id_assoc] using hu.1
    · simpa only [centralSecond, Category.assoc, Iso.hom_inv_id_assoc] using hu.2

theorem centralEvaluation :
    N.centralIso.hom ≫ pullback.fst N.familyParameter N.chart.point.val ≫
      N.familyEvaluation = Normalization.centralMap G := by
  have h : N.centralIso.hom ≫ pullback.fst N.familyParameter N.chart.point.val =
      sourceBaseChangeMap G.source (scalarPoint 0) N.toBase N.chart.point.val
        N.centre_base :=
    baseChangedFibreIso_first G.source N.toBase N.chart.point.val (scalarPoint 0)
      N.centre_base
  rw [← Category.assoc, h]
  dsimp only [familyEvaluation, Normalization.centralMap]
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp [sourceBaseChangeMap, Category.assoc]
  · simp only [sourceBaseChangeMap, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc]
    congr 1
    change N.chart.point.val ≫ (N.inclusion.map ≫ G.inclusion) =
      G.chart.point.val ≫ G.inclusion
    rw [← Category.assoc, N.inclusion.atCentre]

theorem centralFirst_evaluation :
    N.centralFirst ≫ pullback.fst N.familyParameter N.chart.point.val ≫
      N.familyEvaluation = D.first.curve.map := by
  rw [centralFirst, Category.assoc, N.centralEvaluation]
  exact Normalization.centralMap_left G

theorem centralSecond_evaluation :
    N.centralSecond ≫ pullback.fst N.familyParameter N.chart.point.val ≫
      N.familyEvaluation = D.second.curve.map := by
  rw [centralSecond, Category.assoc, N.centralEvaluation]
  exact Normalization.centralMap_right G

/-- The degree-two neighborhood is derived from the published generic
degree theorem after supplying the actual central gluing and both
original degree-one curve maps. -/
theorem degree_neighborhood :
    ∃ U : N.chart.scheme.Opens, Set.range N.chart.point.val ⊆ (U : Set N.chart.scheme) ∧
      ∀ b : PointsOver ComplexBase (𝟙 ComplexBase) N.chart.scheme N.chart.toC,
        Set.range b.val ⊆ (U : Set N.chart.scheme) →
        ∀ e : ProjectiveLine ≅ pullback N.familyParameter b.val,
          e.hom ≫ pullback.snd N.familyParameter b.val = P.structureMap →
          projectiveLineDegree P marking
            (pullbackLine (e.hom ≫ pullback.fst N.familyParameter b.val ≫
              N.familyEvaluation) X.contact.sequence.line) = 2 := by
  letI : Smooth N.chart.toC := N.smooth
  letI : IsLocallyNoetherian N.chart.scheme :=
    LocallyOfFiniteType.isLocallyNoetherian N.chart.toC
  letI : IsProper G.source.parameter := standardSource_proper G.source
  letI : Flat G.source.parameter := standardSource_flat G.source
  letI : LocallyOfFinitePresentation G.source.parameter := standardSource_lfp G.source
  letI : IsProper N.familyParameter := inferInstanceAs
    (IsProper (pullback.snd G.source.parameter N.toBase))
  letI : Flat N.familyParameter := inferInstanceAs
    (Flat (pullback.snd G.source.parameter N.toBase))
  letI : LocallyOfFinitePresentation N.familyParameter := inferInstanceAs
    (LocallyOfFinitePresentation (pullback.snd G.source.parameter N.toBase))
  letI : IsClosedImmersion (Normalization.leftBranch G.marks) :=
    (Normalization.centralFiber_branches_closed G.marks).1
  letI : IsClosedImmersion (Normalization.rightBranch G.marks) :=
    (Normalization.centralFiber_branches_closed G.marks).2
  letI : IsClosedImmersion N.centralFirst := inferInstanceAs
    (IsClosedImmersion (Normalization.leftBranch G.marks ≫ N.centralIso.hom))
  letI : IsClosedImmersion N.centralSecond := inferInstanceAs
    (IsClosedImmersion (Normalization.rightBranch G.marks ≫ N.centralIso.hom))
  obtain ⟨U, hU, hdeg⟩ :=
    DegreeSpecialization.StandardInputs.degree_near_twoComponent_fibre P marking
      N.familyParameter N.chart.toC N.chart.point N.centralFirst N.centralSecond
      N.centralFirst_over N.centralSecond_over N.central_pushout
      (pullbackLine N.familyEvaluation X.contact.sequence.line)
  refine ⟨U, hU, ?_⟩
  intro b hb e he
  have h := hdeg b hb e he
  simp only [degree_composite, Category.assoc,
    N.centralFirst_evaluation, N.centralSecond_evaluation] at h
  change projectiveLineDegree P marking
      (pullbackLine (e.hom ≫ pullback.fst N.familyParameter b.val ≫
        N.familyEvaluation) X.contact.sequence.line) = _ at h
  rw [show projectiveLineDegree P marking
      (pullbackLine D.first.curve.map X.contact.sequence.line) = 1 from D.first.degreeOne,
    show projectiveLineDegree P marking
      (pullbackLine D.second.curve.map X.contact.sequence.line) = 1 from D.second.degreeOne] at h
  exact h

end Neighborhood

theorem puncturedParameter_dense : Dense (puncturedParameter : Set AffineLine) := by
  apply puncturedParameter.isOpen.dense
  refine ⟨⟨⊥, inferInstance⟩, ?_⟩
  change (⟨⊥, inferInstance⟩ : PrimeSpectrum (Polynomial ℂ)) ∈
    (Spec (CommRingCat.of (Polynomial ℂ))).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).inv Polynomial.X)
  rw [basicOpen_eq_of_affine, PrimeSpectrum.mem_basicOpen]
  simpa only [Ideal.mem_bot] using (Polynomial.X_ne_zero : (Polynomial.X : Polynomial ℂ) ≠ 0)

theorem Neighborhood.point_in_puncture {G : Germ D} (N : Neighborhood G)
    (U : N.chart.scheme.Opens) (hU : Set.range N.chart.point.val ⊆ (U : Set N.chart.scheme)) :
    ∃ b : PointsOver ComplexBase (𝟙 ComplexBase) N.chart.scheme N.chart.toC,
      Set.range b.val ⊆ (U : Set N.chart.scheme) ∧
      Set.range (b.val ≫ N.toBase) ⊆ (puncturedParameter : Set AffineLine) := by
  letI : Smooth N.toBase := N.baseSmooth
  letI : Smooth N.chart.toC := N.smooth
  let W : N.chart.scheme.Opens := U ⊓ N.toBase ⁻¹ᵁ puncturedParameter
  have himage : (N.toBase '' (U : Set N.chart.scheme)).Nonempty :=
    ⟨N.toBase (N.chart.point.val (default : PrimeSpectrum ℂ)),
      N.chart.point.val (default : PrimeSpectrum ℂ),
      hU (Set.mem_range_self (default : PrimeSpectrum ℂ)), rfl⟩
  obtain ⟨s, ⟨z, hz, hzs⟩, hs⟩ := puncturedParameter_dense.inter_open_nonempty
    (N.toBase '' (U : Set N.chart.scheme)) (N.toBase.isOpenMap _ U.isOpen) himage
  have hW : (W : Set N.chart.scheme).Nonempty := ⟨z, hz, by simpa [hzs] using hs⟩
  obtain ⟨b, hb, hbW⟩ := RelativeGenericSmoothness.exists_point_in_nonempty_open
    N.chart.toC W hW
  have hbr : Set.range b ⊆ (W : Set N.chart.scheme) :=
    GermProof.point_range_in_open b W
      (by
        have hd : (default : PrimeSpectrum ℂ) = IsLocalRing.closedPoint ℂ :=
          Subsingleton.elim _ _
        change b (default : PrimeSpectrum ℂ) ∈ (W : Set N.chart.scheme)
        change b (IsLocalRing.closedPoint ℂ) ∈ (W : Set N.chart.scheme) at hbW
        simpa only [hd] using hbW)
  refine ⟨⟨b, hb⟩, ?_, ?_⟩
  · intro z hz
    exact (hbr hz).1
  · rintro _ ⟨z, rfl⟩
    exact (hbr ⟨z, rfl⟩).2

namespace PuncturedModel

open PuncturedSourceProof

variable (F : StandardSource) {T : Scheme}
variable (sT : T ⟶ ComplexBase) (t : T ⟶ AffineLine)
variable (ht : t ≫ affineLineToC = sT)
variable (hstar : Set.range t ⊆ (puncturedParameter : Set AffineLine))

def base : T ⟶ Base := IsOpenImmersion.lift puncturedParameter.ι t
  (by simpa only [Scheme.Opens.range_ι] using hstar)

@[reassoc] theorem base_spec : base t hstar ≫ puncturedParameter.ι = t :=
  IsOpenImmersion.lift_fac _ _ _

include ht in
theorem base_over : base t hstar ≫ baseMap = sT := by
  rw [baseMap, ← Category.assoc, base_spec, ht]

def toProduct : RationalSourceOver P T sT ⟶ Product :=
  rationalSourceMap P ⟨base t hstar, base_over sT t ht hstar⟩

@[reassoc] theorem toProduct_left : toProduct sT t ht hstar ≫ productLeft =
    pullback.fst P.structureMap sT := by simp [toProduct, rationalSourceMap, productLeft]

@[reassoc] theorem toProduct_base : toProduct sT t ht hstar ≫ productBase =
    pullback.snd P.structureMap sT ≫ base t hstar := by
  simp [toProduct, rationalSourceMap, productBase]

@[reassoc] theorem inverse_base : inverse F ≫ starBase F = productBase := by
  rw [← projection_base, ← Category.assoc, inverse_projection, Category.id_comp]

@[reassoc] theorem inverse_left : inverse F ≫ starSource F ≫ F.left = productLeft := by
  rw [← projection_left, ← Category.assoc, inverse_projection, Category.id_comp]

def sourceMap : RationalSourceOver P T sT ⟶ F.source :=
  toProduct sT t ht hstar ≫ inverse F ≫ starSource F

@[reassoc] theorem sourceMap_parameter : sourceMap F sT t ht hstar ≫ F.parameter =
    pullback.snd P.structureMap sT ≫ t := by
  simp only [sourceMap, Category.assoc, starSource, pullback.condition]
  change toProduct sT t ht hstar ≫ inverse F ≫ starBase F ≫ puncturedParameter.ι = _
  rw [inverse_base_assoc, toProduct_base_assoc, base_spec]

@[reassoc] theorem sourceMap_left : sourceMap F sT t ht hstar ≫ F.left =
    pullback.fst P.structureMap sT := by
  simp only [sourceMap, Category.assoc, inverse_left, toProduct_left]

def forward : RationalSourceOver P T sT ⟶ SourceOver F t :=
  pullback.lift (sourceMap F sT t ht hstar) (pullback.snd P.structureMap sT)
    (sourceMap_parameter F sT t ht hstar)

def backward : SourceOver F t ⟶ RationalSourceOver P T sT :=
  pullback.lift (pullback.fst F.parameter t ≫ F.left) (pullback.snd F.parameter t) (by
    rw [Category.assoc, F.left_over, ← Category.assoc, pullback.condition,
      Category.assoc, ht])

include hstar in
theorem source_parameter_isUnit :
    IsUnit ((pullback.fst F.parameter t ≫ F.parameter).appTop parameterFunction) := by
  have h : IsUnit (((pullback.snd F.parameter t ≫ base t hstar) ≫
      puncturedParameter.ι).appTop parameterFunction) := by
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
      parameter_isUnit.map (pullback.snd F.parameter t ≫ base t hstar).appTop.hom
  have hm : (pullback.snd F.parameter t ≫ base t hstar) ≫ puncturedParameter.ι =
      pullback.fst F.parameter t ≫ F.parameter := by
    rw [Category.assoc, base_spec]
    exact pullback.condition.symm
  exact (congrArg (fun k : SourceOver F t ⟶ AffineLine =>
    IsUnit (k.appTop parameterFunction)) hm).mp h

theorem forward_backward : forward F sT t ht hstar ≫ backward F sT t ht = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [forward, backward, Category.assoc, pullback.lift_fst,
      pullback.lift_fst_assoc, Category.id_comp]
    exact sourceMap_left F sT t ht hstar
  · simp [forward, backward, Category.assoc]

theorem backward_forward : backward F sT t ht ≫ forward F sT t ht hstar = 𝟙 _ := by
  apply pullback.hom_ext
  · apply parameter_left_ext F
    · simp only [forward, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        sourceMap_parameter, backward, pullback.lift_snd_assoc, Category.id_comp]
      exact pullback.condition.symm
    · simp [forward, backward, Category.assoc, sourceMap_left]
    · simpa only [forward, backward, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc, sourceMap_parameter, pullback.lift_snd_assoc,
        pullback.condition] using source_parameter_isUnit F t hstar
  · simp [forward, backward, Category.assoc]

def iso : RationalSourceOver P T sT ≅ SourceOver F t where
  hom := forward F sT t ht hstar
  inv := backward F sT t ht
  hom_inv_id := forward_backward F sT t ht hstar
  inv_hom_id := backward_forward F sT t ht hstar

@[reassoc] theorem iso_source : (iso F sT t ht hstar).hom ≫ pullback.fst F.parameter t =
    sourceMap F sT t ht hstar := pullback.lift_fst _ _ _

@[reassoc] theorem iso_base : (iso F sT t ht hstar).hom ≫ pullback.snd F.parameter t =
    pullback.snd P.structureMap sT := pullback.lift_snd _ _ _

theorem marked_source (q : ProjectiveLinePoint P)
    (a : AffineLine ⟶ F.source) (ha : a ≫ F.parameter = 𝟙 AffineLine)
    (hleft : a ≫ F.left = affineLineToC ≫ q.map) :
    pullback.lift (sT ≫ q.map) (𝟙 T) (by simp [Category.assoc, q.overC]) ≫
      sourceMap F sT t ht hstar = t ≫ a := by
  apply parameter_left_ext F
  · simp [Category.assoc, sourceMap_parameter, ha]
  · simp only [Category.assoc, sourceMap_left, pullback.lift_fst, hleft]
    exact (congrArg (fun k : T ⟶ ComplexBase => k ≫ q.map) ht).symm.trans
      (Category.assoc t affineLineToC q.map)
  · have h : IsUnit ((base t hstar ≫ puncturedParameter.ι).appTop parameterFunction) := by
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
        parameter_isUnit.map (base t hstar).appTop.hom
    have hu : IsUnit (t.appTop parameterFunction) :=
      (congrArg (fun k : T ⟶ AffineLine => IsUnit (k.appTop parameterFunction))
        (base_spec t hstar)).mp h
    simpa only [Category.assoc, sourceMap_parameter, pullback.lift_snd_assoc,
      Category.id_comp] using hu

end PuncturedModel

def pointProductIso (Q : ProjectiveLineOverC) :
    ProjectiveLine ≅ RationalSourceOver Q ComplexBase (𝟙 ComplexBase) where
  hom := pullback.lift (𝟙 ProjectiveLine) Q.structureMap (by simp)
  inv := pullback.fst Q.structureMap (𝟙 ComplexBase)
  hom_inv_id := by simp
  inv_hom_id := by
    apply pullback.hom_ext <;> simp [Category.assoc, pullback.condition]

theorem constant_curve_degree_zero (Q : ProjectiveLineOverC)
    (p : ProjectiveLinePoint Q) {d : ℕ} (M : SmoothProperComplexVariety d)
    (f : ParametrizedCurve Q M) (L : LineBundle M.scheme)
    (hc : IsConstantOverC Q M f.map) : degreeOnCurve Q p f L = 0 := by
  obtain ⟨x, hx, hf⟩ := hc
  obtain ⟨F⟩ := Jets.pointFrame_exists M L ⟨x, hx⟩
  let e₀ : structureModule ComplexBase ≅ pullbackModule x L.sheaf :=
    FrameEvaluation.fiberFrame F.frame.openSet F.pointLift x F.overPoint
      (Jets.PointFrame.LocalFrameJetProof.frameIso F.frame)
  let e : (pullbackLine f.map L).sheaf ≅ (trivialLine ProjectiveLine).sheaf :=
    (compositionPullback Q.structureMap x f.map hf.symm L.sheaf).symm ≪≫
      (Scheme.Modules.pullback Q.structureMap).mapIso e₀.symm ≪≫
      unitPullbackIso Q.structureMap
  change projectiveLineDegree Q p (pullbackLine f.map L) = 0
  rw [projectiveLineDegree_iso Q p _ _ e]
  simpa only [projectiveTwist, linePowerInt, linePower] using projectiveTwist_degree Q p 0

namespace Neighborhood

variable {G : Germ D} (N : Neighborhood G) (A : Charts.PointedAffine)
variable (i : A.scheme ⟶ N.chart.scheme) (hi : i ≫ N.chart.toC = A.toC)
variable (hstar : Set.range (i ≫ N.toBase) ⊆ (puncturedParameter : Set AffineLine))

include hi in
theorem punctured_over : (i ≫ N.toBase) ≫ affineLineToC = A.toC := by
  rw [Category.assoc, N.overC, hi]

def productSourceIso : RationalSourceOver P A.scheme A.toC ≅
    SourceOver G.source (i ≫ N.toBase) :=
  PuncturedModel.iso G.source A.toC (i ≫ N.toBase)
    (N.punctured_over A i hi) hstar

def productToFamily : RationalSourceOver P A.scheme A.toC ⟶ N.familySource :=
  (N.productSourceIso A i hi hstar).hom ≫
    sourceBaseChangeMap G.source (i ≫ N.toBase) N.toBase i rfl

@[reassoc] theorem productToFamily_source :
    N.productToFamily A i hi hstar ≫ pullback.fst G.source.parameter N.toBase =
      PuncturedModel.sourceMap G.source A.toC (i ≫ N.toBase)
        (N.punctured_over A i hi) hstar := by
  simp only [productToFamily, Category.assoc, sourceBaseChangeMap, pullback.lift_fst]
  exact PuncturedModel.iso_source _ _ _ _ _

@[reassoc] theorem productToFamily_base :
    N.productToFamily A i hi hstar ≫ N.familyParameter =
      pullback.snd P.structureMap A.toC ≫ i := by
  simp only [productToFamily, familyParameter, Category.assoc, sourceBaseChangeMap,
    pullback.lift_snd]
  rw [productSourceIso, PuncturedModel.iso_base_assoc]

def productEvaluation : RationalSourceOver P A.scheme A.toC ⟶ X.variety.scheme :=
  N.productToFamily A i hi hstar ≫ N.familyEvaluation

theorem productEvaluation_over : N.productEvaluation A i hi hstar ≫ X.variety.structureMap =
    pullback.fst P.structureMap A.toC ≫ P.structureMap := by
  rw [productEvaluation, Category.assoc, N.familyEvaluation_over,
    N.productToFamily_base_assoc, hi]
  exact pullback.condition.symm

theorem productEvaluation_marked (q : ProjectiveLinePoint P)
    (a : AffineLine ⟶ G.source.source) (ha : a ≫ G.source.parameter = 𝟙 AffineLine)
    (hleft : a ≫ G.source.left = affineLineToC ≫ q.map) :
    ProductFamily.evaluation P A X.variety (N.productEvaluation A i hi hstar) q =
      i ≫ N.toHom ≫ markedEvaluation G.hom a ha := by
  dsimp only [ProductFamily.evaluation, productEvaluation, familyEvaluation, markedEvaluation]
  simp only [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, sourceBaseChangeMap, pullback.lift_fst,
      pullback.lift_fst_assoc]
    rw [N.productToFamily_source]
    exact PuncturedModel.marked_source G.source A.toC (i ≫ N.toBase)
      (N.punctured_over A i hi) hstar q a ha hleft
  · simp only [Category.assoc, sourceBaseChangeMap, pullback.lift_snd,
      pullback.lift_snd_assoc, Category.comp_id]
    change ProductFamily.markedInclusion P A q ≫
      N.productToFamily A i hi hstar ≫ N.familyParameter ≫ N.toHom = i ≫ N.toHom
    rw [N.productToFamily_base_assoc]
    simp [ProductFamily.markedInclusion, Category.assoc]

theorem productEvaluation_first :
    ProductFamily.evaluation P A X.variety (N.productEvaluation A i hi hstar) infinity =
      i ≫ N.firstEval.map ≫ G.firstOpen := by
  rw [N.productEvaluation_marked A i hi hstar infinity G.marks.first
    G.marks.first_base G.marks.first_left, N.firstEval_spec]

theorem productEvaluation_second :
    ProductFamily.evaluation P A X.variety (N.productEvaluation A i hi hstar) marking =
      i ≫ N.secondEval.map ≫ G.secondOpen := by
  rw [N.productEvaluation_marked A i hi hstar marking G.marks.second
    G.marks.second_base G.marks.second_left, N.secondEval_spec]

def productPoint : PointsOver ComplexBase (𝟙 ComplexBase) N.chart.scheme N.chart.toC :=
  ⟨A.point.val ≫ i, by rw [Category.assoc, hi, A.point.property]⟩

include hstar in
theorem productPoint_punctured :
    Set.range ((N.productPoint A i hi).val ≫ N.toBase) ⊆
      (puncturedParameter : Set AffineLine) := by
  rintro _ ⟨z, rfl⟩
  exact hstar ⟨A.point.val z, rfl⟩

theorem productPoint_parameter_over :
    ((N.productPoint A i hi).val ≫ N.toBase) ≫ affineLineToC = 𝟙 ComplexBase := by
  rw [Category.assoc, N.overC, (N.productPoint A i hi).property]

def productFibreIso : ProjectiveLine ≅
    pullback N.familyParameter (N.productPoint A i hi).val :=
  pointProductIso P ≪≫
    PuncturedModel.iso G.source (𝟙 ComplexBase)
      ((N.productPoint A i hi).val ≫ N.toBase)
      (N.productPoint_parameter_over A i hi) (N.productPoint_punctured A i hi hstar) ≪≫
    baseChangedFibreIso G.source N.toBase (N.productPoint A i hi).val
      ((N.productPoint A i hi).val ≫ N.toBase) rfl

theorem productFibreIso_base :
    (N.productFibreIso A i hi hstar).hom ≫
      pullback.snd N.familyParameter (N.productPoint A i hi).val = P.structureMap := by
  let b := N.productPoint A i hi
  let c := b.val ≫ N.toBase
  let e := PuncturedModel.iso G.source (𝟙 ComplexBase) c
    (N.productPoint_parameter_over A i hi) (N.productPoint_punctured A i hi hstar)
  let j := baseChangedFibreIso G.source N.toBase b.val c rfl
  have hj : j.hom ≫ pullback.snd N.familyParameter b.val =
      pullback.snd G.source.parameter c :=
    baseChangedFibreIso_base G.source N.toBase b.val c rfl
  have he : e.hom ≫ pullback.snd G.source.parameter c =
      pullback.snd P.structureMap (𝟙 ComplexBase) :=
    PuncturedModel.iso_base G.source (𝟙 ComplexBase) c
      (N.productPoint_parameter_over A i hi) (N.productPoint_punctured A i hi hstar)
  change ((pointProductIso P).hom ≫ e.hom ≫ j.hom) ≫
    pullback.snd N.familyParameter b.val = P.structureMap
  simp only [Category.assoc, hj, he, pointProductIso, pullback.lift_snd]

theorem productFibreIso_source :
    (N.productFibreIso A i hi hstar).hom ≫
      pullback.fst N.familyParameter (N.productPoint A i hi).val =
    ProductFamily.centralInclusion P A ≫ N.productToFamily A i hi hstar := by
  let b := N.productPoint A i hi
  let c := b.val ≫ N.toBase
  let e := PuncturedModel.iso G.source (𝟙 ComplexBase) c
    (N.productPoint_parameter_over A i hi) (N.productPoint_punctured A i hi hstar)
  let j := baseChangedFibreIso G.source N.toBase b.val c rfl
  let f : ProjectiveLine ⟶ N.familySource :=
    (N.productFibreIso A i hi hstar).hom ≫ pullback.fst N.familyParameter b.val
  let g : ProjectiveLine ⟶ N.familySource :=
    ProductFamily.centralInclusion P A ≫ N.productToFamily A i hi hstar
  have hfbase : f ≫ N.familyParameter = P.structureMap ≫ b.val := by
    dsimp only [f]
    rw [Category.assoc, pullback.condition, ← Category.assoc, N.productFibreIso_base]
  have hgbase : g ≫ N.familyParameter = P.structureMap ≫ b.val := by
    dsimp only [g]
    rw [Category.assoc, N.productToFamily_base]
    simp only [ProductFamily.centralInclusion, pullback.lift_snd_assoc,
      b, productPoint, Category.assoc]
  have hbase : f ≫ N.familyParameter = g ≫ N.familyParameter :=
    hfbase.trans hgbase.symm
  have hj : j.hom ≫ pullback.fst N.familyParameter b.val =
      sourceBaseChangeMap G.source c N.toBase b.val rfl :=
    baseChangedFibreIso_first G.source N.toBase b.val c rfl
  have hjfst : j.hom ≫ pullback.fst N.familyParameter b.val ≫
      pullback.fst G.source.parameter N.toBase = pullback.fst G.source.parameter c := by
    rw [← Category.assoc, hj]
    exact pullback.lift_fst _ _ _
  have he : e.hom ≫ pullback.fst G.source.parameter c =
      PuncturedModel.sourceMap G.source (𝟙 ComplexBase) c
        (N.productPoint_parameter_over A i hi) (N.productPoint_punctured A i hi hstar) :=
    PuncturedModel.iso_source G.source (𝟙 ComplexBase) c
      (N.productPoint_parameter_over A i hi) (N.productPoint_punctured A i hi hstar)
  have hfsource : f ≫ pullback.fst G.source.parameter N.toBase =
      (pointProductIso P).hom ≫ PuncturedModel.sourceMap G.source (𝟙 ComplexBase) c
        (N.productPoint_parameter_over A i hi) (N.productPoint_punctured A i hi hstar) := by
    change (((pointProductIso P).hom ≫ e.hom ≫ j.hom) ≫
      pullback.fst N.familyParameter b.val) ≫ pullback.fst G.source.parameter N.toBase = _
    simp only [Category.assoc, hjfst, he]
  have hgsource : g ≫ pullback.fst G.source.parameter N.toBase =
      ProductFamily.centralInclusion P A ≫
        PuncturedModel.sourceMap G.source A.toC (i ≫ N.toBase)
          (N.punctured_over A i hi) hstar := by
    dsimp only [g]
    rw [Category.assoc, N.productToFamily_source]
  have hc : pullback.fst G.source.parameter N.toBase ≫ G.source.parameter =
      N.familyParameter ≫ N.toBase := pullback.condition
  have hfparameter : (f ≫ pullback.fst G.source.parameter N.toBase) ≫
      G.source.parameter = P.structureMap ≫ c := by
    calc
      (f ≫ pullback.fst G.source.parameter N.toBase) ≫ G.source.parameter =
          (f ≫ N.familyParameter) ≫ N.toBase := by simp only [Category.assoc, hc]
      _ = (P.structureMap ≫ b.val) ≫ N.toBase :=
        congrArg (fun k : ProjectiveLine ⟶ N.chart.scheme => k ≫ N.toBase) hfbase
      _ = P.structureMap ≫ c := Category.assoc _ _ _
  change f = g
  apply pullback.hom_ext
  · apply PuncturedSourceProof.parameter_left_ext G.source
    · simpa only [Category.assoc, hc] using
        congrArg (fun k : ProjectiveLine ⟶ N.chart.scheme => k ≫ N.toBase) hbase
    · rw [hfsource, hgsource]
      simp only [Category.assoc, PuncturedModel.sourceMap_left,
        pointProductIso, ProductFamily.centralInclusion, pullback.lift_fst]
    · have hu : IsUnit (((P.structureMap ≫ PuncturedModel.base c
          (N.productPoint_punctured A i hi hstar)) ≫ puncturedParameter.ι).appTop
          parameterFunction) := by
        simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
          PuncturedSourceProof.parameter_isUnit.map
            (P.structureMap ≫ PuncturedModel.base c
              (N.productPoint_punctured A i hi hstar)).appTop.hom
      have hm : (P.structureMap ≫ PuncturedModel.base c
          (N.productPoint_punctured A i hi hstar)) ≫ puncturedParameter.ι =
          (f ≫ pullback.fst G.source.parameter N.toBase) ≫ G.source.parameter := by
        rw [Category.assoc, PuncturedModel.base_spec]
        exact hfparameter.symm
      exact (congrArg (fun k : ProjectiveLine ⟶ AffineLine =>
        IsUnit (k.appTop parameterFunction)) hm).mp hu
  · change f ≫ N.familyParameter = g ≫ N.familyParameter
    exact hbase

theorem productFibreIso_curve :
    (N.productFibreIso A i hi hstar).hom ≫
      pullback.fst N.familyParameter (N.productPoint A i hi).val ≫ N.familyEvaluation =
    ProductFamily.curveMap P A X.variety (N.productEvaluation A i hi hstar) := by
  rw [← Category.assoc, N.productFibreIso_source]
  rfl

end Neighborhood

end LeBrunSalamon.Construction.Smoothing.ConicExtraction

namespace LeBrunSalamon.Construction.Smoothing

open Lines ConicExtraction

/-- This final geometric step uses openness of smoothness, nonempty s!=0
locus, the literal punctured-source trivialization, and the P1 splitting
criterion. It must not be proved by numerical dimension counting alone. -/
theorem germ_extracts_veryFreeConic {n : ℕ} {X : ContactFanoManifold n}
    {D : SuitablePair X} (G : Germ D)
    (hb : Function.Surjective G.baseDifferential)
    (he : Function.Surjective G.endpointDifferential) :
    Nonempty (VeryFreeContactConic P marking X) := by
  obtain ⟨N⟩ := neighborhood_exists G he
  obtain ⟨U, hU, hdegree⟩ := N.degree_neighborhood
  obtain ⟨b, hbU, hbStar⟩ := N.point_in_puncture U hU
  have hbOpen : b.val (default : PrimeSpectrum ℂ) ∈ N.toBase ⁻¹ᵁ puncturedParameter := by
    change N.toBase (b.val (default : PrimeSpectrum ℂ)) ∈
      (puncturedParameter : Set AffineLine)
    have h := hbStar (Set.mem_range_self (default : PrimeSpectrum ℂ))
    simpa only [Scheme.Hom.comp_apply] using h
  obtain ⟨V, hV, hbV, hVStar⟩ := exists_isAffineOpen_mem_and_subset
    (X := N.chart.scheme) (x := b.val (default : PrimeSpectrum ℂ))
    (U := N.toBase ⁻¹ᵁ puncturedParameter) hbOpen
  have hbVr := GermProof.point_range_in_open b.val V hbV
  let A := GermProof.chartOfOpen N.chart.toC b V hV hbVr
  have hApoint : A.point.val ≫ V.ι = b.val :=
    GermProof.chartOfOpen_point N.chart.toC b V hV hbVr
  have hstar : Set.range (V.ι ≫ N.toBase) ⊆ (puncturedParameter : Set AffineLine) := by
    rintro _ ⟨z, rfl⟩
    exact hVStar z.property
  let B : Charts.PointedAffine :=
    { scheme := G.firstTarget.scheme
      affine := G.firstTarget.affine
      toC := G.firstTarget.toC
      point := ⟨b.val ≫ N.firstEval.map, by
        rw [Category.assoc, N.firstEval.overC, b.property]⟩ }
  let C : Charts.PointedAffine :=
    { scheme := G.secondTarget.scheme
      affine := G.secondTarget.affine
      toC := G.secondTarget.toC
      point := ⟨b.val ≫ N.secondEval.map, by
        rw [Category.assoc, N.secondEval.overC, b.property]⟩ }
  let e : Charts.Hom A B :=
    { map := V.ι ≫ N.firstEval.map
      overC := by rw [Category.assoc, N.firstEval.overC]; rfl
      atCentre := by rw [← Category.assoc, hApoint] }
  let f : Charts.Hom A C :=
    { map := V.ι ≫ N.secondEval.map
      overC := by rw [Category.assoc, N.secondEval.overC]; rfl
      atCentre := by rw [← Category.assoc, hApoint] }
  have hpair : Smooth (AffineProduct.pair e f).map := by
    have hmap : (AffineProduct.pair e f).map =
        V.ι ≫ (AffineProduct.pair N.firstEval N.secondEval).map := by
      apply pullback.hom_ext <;> simp [AffineProduct.pair, e, f, B, C, Category.assoc]
    letI : Smooth (AffineProduct.pair N.firstEval N.secondEval).map := N.endpointSmooth
    rw [hmap]
    infer_instance
  let F := N.productEvaluation A V.ι rfl hstar
  have hF : F ≫ X.variety.structureMap =
      pullback.fst P.structureMap A.toC ≫ P.structureMap :=
    N.productEvaluation_over A V.ι rfl hstar
  letI : IsOpenImmersion G.firstOpen := G.firstOpen_immersion
  letI : IsOpenImmersion G.secondOpen := G.secondOpen_immersion
  have hp : ProductFamily.evaluation P A X.variety F infinity = e.map ≫ G.firstOpen := by
    simpa only [e, Category.assoc] using N.productEvaluation_first A V.ι rfl hstar
  have hq : ProductFamily.evaluation P A X.variety F marking = f.map ≫ G.secondOpen := by
    simpa only [f, Category.assoc] using N.productEvaluation_second A V.ι rfl hstar
  have hvalues := ProductFamily.twoPointEvaluation_surjective P A X.variety F hF
    infinity marking B C G.firstOpen G.secondOpen G.firstOpen_over G.secondOpen_over
    e f hp hq (AffineProduct.surjective_pair_of_smooth e f hpair)
  have hpositive : IsTwoPointGloballyGenerated P
      (pullbackModule (ProductFamily.curveMap P A X.variety F)
        (tangentSheaf X.variety.structureMap)) :=
    twoPointGeneration_of_onePair P infinity marking zero_ne_infinity.symm
      (pullbackBundle (ProductFamily.curveMap P A X.variety F)
        (intrinsicTangentBundle X.variety)) hvalues
  have hpoint : (N.productPoint A V.ι rfl).val = b.val := hApoint
  have hpointU : Set.range (N.productPoint A V.ι rfl).val ⊆ (U : Set N.chart.scheme) := by
    rw [hpoint]
    exact hbU
  have hdeg := hdegree (N.productPoint A V.ι rfl) hpointU
    (N.productFibreIso A V.ι rfl hstar) (N.productFibreIso_base A V.ι rfl hstar)
  rw [N.productFibreIso_curve] at hdeg
  let g₀ : ParametrizedCurve P X.variety :=
    ⟨ProductFamily.curveMap P A X.variety F, ProductFamily.curveMap_over P A X.variety F hF⟩
  have hgdegree : degreeOnCurve P marking g₀ X.contact.sequence.line = 2 := hdeg
  have hnonconstant : ¬ IsConstantOverC P X.variety g₀.map := by
    intro hc
    have hz := constant_curve_degree_zero P marking X.variety g₀ X.contact.sequence.line hc
    rw [hgdegree] at hz
    norm_num at hz
  let g : RationalCurve P X.variety := ⟨g₀.map, g₀.overC, hnonconstant⟩
  exact ⟨⟨g, hgdegree, hpositive⟩⟩

end LeBrunSalamon.Construction.Smoothing

end

#print axioms LeBrunSalamon.Construction.Smoothing.germ_extracts_veryFreeConic
