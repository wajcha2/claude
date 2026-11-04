import LSTwoMarkedHomLiftSurjectivityProbe

/-! Pass from the two marked endpoint lifts to the actual target product,
then factor the parameter lift into the specified open. No new admission. -/

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
open LeBrunSalamon.Next3i.HomPointDeformations
open LeBrunSalamon.Next3i.HomMarkedEvaluation
open LeBrunSalamon.Next3i.TwoMarkedHomLifts

namespace LeBrunSalamon.Next3i.TwoPointProductLifts

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

end LeBrunSalamon.Next3i.TwoPointProductLifts

#print axioms LeBrunSalamon.Next3i.TwoPointProductLifts.product_evaluation_lifts
#print axioms LeBrunSalamon.Next3i.TwoPointProductLifts.lift_in_open_with_composite

end
