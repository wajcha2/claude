import LSHomPointLiftDeformationProbe

/-! Actual marked evaluation of the universal first-order Hom family.
This isolated comparison uses the unchanged, checked point-lift probe.
No dominance conclusion or additional published input is assumed. -/

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.Construction.Lines
open LeBrunSalamon.Next3i.HomPointDeformations

namespace LeBrunSalamon.Next3i.HomMarkedEvaluation

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

end LeBrunSalamon.Next3i.HomMarkedEvaluation

end
