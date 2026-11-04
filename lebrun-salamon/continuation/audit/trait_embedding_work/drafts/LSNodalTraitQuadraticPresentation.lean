import LSFormalTraitParameters
import LSLineCohomologyBaseChange
import LSPlaneFamilyQuadratic
import LSQuadraticFibreCartier
import LSStandardCentralPlane
import LSTraitFibreCohomology
import LSFormalQuadraticConditions

/-! The original two-component closed fibre supplies an actual polarized
plane embedding with image xy=0. Section lifting and Cartier extraction
then construct the primitive quadratic of the whole trait family.
Every comparison retains the original base map and selected line. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.Construction.Smoothing

namespace LeBrunSalamon.Construction.StableMaps.FormalArcs

theorem nodal_quadratic_equation
    (F : StandardSource) {X : Scheme.{0}} (pi : X ⟶ Trait) [IsProper pi] [Flat pi]
    (L : LineBundle X) (i j : ProjectiveLine ⟶ pullback pi closedPoint)
    (p q : ProjectiveLinePoint Lines.P)
    (hi : i ≫ pullback.snd pi closedPoint = Lines.P.structureMap)
    (hj : j ≫ pullback.snd pi closedPoint = Lines.P.structureMap)
    (hpush : IsPushout p.map q.map i j)
    (hdi : projectiveLineDegree Lines.P Lines.marking
      (pullbackLine (i ≫ pullback.fst pi closedPoint) L) = 1)
    (hdj : projectiveLineDegree Lines.P Lines.marking
      (pullbackLine (j ≫ pullback.fst pi closedPoint) L) = 1) :
    ¬ Smooth (pullback.snd pi closedPoint) ∧
      ∃ c : PlaneQuadratic.Coefficients Coefficients,
        PlaneQuadratic.Primitive Coefficients c ∧
        ∃ e : X ≅ PlaneQuadratic.ZeroScheme Coefficients c,
          e.hom ≫ PlaneQuadratic.projection Coefficients c = pi ∧
          Nonempty (L.sheaf ≅ pullbackModule e.hom
            (pullbackLine (PlaneQuadratic.inclusion Coefficients c)
              (StandardTautological.line Coefficients 2)).sheaf) := by
  let L0 := pullbackLine (pullback.fst pi closedPoint) L
  have hdi0 : projectiveLineDegree Lines.P Lines.marking (pullbackLine i L0) = 1 :=
    (projectiveLineDegree_iso Lines.P Lines.marking (pullbackLine i L0)
      (pullbackLine (i ≫ pullback.fst pi closedPoint) L)
      ((Scheme.Modules.pullbackComp i (pullback.fst pi closedPoint)).app L.sheaf)).trans hdi
  have hdj0 : projectiveLineDegree Lines.P Lines.marking (pullbackLine j L0) = 1 :=
    (projectiveLineDegree_iso Lines.P Lines.marking (pullbackLine j L0)
      (pullbackLine (j ≫ pullback.fst pi closedPoint) L)
      ((Scheme.Modules.pullbackComp j (pullback.fst pi closedPoint)).app L.sheaf)).trans hdj
  obtain ⟨marks⟩ := sourceMarks_exists F
  obtain ⟨e0, he0, ⟨eL0⟩⟩ := NodalFibreComparison.polarized_standard_fibre_iso F marks
    (projectiveCoordinates_hyperplane_degree_one Lines.P Lines.marking)
    (pullback.snd pi closedPoint) p q i j hpush hi hj L0 hdi0 hdj0
  let z := e0 ≪≫ StandardCentralPlane.iso F
  have hz : z.hom ≫ PlaneQuadratic.projection ℂ (PlaneQuadratic.split ℂ 0) =
      pullback.snd pi closedPoint := by
    change (e0.hom ≫ (StandardCentralPlane.iso F).hom) ≫ _ = _
    rw [Category.assoc, StandardCentralPlane.iso_over, he0]
  have hns : ¬ Smooth (pullback.snd pi closedPoint) :=
    FormalQuadraticConditions.notSmooth_of_split_zero_iso (pullback.snd pi closedPoint) z hz
  refine ⟨hns, ?_⟩
  let emb := (StandardCentralPlane.embedding F).transport e0 he0 eL0
  have hze : z.hom ≫ PlaneQuadratic.inclusion ℂ (PlaneQuadratic.split ℂ 0) =
      emb.hom := by
    change (e0.hom ≫ (StandardCentralPlane.iso F).hom) ≫ _ =
      e0.hom ≫ (StandardCentralPlane.embedding F).hom
    rw [Category.assoc, StandardCentralPlane.image_equation]
  obtain ⟨h0, ⟨d0⟩⟩ := QuadraticFibreCartier.of_quadratic_iso ℂ emb.hom
    (PlaneQuadratic.split ℂ 0) StandardCentralPlane.split_zero_nonzero z hze
  letI : IsLocalHom (PowerSeries.constantCoeff (R := ℂ)) :=
    ResidueFieldPresentation.constantCoeff_local ℂ
  letI : ConnectedSpace (Spec (CommRingCat.of Coefficients)) := by
    change ConnectedSpace (PrimeSpectrum Coefficients)
    infer_instance
  have hret : (PowerSeries.constantCoeff (R := ℂ)).comp PowerSeries.C = RingHom.id ℂ := by
    ext c
    exact PowerSeries.constantCoeff_C c
  have ht : (StandardProjectiveBaseChange.base (PowerSeries.constantCoeff (R := ℂ))).base
      (IsLocalRing.closedPoint ℂ) = IsLocalRing.closedPoint Coefficients := Spec_closedPoint
  have h1 := TraitFibreCohomology.nodal Lines.P Lines.marking p q pi closedPoint L
    i j hpush hdi hdj
  have hsections := CohomologyBaseChange.powerSeries_fibre_restriction_surjective pi L h1
  exact PlaneFamilyQuadratic.of_closed_embedding Coefficients
    PowerSeries.C PowerSeries.constantCoeff PowerSeries.constantCoeff_surj hret
    (IsLocalRing.closedPoint ℂ) ht pi L hsections emb h0 d0

end LeBrunSalamon.Construction.StableMaps.FormalArcs
end
