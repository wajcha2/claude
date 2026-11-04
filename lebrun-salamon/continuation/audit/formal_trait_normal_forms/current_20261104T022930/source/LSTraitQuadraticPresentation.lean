import LSStableMapFamily
import LSLineCohomologyBaseChange
import LSPlaneFamilyQuadratic
import LSSmoothFibreCartier
import LSTraitFibreCohomology

/-! Construct the actual primitive quadratic of a proper flat family on
the original complex power-series trait. The smooth closed-fibre case
uses the given rational-fibre isomorphism and the original degree-two
line. H1, section lifting, embedding, Cartierness, Picard comparison and
the actual equation isomorphism are all supplied by proved translations. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.StableMaps.FormalArcs

theorem smooth_quadratic_equation
    {X : Scheme.{0}} (pi : X ⟶ Trait) [IsProper pi] [Flat pi]
    (L : LineBundle X) (i : ProjectiveLine ≅ pullback pi closedPoint)
    (hi : i.hom ≫ pullback.snd pi closedPoint = Lines.P.structureMap)
    (hdegree : projectiveLineDegree Lines.P Lines.marking
      (pullbackLine (i.hom ≫ pullback.fst pi closedPoint) L) = 2) :
    ∃ q : PlaneQuadratic.Coefficients (PowerSeries ℂ),
      PlaneQuadratic.Primitive (PowerSeries ℂ) q ∧
      ∃ e : X ≅ PlaneQuadratic.ZeroScheme (PowerSeries ℂ) q,
        e.hom ≫ PlaneQuadratic.projection (PowerSeries ℂ) q = pi ∧
        Nonempty (L.sheaf ≅ pullbackModule e.hom
          (pullbackLine (PlaneQuadratic.inclusion (PowerSeries ℂ) q)
            (StandardTautological.line (PowerSeries ℂ) 2)).sheaf) := by
  letI : IsLocalHom (PowerSeries.constantCoeff (R := ℂ)) :=
    ResidueFieldPresentation.constantCoeff_local ℂ
  letI : ConnectedSpace (Spec (CommRingCat.of (PowerSeries ℂ))) := by
    change ConnectedSpace (PrimeSpectrum (PowerSeries ℂ))
    infer_instance
  have hret : (PowerSeries.constantCoeff (R := ℂ)).comp PowerSeries.C = RingHom.id ℂ := by
    ext c
    exact PowerSeries.constantCoeff_C c
  have ht : (StandardProjectiveBaseChange.base (PowerSeries.constantCoeff (R := ℂ))).base
      (IsLocalRing.closedPoint ℂ) = IsLocalRing.closedPoint (PowerSeries ℂ) :=
    Spec_closedPoint
  have h1 := TraitFibreCohomology.smooth Lines.P Lines.marking pi closedPoint L i hdegree
  have hsections := CohomologyBaseChange.powerSeries_fibre_restriction_surjective pi L h1
  obtain ⟨j, h0, ⟨d0⟩⟩ := SmoothFibreComparison.fibre_cartier_plane_embedding
    pi closedPoint L i hi Lines.marking hdegree
  exact PlaneFamilyQuadratic.of_closed_embedding (PowerSeries ℂ)
    PowerSeries.C PowerSeries.constantCoeff PowerSeries.constantCoeff_surj hret
    (IsLocalRing.closedPoint ℂ) ht pi L hsections j h0 d0

end LeBrunSalamon.Construction.StableMaps.FormalArcs
end
