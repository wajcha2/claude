import LSStandardProjectivePicard
import LSPlaneEmbeddingCartier
import LSCartierQuadraticExtraction
import LSQuadraticPrimitive

/-! Assemble the actual primitive quadratic from a polarized closed-fibre
plane embedding and surjectivity of the actual restriction on sections.
The Picard comparison, canonical divisor section, coefficient extraction,
primitivity, base map and polarization are all retained in the proof. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.PlaneFamilyQuadratic

theorem of_closed_embedding
    (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsDomain R] [UniqueFactorizationMonoid R]
    [ConnectedSpace (Spec (CommRingCat.of R))]
    (φ : ℂ →+* R) (ψ : R →+* ℂ) [IsLocalHom ψ]
    (hψ : Function.Surjective ψ) (hret : ψ.comp φ = RingHom.id ℂ)
    (t : Spec (CommRingCat.of ℂ))
    (ht : (StandardProjectiveBaseChange.base ψ).base t = IsLocalRing.closedPoint R)
    {X : Scheme.{0}} (pi : X ⟶ Spec (CommRingCat.of R)) [IsProper pi] [Flat pi]
    (L : LineBundle X)
    (hsections : Function.Surjective (fun a : AlgebraicSection L.sheaf =>
      pullSection (pullback.fst pi (StandardProjectiveBaseChange.base ψ)) a))
    (j : PolarizedProjectiveEmbedding ℂ 2
      (pullback pi (StandardProjectiveBaseChange.base ψ))
      (pullback.snd pi (StandardProjectiveBaseChange.base ψ))
      (pullbackLine (pullback.fst pi (StandardProjectiveBaseChange.base ψ)) L))
    (h0 : IsLocallyFreeOfRank (EffectiveCartier.ideal j.hom) 1)
    (d0 : (EffectiveCartier.line j.hom h0).sheaf ≅ (PlaneQuadratic.quadraticLine ℂ).sheaf) :
    ∃ q : PlaneQuadratic.Coefficients R, PlaneQuadratic.Primitive R q ∧
      ∃ e : X ≅ PlaneQuadratic.ZeroScheme R q,
        e.hom ≫ PlaneQuadratic.projection R q = pi ∧
        Nonempty (L.sheaf ≅ pullbackModule e.hom
          (pullbackLine (PlaneQuadratic.inclusion R q) (StandardTautological.line R 2)).sheaf) := by
  obtain ⟨f, hcompare⟩ := PolarizedEmbeddingLift.with_closed_fibre_comparison
    R ℂ ψ t ht pi 2 L hsections j
  letI : IsClosedImmersion f.hom := f.closed
  letI : IsClosedImmersion j.hom := j.closed
  have h := PlaneEmbeddingCartier.of_closed_fibre R ℂ ψ hψ pi L f j hcompare h0
  have hsq := PolarizedEmbeddingLift.cartesian_of_comparison R ℂ ψ pi 2 L f j hcompare
  obtain ⟨c, _⟩ := PublishedInputs.EffectiveCartier.baseChange_line
    f.hom (pullback.fst pi (StandardProjectiveBaseChange.base ψ)) j.hom
    (StandardProjectiveBaseChange.map ψ 2) hsq h h0
  let fibreLine := c ≪≫ d0 ≪≫ (PlaneQuadraticBaseChange.squareLineIso ψ 2).symm
  obtain ⟨d⟩ := StandardProjectivePicard.iso_of_fibre_iso φ ψ hret 2 (by omega)
    (EffectiveCartier.line f.hom h) (PlaneQuadratic.quadraticLine R) fibreLine
  obtain ⟨q, hq, e, he⟩ := CartierQuadraticExtraction.exists_equation R f.hom h d
  have hprimitive : PlaneQuadratic.Primitive R q :=
    QuadraticPrimitive.of_fibre_cartier ψ f.hom
      (pullback.fst pi (StandardProjectiveBaseChange.base ψ)) j.hom hsq h h0 d q hq
  refine ⟨q, hprimitive, e, ?_, ?_⟩
  · change e.hom ≫ (PlaneQuadratic.inclusion R q ≫ StandardTautological.toSpec R 2) = pi
    rw [← Category.assoc, he, f.over_base]
  · exact ⟨f.lineIso.symm ≪≫ ((Scheme.Modules.pullbackCongr he).app
      (StandardTautological.line R 2).sheaf).symm ≪≫
      ((Scheme.Modules.pullbackComp e.hom (PlaneQuadratic.inclusion R q)).app
        (StandardTautological.line R 2).sheaf).symm⟩

end LeBrunSalamon.PlaneFamilyQuadratic
end
