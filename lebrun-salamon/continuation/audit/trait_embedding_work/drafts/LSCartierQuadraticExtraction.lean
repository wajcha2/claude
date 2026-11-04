import LSEffectiveCartierInputs
import LSPlaneQuadraticPublished

/-! Extract the actual equation of a specified Cartier embedding whose
positive divisor line has been identified with standard O(2).  The
quadratic is obtained from the canonical inclusion section, and the
two scheme maps are inverse by their actual universal properties.
No family equation or family isomorphism is admitted. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Refinement

namespace LeBrunSalamon.CartierQuadraticExtraction

theorem exists_equation (A : Type) [CommRing A]
    {X : Scheme.{0}} (i : X ⟶ PlaneQuadratic.Plane A) [IsClosedImmersion i]
    (h : IsLocallyFreeOfRank (EffectiveCartier.ideal i) 1)
    (d : (EffectiveCartier.line i h).sheaf ≅ (PlaneQuadratic.quadraticLine A).sheaf) :
    ∃ q : PlaneQuadratic.Coefficients A,
      PlaneQuadratic.sectionOf A q = EffectiveCartier.canonicalSection i h ≫ d.hom ∧
      ∃ e : X ≅ PlaneQuadratic.ZeroScheme A q,
        e.hom ≫ PlaneQuadratic.inclusion A q = i := by
  obtain ⟨q, hq⟩ := (PublishedInputs.ProjectiveSpace.quadraticSections_bijective A).surjective
    (EffectiveCartier.canonicalSection i h ≫ d.hom)
  have hzero : pullSection i (PlaneQuadratic.sectionOf A q) = 0 := by
    rw [hq, ExternalExchangeCoherenceProof.pullSection_map,
      EffectiveCartier.canonical_zero, zero_comp]
  obtain ⟨f, hf, _⟩ := PlaneQuadratic.universal A q i hzero
  have hback : pullSection (PlaneQuadratic.inclusion A q)
      (EffectiveCartier.canonicalSection i h) = 0 := by
    apply (cancel_mono ((Scheme.Modules.pullback (PlaneQuadratic.inclusion A q)).map d.hom)).mp
    rw [zero_comp, ← ExternalExchangeCoherenceProof.pullSection_map, ← hq]
    exact PlaneQuadratic.zero_equation A q
  obtain ⟨g, hg, _⟩ := EffectiveCartier.universal i h (PlaneQuadratic.inclusion A q) hback
  have hfg : f ≫ g = 𝟙 X := by
    apply (cancel_mono i).mp
    rw [Category.assoc, hg, hf, Category.id_comp]
  have hgf : g ≫ f = 𝟙 (PlaneQuadratic.ZeroScheme A q) := by
    apply (cancel_mono (PlaneQuadratic.inclusion A q)).mp
    rw [Category.assoc, hf, hg, Category.id_comp]
  exact ⟨q, hq, ⟨f, g, hfg, hgf⟩, hf⟩

/-- The equation comparison preserves the specified projective
polarization and the specified base map, not just the abstract curve. -/
theorem polarized_equation (A : Type) [CommRing A]
    {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A))
    (L : LineBundle X) (i : X ⟶ PlaneQuadratic.Plane A) [IsClosedImmersion i]
    (hi : i ≫ StandardTautological.toSpec A 2 = p)
    (eL : pullbackModule i (StandardTautological.line A 2).sheaf ≅ L.sheaf)
    (h : IsLocallyFreeOfRank (EffectiveCartier.ideal i) 1)
    (d : (EffectiveCartier.line i h).sheaf ≅ (PlaneQuadratic.quadraticLine A).sheaf) :
    ∃ q : PlaneQuadratic.Coefficients A,
      ∃ e : X ≅ PlaneQuadratic.ZeroScheme A q,
        e.hom ≫ PlaneQuadratic.projection A q = p ∧
        Nonempty (L.sheaf ≅ pullbackModule e.hom
          (pullbackLine (PlaneQuadratic.inclusion A q) (StandardTautological.line A 2)).sheaf) := by
  obtain ⟨q, hq, e, he⟩ := exists_equation A i h d
  refine ⟨q, e, ?_, ?_⟩
  · change e.hom ≫ (PlaneQuadratic.inclusion A q ≫ StandardTautological.toSpec A 2) = p
    rw [← Category.assoc, he, hi]
  · exact ⟨eL.symm ≪≫ ((Scheme.Modules.pullbackCongr he).app
      (StandardTautological.line A 2).sheaf).symm ≪≫
      ((Scheme.Modules.pullbackComp e.hom (PlaneQuadratic.inclusion A q)).app
        (StandardTautological.line A 2).sheaf).symm⟩

end LeBrunSalamon.CartierQuadraticExtraction
end
