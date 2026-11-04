import LSStandardProjectiveNonempty
import LSEffectiveCartierInputs
import LSPlaneQuadraticBaseChange

/-! A lifted Cartier equation is primitive because its residue section
is the actual regular Cartier section, up to the specified line
isomorphism.  All coordinate, pullback and unit comparisons are proofs. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Refinement

namespace LeBrunSalamon.QuadraticPrimitive

theorem sectionOf_zero (A : Type) [CommRing A] :
    PlaneQuadratic.sectionOf A 0 = 0 := by
  simp only [PlaneQuadratic.sectionOf, Pi.zero_apply, PlaneQuadratic.coefficient,
    map_zero, zero_smul, sectionFromValue_zero, Finset.sum_const_zero]

theorem of_reduction_ne_zero
    {R K : Type} [CommRing R] [Field K] (φ : R →+* K) [IsLocalHom φ]
    (q : PlaneQuadratic.Coefficients R) (h : (fun i => φ (q i)) ≠ 0) :
    PlaneQuadratic.Primitive R q := by
  obtain ⟨i, hi⟩ : ∃ i, φ (q i) ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact h (funext hn)
  exact ⟨i, isUnit_of_map_unit φ (q i) (isUnit_iff_ne_zero.mpr hi)⟩

theorem of_reduction_section_mono
    {R K : Type} [CommRing R] [Field K] (φ : R →+* K) [IsLocalHom φ]
    (q : PlaneQuadratic.Coefficients R)
    (hm : Mono (PlaneQuadratic.sectionOf K (fun i => φ (q i)))) :
    PlaneQuadratic.Primitive R q := by
  letI := hm
  obtain ⟨x⟩ := StandardProjectiveNonempty.nonempty K 2
  apply of_reduction_ne_zero φ q
  intro hzero
  have hn := StandardProjectiveNonempty.section_ne_zero_of_mono x
    (PlaneQuadratic.sectionOf K (fun i => φ (q i)))
  apply hn
  rw [hzero, sectionOf_zero]

theorem of_fibre_cartier
    {R K : Type} [CommRing R] [Field K] (φ : R →+* K) [IsLocalHom φ]
    {X X0 : Scheme.{0}} (i : X ⟶ PlaneQuadratic.Plane R) [IsClosedImmersion i]
    (a : X0 ⟶ X) (j : X0 ⟶ PlaneQuadratic.Plane K) [IsClosedImmersion j]
    (hb : IsPullback a j i (StandardProjectiveBaseChange.map φ 2))
    (h : IsLocallyFreeOfRank (EffectiveCartier.ideal i) 1)
    (h0 : IsLocallyFreeOfRank (EffectiveCartier.ideal j) 1)
    (d : (EffectiveCartier.line i h).sheaf ≅ (PlaneQuadratic.quadraticLine R).sheaf)
    (q : PlaneQuadratic.Coefficients R)
    (hq : PlaneQuadratic.sectionOf R q = EffectiveCartier.canonicalSection i h ≫ d.hom) :
    PlaneQuadratic.Primitive R q := by
  let b := StandardProjectiveBaseChange.map φ 2
  obtain ⟨c, hc⟩ := PublishedInputs.EffectiveCartier.baseChange_line i a j b hb h h0
  let e : (EffectiveCartier.line j h0).sheaf ≅ (PlaneQuadratic.quadraticLine K).sheaf :=
    c.symm ≪≫ (Scheme.Modules.pullback b).mapIso d ≪≫
      PlaneQuadraticBaseChange.squareLineIso φ 2
  have he : PlaneQuadratic.sectionOf K (fun k => φ (q k)) =
      EffectiveCartier.canonicalSection j h0 ≫ e.hom := by
    rw [← PlaneQuadraticBaseChange.sectionOf φ q, hq,
      ExternalExchangeCoherenceProof.pullSection_map, ← hc]
    simp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
      c.hom_inv_id_assoc]
    rfl
  have hm : Mono (EffectiveCartier.canonicalSection j h0) :=
    (PublishedInputs.EffectiveCartier.canonical_regular_and_zero_locus j h0).1
  letI := hm
  apply of_reduction_section_mono φ q
  rw [he]
  infer_instance

end LeBrunSalamon.QuadraticPrimitive
end
