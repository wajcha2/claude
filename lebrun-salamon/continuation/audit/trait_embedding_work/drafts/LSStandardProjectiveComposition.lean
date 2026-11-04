import LSStandardProjectiveBaseChange

/-! The actual standard projective maps respect a ring retraction.
This is proved through their normalized coordinate tuples, not inferred
from a bare isomorphism class of projective spaces. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Refinement

namespace LeBrunSalamon.StandardProjectiveBaseChange

theorem base_retraction {R S : Type} [CommRing R] [CommRing S]
    (φ : R →+* S) (ψ : S →+* R) (h : ψ.comp φ = RingHom.id R) :
    base ψ ≫ base φ = 𝟙 (Spec (CommRingCat.of R)) := by
  change Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) = _
  rw [← Spec.map_comp]
  have hr : CommRingCat.ofHom φ ≫ CommRingCat.ofHom ψ = 𝟙 (CommRingCat.of R) := by
    apply CommRingCat.hom_ext
    exact h
  rw [hr, Spec.map_id]

theorem map_retraction {R S : Type} [CommRing R] [CommRing S]
    (φ : R →+* S) (ψ : S →+* R) (h : ψ.comp φ = RingHom.id R) (N : ℕ) :
    map ψ N ≫ map φ N = 𝟙 (StandardTautological.space R N) := by
  let D := StandardTautological.chosen R N
  let E := StandardTautological.chosen S N
  let f := map ψ N
  let g := map φ N
  let c : pullbackModule (f ≫ g) D.sheaf ≅ D.sheaf :=
    ((Scheme.Modules.pullbackComp f g).app D.sheaf).symm ≪≫
      (Scheme.Modules.pullback f).mapIso (lineIso φ N) ≪≫ lineIso ψ N
  have hc (i : Fin (N+1)) : pullSection (f ≫ g) (D.coordinate i) ≫ c.hom = D.coordinate i := by
    rw [composite_coordinate]
    have hg : pullSection g (D.coordinate i) ≫ (lineIso φ N).hom = E.coordinate i :=
      coordinate φ N i
    exact (congrArg (fun a : AlgebraicSection E.sheaf =>
      pullSection f a ≫ (lineIso ψ N).hom) hg).trans (coordinate ψ N i)
  have hb : (f ≫ g) ≫ StandardTautological.toSpec R N = StandardTautological.toSpec R N := by
    rw [Category.assoc, (mapPoint φ N).property, ← Category.assoc,
      (mapPoint ψ N).property, Category.assoc, base_retraction φ ψ h, Category.comp_id]
  obtain ⟨u, _, hu⟩ := D.universal (StandardTautological.space R N)
    (StandardTautological.toSpec R N) D.sheaf D.locallyFree D.coordinate D.generates
  exact congrArg Subtype.val ((hu ⟨f ≫ g, hb⟩ ⟨c, hc⟩).trans
    (hu ⟨𝟙 _, Category.id_comp _⟩
      ⟨(Scheme.Modules.pullbackId _).app D.sheaf,
        fun i => ExternalExchangeCoherenceProof.pullSection_id (D.coordinate i)⟩).symm)

def squareLineIso {R S : Type} [CommRing R] [CommRing S]
    (φ : R →+* S) (N : ℕ) :
    pullbackModule (map φ N) (tensorLine (StandardTautological.line R N)
      (StandardTautological.line R N)).sheaf ≅
    (tensorLine (StandardTautological.line S N) (StandardTautological.line S N)).sheaf :=
  Classical.choice (tensorSheaf_pullback (map φ N)
    (StandardTautological.line R N).sheaf (StandardTautological.line R N).sheaf) ≪≫
      tensorIso (lineIso φ N) (lineIso φ N)

end LeBrunSalamon.StandardProjectiveBaseChange
end
