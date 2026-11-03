import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Topology of a split nilpotent thickening

These lemmas are proved from mathlib's prime-spectrum and pullback APIs.
They supply the topology needed for the actual dual-number base change;
there is no admitted geometric input in this module.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LeBrunSalamon.NilpotentTopology

/-- A surjective ring map whose kernel consists of nilpotents induces a
surjective map on prime spectra. -/
theorem specMap_surjective_of_nilpotent_ker
    {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (hker : ∀ a : R, f a = 0 → IsNilpotent a) :
    Function.Surjective (Spec.map (CommRingCat.ofHom f)) := by
  change Function.Surjective (PrimeSpectrum.comap f)
  rw [← Set.range_eq_univ, range_comap_of_surjective S f hf,
    PrimeSpectrum.zeroLocus_eq_univ_iff]
  intro a ha
  exact hker a ha

/-- The section obtained by base change of a split morphism is Cartesian.
All maps in the square are the actual pullback maps. -/
theorem splitSection_isPullback
    {Y C D : Scheme} (s : Y ⟶ C) (r : D ⟶ C) (i : C ⟶ D)
    (hi : i ≫ r = 𝟙 C) :
    IsPullback
      (pullback.lift (𝟙 Y) (s ≫ i) (by simp [Category.assoc, hi]))
      s (pullback.snd s r) i := by
  apply IsPullback.of_right (t := IsPullback.of_hasPullback s r)
  · simpa only [pullback.lift_fst, hi] using
      (IsPullback.of_id_fst (f := s))
  · exact pullback.lift_snd _ _ _

/-- A surjective split thickening remains surjective after the actual
base change. No equality of the two schemes is asserted. -/
theorem splitSection_surjective
    {Y C D : Scheme} (s : Y ⟶ C) (r : D ⟶ C) (i : C ⟶ D)
    (hi : i ≫ r = 𝟙 C) (hsurj : Function.Surjective i) :
    Function.Surjective
      (pullback.lift (𝟙 Y) (s ≫ i) (by simp [Category.assoc, hi]) :
        Y ⟶ pullback s r) := by
  intro z
  obtain ⟨c, hc⟩ := hsurj (pullback.snd s r z)
  obtain ⟨y, hy, _⟩ := Scheme.exists_preimage_of_isPullback
    (splitSection_isPullback s r i hi) z c hc.symm
  exact ⟨y, hy⟩

end LeBrunSalamon.NilpotentTopology

end
