import Mathlib

/-!
A specified surjective local map to a field presents the literal residue
field. The induced spectrum isomorphism changes only the base projection
of an actual cartesian fibre square. Its fibre object and its morphism to
the original scheme remain unchanged, so the original section restriction
and H1 predicate require no replacement or new hypothesis.

No admission is introduced. Off-graph native candidate.
-/

noncomputable section
set_option autoImplicit false
set_option maxErrors 1

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LeBrunSalamon.ResidueFieldPresentation

/-- The specified constant-term quotient reflects units, by the actual
formal-power-series invertibility criterion already in Mathlib. -/
theorem constantCoeff_local (K : Type) [CommRing K] :
    IsLocalHom (PowerSeries.constantCoeff (R := K)) :=
  ⟨fun f hf => PowerSeries.isUnit_iff_constantCoeff.mpr hf⟩

variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K]

/-- The given quotient map, descended to the actual residue field. -/
def equiv (f : R →+* K) [IsLocalHom f] (hf : Function.Surjective f) :
    IsLocalRing.ResidueField R ≃+* K :=
  RingEquiv.ofBijective (IsLocalRing.ResidueField.lift f)
    ⟨(IsLocalRing.ResidueField.lift f).injective, by
      intro a
      obtain ⟨r, hr⟩ := hf a
      exact ⟨IsLocalRing.residue R r,
        (IsLocalRing.ResidueField.lift_residue_apply f r).trans hr⟩⟩

@[simp]
theorem equiv_residue (f : R →+* K) [IsLocalHom f]
    (hf : Function.Surjective f) (r : R) :
    equiv f hf (IsLocalRing.residue R r) = f r :=
  IsLocalRing.ResidueField.lift_residue_apply f r

/-- The actual spectrum isomorphism of the specified field with the
literal residue-field spectrum. -/
def specIso (f : R →+* K) [IsLocalHom f] (hf : Function.Surjective f) :
    Spec (CommRingCat.of K) ≅ Spec (CommRingCat.of (IsLocalRing.ResidueField R)) :=
  Scheme.Spec.mapIso (equiv f hf).toCommRingCatIso.op

theorem specIso_to_base (f : R →+* K) [IsLocalHom f]
    (hf : Function.Surjective f) :
    (specIso f hf).hom ≫ Spec.map
        (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) =
      Spec.map (CommRingCat.ofHom f) := by
  change Spec.map (CommRingCat.ofHom (equiv f hf).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) = _
  rw [← Spec.map_comp]
  congr 1

/-- Change the base projection through the proved residue-field isomorphism.
The original fibre object and its map `p` to `X` are retained literally. -/
theorem pullback_residue {X Y : Scheme}
    (sX : X ⟶ Spec (CommRingCat.of R)) (p : Y ⟶ X)
    (q : Y ⟶ Spec (CommRingCat.of K))
    (f : R →+* K) [IsLocalHom f] (hf : Function.Surjective f)
    (h : IsPullback p q sX (Spec.map (CommRingCat.ofHom f))) :
    IsPullback p (q ≫ (specIso f hf).hom) sX
      (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))) := by
  apply h.of_iso (Iso.refl Y) (Iso.refl X) (specIso f hf)
    (Iso.refl (Spec (CommRingCat.of R)))
  · simp
  · simp
  · simp
  · simpa using (specIso_to_base f hf).symm

end LeBrunSalamon.ResidueFieldPresentation

end
