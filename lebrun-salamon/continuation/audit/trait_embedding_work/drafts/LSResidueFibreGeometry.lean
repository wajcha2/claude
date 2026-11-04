import LSResidueFieldPresentation

/-! The actual fibre over a given field quotient and the literal residue
fibre have isomorphic schemes. Smoothness and reducedness are transported
using their actual projections and the specified field isomorphism. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LeBrunSalamon.ResidueFibreGeometry

variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K]
  {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R))
  (φ : R →+* K) [IsLocalHom φ] (hφ : Function.Surjective φ)

abbrev quotientPoint : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom φ)

abbrev residuePoint : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))

def iso : pullback p (quotientPoint φ) ≅ pullback p (residuePoint (R := R)) :=
  (ResidueFieldPresentation.pullback_residue p
    (pullback.fst p (quotientPoint φ)) (pullback.snd p (quotientPoint φ)) φ hφ
    (IsPullback.of_hasPullback p (quotientPoint φ))).isoPullback

@[reassoc] theorem iso_projection : (iso p φ hφ).hom ≫ pullback.snd p (residuePoint (R := R)) =
    pullback.snd p (quotientPoint φ) ≫ (ResidueFieldPresentation.specIso φ hφ).hom :=
  (ResidueFieldPresentation.pullback_residue p
    (pullback.fst p (quotientPoint φ)) (pullback.snd p (quotientPoint φ)) φ hφ
    (IsPullback.of_hasPullback p (quotientPoint φ))).isoPullback_hom_snd

include hφ in
theorem smooth_residue [Smooth (pullback.snd p (quotientPoint φ))] :
    Smooth (pullback.snd p (residuePoint (R := R))) := by
  let e := iso p φ hφ
  letI : IsIso e.inv := e.isIso_inv
  have he : pullback.snd p (residuePoint (R := R)) =
      e.inv ≫ (pullback.snd p (quotientPoint φ) ≫ (ResidueFieldPresentation.specIso φ hφ).hom) := by
    rw [← iso_projection p φ hφ, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [he]
  infer_instance

include hφ in
theorem smooth_quotient [Smooth (pullback.snd p (residuePoint (R := R)))] :
    Smooth (pullback.snd p (quotientPoint φ)) := by
  let e := iso p φ hφ
  letI : IsIso e.hom := e.isIso_hom
  have he : pullback.snd p (quotientPoint φ) =
      (e.hom ≫ pullback.snd p (residuePoint (R := R))) ≫
        (ResidueFieldPresentation.specIso φ hφ).inv := by
    rw [iso_projection p φ hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [he]
  infer_instance

include hφ in
theorem reduced_residue [IsReduced (pullback p (quotientPoint φ))] :
    IsReduced (pullback p (residuePoint (R := R))) := by
  let e := iso p φ hφ
  letI : IsIso e.inv := e.isIso_inv
  exact isReduced_of_isOpenImmersion e.inv

end LeBrunSalamon.ResidueFibreGeometry
end
