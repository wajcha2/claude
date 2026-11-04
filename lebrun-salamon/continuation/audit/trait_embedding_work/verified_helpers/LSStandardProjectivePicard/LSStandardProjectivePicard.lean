import LSStandardProjectiveComposition
import LSProjectiveFibreLineRigidity

/-! Transfer the already proved projective-bundle fibre rigidity to the
literal polynomial Proj and its literal residue map.  The comparison
isomorphism, both projections, and the actual fibre are identified.
There is no new admitted Picard or normal-form statement. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.StandardProjectivePicard

variable {R : Type} [CommRing R]

def productIso (φ : ℂ →+* R) (N : ℕ) :
    StandardTautological.space R N ≅
      ProjectiveFibreLineRigidity.product N (StandardProjectiveBaseChange.base φ) :=
  (StandardProjectiveBaseChange.isPullback φ N).isoPullback

theorem productIso_fst (φ : ℂ →+* R) (N : ℕ) :
    (productIso φ N).hom ≫
      pullback.fst (ProjectiveQuotient.toSpec ℂ N) (StandardProjectiveBaseChange.base φ) =
      StandardProjectiveBaseChange.map φ N :=
  (StandardProjectiveBaseChange.isPullback φ N).isoPullback_hom_fst

theorem productIso_snd (φ : ℂ →+* R) (N : ℕ) :
    (productIso φ N).hom ≫
      pullback.snd (ProjectiveQuotient.toSpec ℂ N) (StandardProjectiveBaseChange.base φ) =
      StandardTautological.toSpec R N :=
  (StandardProjectiveBaseChange.isPullback φ N).isoPullback_hom_snd

theorem fibre_productIso (φ : ℂ →+* R) (ψ : R →+* ℂ)
    (h : ψ.comp φ = RingHom.id ℂ) (N : ℕ) :
    StandardProjectiveBaseChange.map ψ N ≫ (productIso φ N).hom =
      ProjectiveFibreLineRigidity.fibre N (StandardProjectiveBaseChange.base φ)
        (StandardProjectiveBaseChange.base ψ) (StandardProjectiveBaseChange.base_retraction φ ψ h) := by
  apply pullback.hom_ext
  · rw [Category.assoc, productIso_fst, StandardProjectiveBaseChange.map_retraction φ ψ h]
    exact (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, productIso_snd, (StandardProjectiveBaseChange.mapPoint ψ N).property]
    exact (pullback.lift_snd _ _ _).symm

/-- The selected fibre determines the line on the actual projective
space over the affine UFD.  In particular it compares the positive
Cartier divisor line with the actual standard O(2). -/
theorem iso_of_fibre_iso
    [IsDomain R] [UniqueFactorizationMonoid R]
    [IsLocallyNoetherian (Spec (CommRingCat.of R))]
    [ConnectedSpace (Spec (CommRingCat.of R))]
    (φ : ℂ →+* R) (ψ : R →+* ℂ) (h : ψ.comp φ = RingHom.id ℂ)
    (N : ℕ) (hN : 1 ≤ N)
    (L M : LineBundle (StandardTautological.space R N))
    (e0 : pullbackModule (StandardProjectiveBaseChange.map ψ N) L.sheaf ≅
      pullbackModule (StandardProjectiveBaseChange.map ψ N) M.sheaf) :
    Nonempty (L.sheaf ≅ M.sheaf) := by
  let e := productIso φ N
  let a := StandardProjectiveBaseChange.base ψ
  let s := StandardProjectiveBaseChange.base φ
  have ha : a ≫ s = 𝟙 _ := StandardProjectiveBaseChange.base_retraction φ ψ h
  let f := ProjectiveFibreLineRigidity.fibre N s a ha
  have hf : f ≫ e.inv = StandardProjectiveBaseChange.map ψ N := by
    dsimp only [f, s, a, e]
    rw [← fibre_productIso φ ψ h N, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let cL := P1FamilyDegree.pullComp f e.inv (StandardProjectiveBaseChange.map ψ N) hf L.sheaf
  let cM := P1FamilyDegree.pullComp f e.inv (StandardProjectiveBaseChange.map ψ N) hf M.sheaf
  obtain ⟨d⟩ := ProjectiveFibreLineRigidity.iso_of_fibre_iso N hN s a ha
    (pullbackLine e.inv L) (pullbackLine e.inv M) (cL ≪≫ e0 ≪≫ cM.symm)
  let uL : pullbackModule e.hom (pullbackModule e.inv L.sheaf) ≅ L.sheaf :=
    P1FamilyDegree.pullComp e.hom e.inv (𝟙 _) e.hom_inv_id L.sheaf ≪≫
      (Scheme.Modules.pullbackId _).app L.sheaf
  let uM : pullbackModule e.hom (pullbackModule e.inv M.sheaf) ≅ M.sheaf :=
    P1FamilyDegree.pullComp e.hom e.inv (𝟙 _) e.hom_inv_id M.sheaf ≪≫
      (Scheme.Modules.pullbackId _).app M.sheaf
  exact ⟨uL.symm ≪≫ (Scheme.Modules.pullback e.hom).mapIso d ≪≫ uM⟩

end LeBrunSalamon.StandardProjectivePicard
end
