import LSNodalLineCohomology
import LSNonvanishingPullback

/-! Actual line comparison on a pushout with a split node inclusion.
Branch frames are normalized using a pulled-back unit automorphism, then
glued through the represented total line. No Picard-of-a-tree or line
normal-form assertion is admitted.+-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.Construction.Normalization.NodeCohomology

namespace LeBrunSalamon.NodalLineTriviality

/-- An open containing both branch images contains the supplied pushout.
This uses only the actual universal property, not a topological surrogate. -/
theorem open_eq_top {A B N Y : Scheme}
    {p : N ⟶ A} {q : N ⟶ B} {i : A ⟶ Y} {j : B ⟶ Y}
    (hpush : IsPushout p q i j) (U : Y.Opens)
    (hi : Set.range i ⊆ Set.range U.ι)
    (hj : Set.range j ⊆ Set.range U.ι) : U = ⊤ := by
  let a := IsOpenImmersion.lift U.ι i hi
  let b := IsOpenImmersion.lift U.ι j hj
  have ha : a ≫ U.ι = i := IsOpenImmersion.lift_fac _ _ _
  have hb : b ≫ U.ι = j := IsOpenImmersion.lift_fac _ _ _
  have hc : p ≫ a = q ≫ b := by
    apply (cancel_mono U.ι).mp
    simpa only [Category.assoc, ha, hb] using hpush.w
  let r : Y ⟶ U.toScheme := hpush.desc a b hc
  have hr : r ≫ U.ι = 𝟙 Y := by
    apply hpush.hom_ext
    · rw [← Category.assoc, hpush.inl_desc, ha, Category.comp_id]
    · rw [← Category.assoc, hpush.inr_desc, hb, Category.comp_id]
  apply top_unique
  intro x hx
  have he : U.ι (r x) = x := congrArg (fun f : Y ⟶ Y => f x) hr
  exact he ▸ (r x).property

theorem pullSection_isIso {X Y : Scheme} (f : X ⟶ Y)
    {E : OModule Y} (a : AlgebraicSection E) [IsIso a] : IsIso (pullSection f a) := by
  dsimp [pullSection, restrictSection]
  infer_instance

/-- The specified unit comparison along the identity equals the functor's
identity comparison; both normalize the same pulled-back identity section. -/
theorem unitPullback_identity (Y : Scheme) :
    (unitPullbackIso (𝟙 Y)).hom = (Scheme.Modules.pullbackId Y).hom.app (structureModule Y) := by
  letI := pullSection_isIso (𝟙 Y) (𝟙 (structureModule Y))
  apply (cancel_epi (pullSection (𝟙 Y) (𝟙 (structureModule Y)))).mp
  exact (pullSection_identity_unit (𝟙 Y)).trans
    (ExternalExchangeCoherenceProof.pullSection_id (𝟙 (structureModule Y))).symm

/-- Pull a unit automorphism from the node to a branch and evaluate it
back at that same node, retaining both actual unit comparisons. -/
theorem scalar_return {N A : Scheme} (p : N ⟶ A) (s : A ⟶ N)
    (hs : p ≫ s = 𝟙 N) (d : structureModule N ⟶ structureModule N) :
    pullSection p (pullSection s d ≫ (unitPullbackIso s).hom) ≫
        (unitPullbackIso p).hom = d := by
  rw [pullSection_naturality, Category.assoc, ← compositionPullback_unit p s (𝟙 N) hs,
    ← Category.assoc, compositionPullback_sections, unitPullback_identity,
    ExternalExchangeCoherenceProof.pullSection_id]

theorem scalar_normalized {N A Y : Scheme}
    (p : N ⟶ A) (i : A ⟶ Y) (E : OModule Y)
    (a : AlgebraicSection (pullbackModule i E))
    (d : structureModule A ⟶ structureModule A) :
    pullSection p (d ≫ a) ≫ (compositionPullback p i (p ≫ i) rfl E).hom =
      (pullSection p d ≫ (unitPullbackIso p).hom) ≫
        (pullSection p a ≫ (compositionPullback p i (p ≫ i) rfl E).hom) := by
  simp only [pullSection, restrictSection, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc]

/-- If the pulled-back section is invertible on both branches, the
original section is invertible on the actual pushout. -/
theorem section_isIso {A B N Y : Scheme.{0}}
    {p : N ⟶ A} {q : N ⟶ B} {i : A ⟶ Y} {j : B ⟶ Y}
    (hpush : IsPushout p q i j) (L : LineBundle Y)
    (a : AlgebraicSection L.sheaf)
    (hi : IsIso (pullSection i a)) (hj : IsIso (pullSection j a)) : IsIso a := by
  apply (nonvanishingOpen_eq_top_iff L a).mp
  apply open_eq_top hpush
  · rw [Scheme.Opens.range_ι]
    rintro x ⟨z, rfl⟩
    have hU : nonvanishingOpen (pullbackLine i L) (pullSection i a) = ⊤ :=
      (nonvanishingOpen_eq_top_iff _ _).mpr hi
    rw [← NonvanishingPullbackProof.nonvanishingOpen_pullback] at hU
    change z ∈ i ⁻¹ᵁ nonvanishingOpen L a
    rw [hU]
    trivial
  · rw [Scheme.Opens.range_ι]
    rintro x ⟨z, rfl⟩
    have hU : nonvanishingOpen (pullbackLine j L) (pullSection j a) = ⊤ :=
      (nonvanishingOpen_eq_top_iff _ _).mpr hj
    rw [← NonvanishingPullbackProof.nonvanishingOpen_pullback] at hU
    change z ∈ j ⁻¹ᵁ nonvanishingOpen L a
    rw [hU]
    trivial

/-- A line trivial on both branches is trivial on the pushout when the
node map on one branch has the specified retraction. The scalar matching
is constructed; it is not an extra compatibility assumption. -/
theorem trivial_of_branches {A B N Y : Scheme.{0}}
    (p : N ⟶ A) (q : N ⟶ B) (i : A ⟶ Y) (j : B ⟶ Y)
    (hpush : IsPushout p q i j) (s : A ⟶ N) (hs : p ≫ s = 𝟙 N)
    (L : LineBundle Y)
    (eA : structureModule A ≅ pullbackModule i L.sheaf)
    (eB : structureModule B ≅ pullbackModule j L.sheaf) :
    Nonempty (structureModule Y ≅ L.sheaf) := by
  let z := p ≫ i
  let cA := compositionPullback p i z rfl L.sheaf
  let cB := compositionPullback q j z hpush.w.symm L.sheaf
  let a : AlgebraicSection (pullbackModule z L.sheaf) := pullSection p eA.hom ≫ cA.hom
  let b : AlgebraicSection (pullbackModule z L.sheaf) := pullSection q eB.hom ≫ cB.hom
  letI := pullSection_isIso p eA.hom
  letI := pullSection_isIso q eB.hom
  letI : IsIso a := by dsimp [a]; infer_instance
  letI : IsIso b := by dsimp [b]; infer_instance
  let d : structureModule N ⟶ structureModule N := b ≫ inv a
  letI : IsIso d := by dsimp [d]; infer_instance
  letI := pullSection_isIso s d
  let dA : structureModule A ⟶ structureModule A :=
    pullSection s d ≫ (unitPullbackIso s).hom
  letI : IsIso dA := by dsimp [dA]; infer_instance
  let aA : AlgebraicSection (pullbackModule i L.sheaf) := dA ≫ eA.hom
  have hn : pullSection p aA ≫ cA.hom = b := by
    change pullSection p (dA ≫ eA.hom) ≫ cA.hom = b
    rw [scalar_normalized, scalar_return p s hs]
    change (b ≫ inv a) ≫ a = b
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  obtain ⟨t, htA, htB⟩ := NodalLineCohomology.GlueProof.glue_sections_of_pushout L
    i j p q z rfl hpush.w.symm (NodalLineCohomology.pushout_universal hpush)
    (fun _ _ hl hr => hpush.hom_ext hl hr) aA eB.hom hn
  letI : IsIso t := section_isIso hpush L t
    (by rw [htA]; dsimp [aA]; infer_instance)
    (by rw [htB]; infer_instance)
  exact ⟨asIso t⟩

/-- Tensor comparison reduces a pair of line bundles to the preceding
triviality theorem, using their actual branch isomorphisms. -/
theorem line_iso_of_branch_iso {A B N Y : Scheme.{0}}
    (p : N ⟶ A) (q : N ⟶ B) (i : A ⟶ Y) (j : B ⟶ Y)
    (hpush : IsPushout p q i j) (s : A ⟶ N) (hs : p ≫ s = 𝟙 N)
    (L M : LineBundle Y)
    (eA : pullbackModule i L.sheaf ≅ pullbackModule i M.sheaf)
    (eB : pullbackModule j L.sheaf ≅ pullbackModule j M.sheaf) :
    Nonempty (L.sheaf ≅ M.sheaf) := by
  let K := tensorLine L (dualLine M)
  have branch {T : Scheme.{0}} (f : T ⟶ Y)
      (e : pullbackModule f L.sheaf ≅ pullbackModule f M.sheaf) :
      Nonempty (structureModule T ≅ pullbackModule f K.sheaf) := by
    letI := dualBaseChange_isIso f M.locallyFree
    obtain ⟨et⟩ := tensorSheaf_pullback f L.sheaf (dualSheaf M.sheaf)
    obtain ⟨ev⟩ := line_dual_evaluation (pullbackLine f M)
    exact ⟨(et ≪≫ tensorIso e (asIso (dualBaseChange f M.sheaf)) ≪≫
      TensorConstruction.commIso _ _ ≪≫ ev).symm⟩
  obtain ⟨bA⟩ := branch i eA
  obtain ⟨bB⟩ := branch j eB
  obtain ⟨eK⟩ := trivial_of_branches p q i j hpush s hs K bA bB
  obtain ⟨ev⟩ := line_dual_evaluation M
  apply (LineBundleClasses.tensorLine_cancel_right L M (dualLine M)).mp
  exact ⟨eK.symm ≪≫ (TensorConstruction.commIso _ _ ≪≫ ev).symm⟩

end LeBrunSalamon.NodalLineTriviality

end
