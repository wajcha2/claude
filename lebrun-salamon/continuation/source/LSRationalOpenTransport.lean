import LSFormalArcRegularity

/-!
# Actual-open transport for rational-section regularity

Local sections are pulled by the unit of the genuine module-sheaf
adjunction.  The conversion to a section on an open subscheme is the
existing restriction/pullback comparison.  This file proves their
compatibility and retains every composition isomorphism in the generic
criterion for regularity.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton
open LeBrunSalamon.PhaseTwentyEight.ExternalExchangeCoherenceProof
open LeBrunSalamon.Refinement (pullbackSquareIso)

namespace LeBrunSalamon.Construction.FamilyBivectors.OpenSection

/-- Pull a local section to the whole source when its image lies in
the given open, using the literal presheaf restriction after the unit. -/
def onWhole {T Y : Scheme} (f : T ⟶ Y) (E : OModule Y) (U : Y.Opens)
    (h : ⊤ ≤ f ⁻¹ᵁ U) (s : SectionsOn E U) : AlgebraicSection (pullbackModule f E) :=
  sectionFromValue ((pullbackModule f E).presheaf.map (homOfLE h).op
    (pullLocalSection f E U s))

/-- Uniqueness of left adjoints identifies the actual open-section
construction with the local pullback unit. -/
theorem fromValue_eq_onWhole {Y : Scheme} (U : Y.Opens) {E : OModule Y}
    (s : SectionsOn E U) :
    fromValue U s = onWhole U.ι E U U.ι_preimage_self.ge s := by
  have hunit := Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction U.ι)
    (Scheme.Modules.pullbackPushforwardAdjunction U.ι) E
  have hu := congrArg (fun m : E ⟶
    (Scheme.Modules.pushforward U.ι).obj (pullbackModule U.ι E) => m.app U s) hunit
  change ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app E).app (U.ι ⁻¹ᵁ U)
      (E.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op s) =
    pullLocalSection U.ι E U s at hu
  apply (sectionValue_bijective (pullbackModule U.ι E)).injective
  rw [fromValue, sectionValue_comp, sectionFromValue_spec, onWhole, sectionFromValue_spec,
    ← hu, sheafHom_naturality]
  change ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app E).app ⊤
      (E.presheaf.map (eqToHom U.ι_image_top).op s) =
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app E).app ⊤
      (E.presheaf.map (U.ι.opensFunctor.map (homOfLE U.ι_preimage_self.ge)).op
        (E.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op s))
  congr 1
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  have hmap : eqToHom U.ι_image_top =
      U.ι.opensFunctor.map (homOfLE U.ι_preimage_self.ge) ≫
        homOfLE (U.ι.image_preimage_le U) := Subsingleton.elim _ _
  rw [hmap]

/-- Pullback of a globally realized local section is the successive
local unit pullback on the actual inverse-image open. -/
theorem onWhole_pull {T Y Z : Scheme} (f : T ⟶ Y) (g : Y ⟶ Z)
    (E : OModule Z) (U : Z.Opens) (hg : ⊤ ≤ g ⁻¹ᵁ U)
    (hfg : ⊤ ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U)) (s : SectionsOn E U) :
    pullSection f (onWhole g E U hg s) =
      onWhole f (pullbackModule g E) (g ⁻¹ᵁ U) hfg (pullLocalSection g E U s) := by
  apply (sectionValue_bijective (pullbackModule f (pullbackModule g E))).injective
  rw [pullSection_value, onWhole, sectionFromValue_spec, onWhole, sectionFromValue_spec]
  change pullLocalSection f (pullbackModule g E) ⊤
      ((pullbackModule g E).presheaf.map (homOfLE hg).op (pullLocalSection g E U s)) =
    (pullbackModule f (pullbackModule g E)).presheaf.map (homOfLE hfg).op
      (pullLocalSection f (pullbackModule g E) (g ⁻¹ᵁ U) (pullLocalSection g E U s))
  exact (PullbackPairProof.pullLocalSection_restrict f (pullbackModule g E)
    (homOfLE hg) (pullLocalSection g E U s)).symm

/-- Composition on local sections, normalized on the whole source. -/
theorem onWhole_local_comp {T Y Z : Scheme} (f : T ⟶ Y) (g : Y ⟶ Z)
    (E : OModule Z) (U : Z.Opens) (hfg : ⊤ ≤ (f ≫ g) ⁻¹ᵁ U)
    (s : SectionsOn E U) :
    onWhole f (pullbackModule g E) (g ⁻¹ᵁ U) hfg (pullLocalSection g E U s) ≫
        (Scheme.Modules.pullbackComp f g).hom.app E =
      onWhole (f ≫ g) E U hfg s := by
  apply (sectionValue_bijective (pullbackModule (f ≫ g) E)).injective
  rw [sectionValue_comp, onWhole, sectionFromValue_spec, onWhole, sectionFromValue_spec]
  rw [← sheafHom_naturality]
  exact congrArg ((pullbackModule (f ≫ g) E).presheaf.map (homOfLE hfg).op)
    (pullLocalSection_comp f g E U s)

theorem onWhole_local_composition {T Y Z : Scheme}
    (f : T ⟶ Y) (g : Y ⟶ Z) (r : T ⟶ Z) (h : f ≫ g = r)
    (E : OModule Z) (U : Z.Opens) (hr : ⊤ ≤ r ⁻¹ᵁ U)
    (hfg : ⊤ ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U)) (s : SectionsOn E U) :
    onWhole f (pullbackModule g E) (g ⁻¹ᵁ U) hfg (pullLocalSection g E U s) ≫
        (compositionPullback f g r h E).hom = onWhole r E U hr s := by
  subst r
  simpa only [compositionPullback, Iso.trans_hom, Iso.app_hom,
    eqToIso_refl, Iso.refl_hom, Category.comp_id] using onWhole_local_comp f g E U hr s

theorem onWhole_composition {T Y Z : Scheme}
    (f : T ⟶ Y) (g : Y ⟶ Z) (r : T ⟶ Z) (h : f ≫ g = r)
    (E : OModule Z) (U : Z.Opens) (hg : ⊤ ≤ g ⁻¹ᵁ U)
    (hr : ⊤ ≤ r ⁻¹ᵁ U) (s : SectionsOn E U) :
    pullSection f (onWhole g E U hg s) ≫
        (compositionPullback f g r h E).hom = onWhole r E U hr s := by
  have hfg : ⊤ ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U) := by
    simpa only [← h, Scheme.Hom.comp_preimage] using hr
  rw [onWhole_pull f g E U hg hfg s]
  exact onWhole_local_composition f g r h E U hr hfg s

/-- The restriction of an actual morphism transports the existing
open section to the local unit pullback on its complete inverse image. -/
theorem fromValue_pullback {T Y : Scheme} (f : T ⟶ Y) (U : Y.Opens)
    {E : OModule Y} (s : SectionsOn E U)
    (j : (f ⁻¹ᵁ U).toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f) :
    pullSection j (fromValue U s) ≫
        (pullbackSquareIso j U.ι (f ⁻¹ᵁ U).ι f hj E).hom =
      fromValue (f ⁻¹ᵁ U) (pullLocalSection f E U s) := by
  let V := f ⁻¹ᵁ U
  have hr : ⊤ ≤ (V.ι ≫ f) ⁻¹ᵁ U := V.ι_preimage_self.ge
  apply (cancel_mono (compositionPullback V.ι f (V.ι ≫ f) rfl E).hom).mp
  rw [Category.assoc, FlatSectionDescent.squareIso_comp_composition,
    fromValue_eq_onWhole U s,
    onWhole_composition j U.ι (V.ι ≫ f) hj E U U.ι_preimage_self.ge hr s,
    fromValue_eq_onWhole V (pullLocalSection f E U s)]
  exact (onWhole_local_composition V.ι f (V.ι ≫ f) rfl E U hr
    V.ι_preimage_self.ge s).symm

theorem fromValue_morphismRestrict {T Y : Scheme} (f : T ⟶ Y) (U : Y.Opens)
    {E : OModule Y} (s : SectionsOn E U) :
    pullSection (f ∣_ U) (fromValue U s) ≫
        (pullbackSquareIso (f ∣_ U) U.ι (f ⁻¹ᵁ U).ι f (morphismRestrict_ι f U) E).hom =
      fromValue (f ⁻¹ᵁ U) (pullLocalSection f E U s) :=
  fromValue_pullback f U s (f ∣_ U) (morphismRestrict_ι f U)

end LeBrunSalamon.Construction.FamilyBivectors.OpenSection

namespace LeBrunSalamon.Construction.StableMaps.FormalArcs

open FamilyBivectors

/-- A canonically normalized comparison at the actual fraction-field
point proves regularity on the complete inverse-image open.  The local
section on its original open is transported by its actual factor map. -/
theorem regular_of_normalized_generic_comparison {Y : Scheme} {r : ℕ}
    (E : AlgebraicVectorBundle Y r) (s : NormalExtension.RationalSection E.sheaf)
    (gamma : Trait ⟶ Y) (hU : Dense (gamma ⁻¹ᵁ s.domain : Set Trait))
    (w : AlgebraicSection (pullbackModule gamma E.sheaf))
    (g : GenericPoint ⟶ s.domain.toScheme)
    (hg : g ≫ s.domain.ι = genericPoint ≫ gamma)
    (h : pullSection genericPoint w ≫
        (compositionPullback genericPoint gamma (genericPoint ≫ gamma) rfl E.sheaf).hom =
      pullSection g (OpenSection.fromValue s.domain s.value) ≫
        (compositionPullback g s.domain.ι (genericPoint ≫ gamma) hg E.sheaf).hom) :
    Regular s gamma := by
  let V := gamma ⁻¹ᵁ s.domain
  let j : V.toScheme ⟶ s.domain.toScheme := gamma ∣_ s.domain
  have hj : j ≫ s.domain.ι = V.ι ≫ gamma := morphismRestrict_ι gamma s.domain
  let v : GenericPoint ⟶ V.toScheme := genericToOpen V hU
  have hv : v ≫ V.ι = genericPoint := genericToOpen_inclusion V hU
  have hvg : v ≫ j = g := by
    apply (cancel_mono s.domain.ι).mp
    rw [Category.assoc, hj, ← Category.assoc, hv, hg]
  subst g
  apply regular_of_generic_comparison E s gamma hU w
  let A := compositionPullback v V.ι genericPoint hv (pullbackModule gamma E.sheaf)
  let B := compositionPullback genericPoint gamma (genericPoint ≫ gamma) rfl E.sheaf
  apply (cancel_mono (A.hom ≫ B.hom)).mp
  have hleft : pullSection v (pullSection V.ι w) ≫ A.hom ≫ B.hom =
      pullSection genericPoint w ≫ B.hom := by
    rw [← Category.assoc, compositionPullback_sections]
  have hright : pullSection v (OpenSection.fromValue V
        (pullLocalSection gamma E.sheaf s.domain s.value)) ≫ A.hom ≫ B.hom =
      pullSection (v ≫ j) (OpenSection.fromValue s.domain s.value) ≫
        (compositionPullback (v ≫ j) s.domain.ι (genericPoint ≫ gamma) hg E.sheaf).hom := by
    rw [← OpenSection.fromValue_pullback gamma s.domain s.value j hj,
      pullSection_naturality]
    simp only [Category.assoc]
    rw [SectionTransport.square_comp v j s.domain.ι V.ι gamma hj
      genericPoint hv (genericPoint ≫ gamma) rfl hg E.sheaf,
      ← Category.assoc, compositionPullback_sections]
  exact hleft.trans (h.trans hright.symm)

end LeBrunSalamon.Construction.StableMaps.FormalArcs

end
