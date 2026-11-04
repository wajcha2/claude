import LSHomVelocity
import LSModuleHomGluing

/-! Restriction along an actual open immersion and the canonical module
pullback agree on the original unit sections. These normalizations prove their
composition coherence, so local sheaf morphisms can be compared in charts
without suppressing a chosen comparison isomorphism. No admission. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.Construction
open ExternalExchangeCoherenceProof

namespace LeBrunSalamon.OpenModuleCoherence

theorem presheaf_map_comp_apply {X : Scheme} (E : OModule X)
    {U V W : X.Opens} (i : V ⟶ U) (j : W ⟶ V) (a : SectionsOn E U) :
    E.presheaf.map j.op (E.presheaf.map i.op a) =
      E.presheaf.map (j ≫ i).op a := by
  change (E.presheaf.map i.op ≫ E.presheaf.map j.op) a = _
  rw [← Functor.map_comp]
  rfl

/-- The inverse comparison sends the actual unit image to ordinary
restriction on the corresponding image open. -/
theorem comparison_inv_pullLocalSection {X Y : Scheme} (f : X ⟶ Y)
    [IsOpenImmersion f] (E : OModule Y) (U : Y.Opens) (e : SectionsOn E U) :
    ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app E).app (f ⁻¹ᵁ U)
      (pullLocalSection f E U e) =
        E.presheaf.map (homOfLE (f.image_preimage_le U)).op e := by
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) E
  have hv := congrArg (fun k : E ⟶
    (Scheme.Modules.pushforward f).obj (pullbackModule f E) => k.app U e) hu
  change ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app E).app (f ⁻¹ᵁ U)
      (E.presheaf.map (homOfLE (f.image_preimage_le U)).op e) =
        pullLocalSection f E U e at hv
  rw [← hv]
  exact iso_inv_hom_app ((Scheme.Modules.restrictFunctorIsoPullback f).app E) _ _

/-- The canonical comparison respects composition, proved on the original
unit images rather than by choosing a new restriction equivalence. -/
theorem comparison_comp_inv {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (E : OModule Z) :
    (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).inv.app E =
      (Scheme.Modules.pullbackComp f g).inv.app E ≫
        (Scheme.Modules.pullback f).map
          ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app E) ≫
        (Scheme.Modules.restrictFunctorIsoPullback f).inv.app (E.restrict g) ≫
        (Scheme.Modules.restrictFunctorComp f g).inv.app E := by
  apply PullbackPairProof.pullbackHom_ext (f ≫ g) E (E.restrict (f ≫ g))
  intro U e
  change ((Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).inv.app E).app
      ((f ≫ g) ⁻¹ᵁ U) (pullLocalSection (f ≫ g) E U e) =
    ((Scheme.Modules.restrictFunctorComp f g).inv.app E).app ((f ≫ g) ⁻¹ᵁ U)
      (((Scheme.Modules.restrictFunctorIsoPullback f).inv.app (E.restrict g)).app
        ((f ≫ g) ⁻¹ᵁ U)
        (((Scheme.Modules.pullback f).map
          ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app E)).app
          ((f ≫ g) ⁻¹ᵁ U)
          (((Scheme.Modules.pullbackComp f g).inv.app E).app ((f ≫ g) ⁻¹ᵁ U)
            (pullLocalSection (f ≫ g) E U e))))
  rw [comparison_inv_pullLocalSection, pullLocalSection_comp_inv]
  simp only [Scheme.Hom.comp_preimage]
  rw [pullLocalSection_map, comparison_inv_pullLocalSection,
    comparison_inv_pullLocalSection, Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.restrict_map]
  change E.presheaf.map (homOfLE ((f ≫ g).image_preimage_le U)).op e =
    E.presheaf.map (eqToHom (show
        (f ≫ g) ''ᵁ ((f ≫ g) ⁻¹ᵁ U) = g ''ᵁ (f ''ᵁ (f ⁻¹ᵁ (g ⁻¹ᵁ U))) by simp)).op
      (E.presheaf.map ((Scheme.Hom.opensFunctor g).map
        (homOfLE (f.image_preimage_le (g ⁻¹ᵁ U)))).op
        (E.presheaf.map (homOfLE (g.image_preimage_le U)).op e))
  rw [presheaf_map_comp_apply, presheaf_map_comp_apply]
  congr 1

/-- The same normalization in the forward direction. -/
theorem comparison_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (E : OModule Z) :
    (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).hom.app E =
      (Scheme.Modules.restrictFunctorComp f g).hom.app E ≫
        (Scheme.Modules.restrictFunctorIsoPullback f).hom.app (E.restrict g) ≫
        (Scheme.Modules.pullback f).map
          ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app E) ≫
        (Scheme.Modules.pullbackComp f g).hom.app E := by
  let e := (Scheme.Modules.restrictFunctorComp f g).app E ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback f).app (E.restrict g) ≪≫
    (Scheme.Modules.pullback f).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback g).app E) ≪≫
    (Scheme.Modules.pullbackComp f g).app E
  have h : ((Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).app E).symm = e.symm := by
    apply Iso.ext
    exact comparison_comp_inv f g E
  have h' := congrArg (fun i => i.inv) h
  exact h'

/-- Express an actual map of restrictions as a map of canonical pullbacks. -/
def normalize {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    {E F : OModule Y} (q : E.restrict f ⟶ F.restrict f) :
    pullbackModule f E ⟶ pullbackModule f F :=
  (Scheme.Modules.restrictFunctorIsoPullback f).inv.app E ≫ q ≫
    (Scheme.Modules.restrictFunctorIsoPullback f).hom.app F

theorem normalize_injective {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    (E F : OModule Y) : Function.Injective (normalize f (E := E) (F := F)) :=
  (ModuleHomGluing.isoHomEquiv
    ((Scheme.Modules.restrictFunctorIsoPullback f).app E)
    ((Scheme.Modules.restrictFunctorIsoPullback f).app F)).injective

/-- Pull a local map back along another chart, retaining composition. -/
def pullMap {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    {E F : OModule Z} (q : pullbackModule g E ⟶ pullbackModule g F) :
    pullbackModule (f ≫ g) E ⟶ pullbackModule (f ≫ g) F :=
  (Scheme.Modules.pullbackComp f g).inv.app E ≫
    (Scheme.Modules.pullback f).map q ≫ (Scheme.Modules.pullbackComp f g).hom.app F

def pullMapAlong {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (v : X ⟶ Z) (h : f ≫ g = v)
    {E F : OModule Z} (q : pullbackModule g E ⟶ pullbackModule g F) :
    pullbackModule v E ⟶ pullbackModule v F :=
  (compositionPullback f g v h E).inv ≫
    (Scheme.Modules.pullback f).map q ≫ (compositionPullback f g v h F).hom

@[simp] theorem pullMapAlong_rfl {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    {E F : OModule Z} (q : pullbackModule g E ⟶ pullbackModule g F) :
    pullMapAlong f g (f ≫ g) rfl q = pullMap f g q := by
  simp [pullMapAlong, pullMap, compositionPullback]

/-- A fixed global functional can be evaluated before or after the local
map is transported. The structure-sheaf unit is the same on both sides. -/
theorem pullMap_evaluate {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    {E F : OModule Z} (q : pullbackModule g E ⟶ pullbackModule g F)
    (s : F ⟶ structureModule Z) :
    pullMap f g q ≫ (Scheme.Modules.pullback (f ≫ g)).map s ≫
        unitPullbackMap (f ≫ g) =
      (Scheme.Modules.pullbackComp f g).inv.app E ≫
        (Scheme.Modules.pullback f).map
          (q ≫ (Scheme.Modules.pullback g).map s ≫ unitPullbackMap g) ≫
        unitPullbackMap f := by
  have hn := congrArg (fun a => a ≫ unitPullbackMap (f ≫ g))
    ((Scheme.Modules.pullbackComp f g).hom.naturality s).symm
  have hn' : (Scheme.Modules.pullbackComp f g).hom.app F ≫
        (Scheme.Modules.pullback (f ≫ g)).map s ≫ unitPullbackMap (f ≫ g) =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map s) ≫
        (Scheme.Modules.pullback f).map (unitPullbackMap g) ≫ unitPullbackMap f := by
    simpa only [Functor.comp_map, Category.assoc,
      CanonicalPullbackSectionProof.unitPullbackMap_comp_hom] using hn
  simpa only [pullMap, Functor.map_comp, Category.assoc] using
    congrArg (fun a => (Scheme.Modules.pullbackComp f g).inv.app E ≫
      (Scheme.Modules.pullback f).map q ≫ a) hn'


/-- The restriction and pullback transports of an arbitrary local map agree. -/
theorem normalize_restrict {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g]
    {E F : OModule Z} (q : E.restrict g ⟶ F.restrict g) :
    normalize (f ≫ g)
      ((Scheme.Modules.restrictFunctorComp f g).hom.app E ≫
        (Scheme.Modules.restrictFunctor f).map q ≫
        (Scheme.Modules.restrictFunctorComp f g).inv.app F) =
      pullMap f g (normalize g q) := by
  simp only [normalize, comparison_comp_inv, comparison_comp, pullMap,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  have hn := ModuleHomGluing.isoHomEquiv_naturality
    (Scheme.Modules.restrictFunctorIsoPullback f) q
  change (Scheme.Modules.restrictFunctorIsoPullback f).inv.app (E.restrict g) ≫
      (Scheme.Modules.restrictFunctor f).map q ≫
      (Scheme.Modules.restrictFunctorIsoPullback f).hom.app (F.restrict g) =
    (Scheme.Modules.pullback f).map q at hn
  simpa only [Category.assoc] using congrArg
    (fun a => (Scheme.Modules.pullbackComp f g).inv.app E ≫
      (Scheme.Modules.pullback f).map
        ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app E) ≫ a ≫
      (Scheme.Modules.pullback f).map
        ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app F) ≫
      (Scheme.Modules.pullbackComp f g).hom.app F) hn

theorem normalize_restrictAlong {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (v : X ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion v]
    (h : f ≫ g = v) {E F : OModule Z} (q : E.restrict g ⟶ F.restrict g) :
    normalize v (ModuleHomGluing.restrictHomAlong f g v h q) =
      pullMapAlong f g v h (normalize g q) := by
  subst v
  simpa only [ModuleHomGluing.restrictHomAlong,
    ModuleHomGluing.transportRestrictHom_rfl, ModuleHomGluing.restrictLocalHom,
    pullMapAlong_rfl] using normalize_restrict f g q

theorem chartHomAlongEquiv_eq_normalize {X A : Scheme} (E F : OModule X)
    (U : X.Opens) (c : A ≅ U.toScheme) (j : A ⟶ X) [IsOpenImmersion j]
    (h : c.hom ≫ U.ι = j) (q : E.over U ⟶ F.over U) :
    ModuleHomGluing.chartHomAlongEquiv E F U c j h q =
      normalize j (ModuleHomGluing.restrictHomAlong c.hom U.ι j h
        (ModuleHomGluing.openHomEquiv E F U q)) := rfl

/-- On an arbitrary subopen, the map in the selected chart is precisely the
original over-site map restricted to that subopen. All the comparisons are
the canonical ones already normalized on genuine unit sections. -/
theorem chartRestriction {X A : Scheme} (E F : OModule X) (U W : X.Opens)
    (hWU : W ≤ U) (c : A ≅ U.toScheme) (j : A ⟶ X) [IsOpenImmersion j]
    (hc : c.hom ≫ U.ι = j) (d : W.toScheme ⟶ A) [IsOpenImmersion d]
    (hd : d ≫ c.hom = X.homOfLE hWU) (hdj : d ≫ j = W.ι)
    (q : E.over U ⟶ F.over U) :
    normalize W.ι (ModuleHomGluing.openHomEquiv E F W
      (ModuleHomGluing.restrictOverHom (homOfLE hWU) q)) =
      pullMapAlong d j W.ι hdj (ModuleHomGluing.chartHomAlongEquiv E F U c j hc q) := by
  rw [chartHomAlongEquiv_eq_normalize, ← normalize_restrictAlong,
    ModuleHomGluing.openHomEquiv_restrict, ModuleHomGluing.restrictOpenHom_eq_along,
    ModuleHomGluing.restrictHomAlong_comp]
  congr 1
  exact (ModuleHomGluing.restrictHomAlong_congr hd U.ι W.ι
    (by rw [Category.assoc, hc, hdj]) (X.homOfLE_ι hWU)
    (ModuleHomGluing.openHomEquiv E F U q)).symm

end LeBrunSalamon.OpenModuleCoherence
end
