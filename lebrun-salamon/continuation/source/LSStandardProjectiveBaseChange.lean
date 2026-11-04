import LSStandardTautological

/-! Base change of the standard projective quotient, proved from its
actual universal property. The map and the tautological comparison are
constructed together; no base-change admission is introduced. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Refinement

namespace LeBrunSalamon.StandardProjectiveBaseChange

theorem pull_generates {X Y : Scheme.{0}} {N : ℕ} {L : OModule Y}
    (a : Fin (N+1) → AlgebraicSection L) (ha : Epi (Sigma.desc a)) (f : X ⟶ Y) :
    Epi (Sigma.desc (fun i => pullSection f (a i))) := by
  let F : SheafOfModules.{0} Y.ringCatSheaf ⥤ SheafOfModules.{0} X.ringCatSheaf :=
    Scheme.Modules.pullback f
  letI : F.IsLeftAdjoint :=
    (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).isLeftAdjoint
  let q : SheafOfModules.free (R := Y.ringCatSheaf) (Fin (N+1)) ⟶ L := Sigma.desc a
  letI : Epi q := ha
  let c := SheafOfModules.mapFreeIso F (Fin (N+1)) (unitPullbackIso f).symm
  have h : Sigma.desc (fun i => pullSection f (a i)) = c.hom ≫ F.map q := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc]
    change pullSection f (a i) = SheafOfModules.ιFree i ≫ c.hom ≫ F.map q
    erw [SheafOfModules.ιFree_mapFreeIso_hom_assoc, ← Functor.map_comp]
    simp only [q, SheafOfModules.ιFree, Sigma.ι_comp_desc,
      pullSection, restrictSection, F, Iso.symm_hom, Category.assoc]
  rw [h]
  infer_instance

theorem composite_coordinate {X Y Z : Scheme.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {A : OModule Z} {B : OModule Y} {C : OModule X}
    (a : AlgebraicSection A) (l : pullbackModule g A ≅ B)
    (k : pullbackModule f B ≅ C) :
    pullSection (f ≫ g) a ≫
      (((Scheme.Modules.pullbackComp f g).app A).symm ≪≫
        (Scheme.Modules.pullback f).mapIso l ≪≫ k).hom =
      pullSection f (pullSection g a ≫ l.hom) ≫ k.hom := by
  let p := (Scheme.Modules.pullbackComp f g).app A
  change pullSection (f ≫ g) a ≫
    (p.inv ≫ (Scheme.Modules.pullback f).map l.hom ≫ k.hom) = _
  rw [← CanonicalPullbackSectionProof.pullSection_comp]
  change (pullSection f (pullSection g a) ≫ p.hom) ≫
    (p.inv ≫ (Scheme.Modules.pullback f).map l.hom ≫ k.hom) = _
  simp only [Category.assoc, p.hom_inv_id_assoc]
  rw [ExternalExchangeCoherenceProof.pullSection_map, Category.assoc]

/-- The inverse normalization is proved on abstract schemes and modules,
before inserting the larger projective-space expressions. -/
theorem inverse_composite_coordinate {X Y Z : Scheme.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hfg : f ≫ g = k)
    {A : OModule Z} {B : OModule Y}
    (a : AlgebraicSection A) (b : AlgebraicSection B)
    (l : pullbackModule g A ≅ B) (hl : pullSection g a ≫ l.hom = b) :
    pullSection f b ≫
      ((Scheme.Modules.pullback f).mapIso l.symm ≪≫
        (Scheme.Modules.pullbackComp f g).app A ≪≫
        (Scheme.Modules.pullbackCongr hfg).app A).hom = pullSection k a := by
  subst k
  change pullSection f b ≫
    ((Scheme.Modules.pullback f).map l.inv ≫
      ((Scheme.Modules.pullbackComp f g).app A).hom) = pullSection (f ≫ g) a
  rw [← hl, ExternalExchangeCoherenceProof.pullSection_map]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, l.hom_inv_id,
    (Scheme.Modules.pullback f).map_id, Category.id_comp]
  exact CanonicalPullbackSectionProof.pullSection_comp f g a

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (N : ℕ)

abbrev base : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom φ)

def mapPoint : {b : StandardTautological.space S N ⟶ StandardTautological.space R N //
    b ≫ StandardTautological.toSpec R N = StandardTautological.toSpec S N ≫ base φ} :=
  Classical.choose ((StandardTautological.chosen R N).universal
    (StandardTautological.space S N) (StandardTautological.toSpec S N ≫ base φ)
    (StandardTautological.line S N).sheaf (StandardTautological.line S N).locallyFree
    (StandardTautological.coordinate S N) (StandardTautological.generates S N))

abbrev map : StandardTautological.space S N ⟶ StandardTautological.space R N :=
  (mapPoint φ N).val

theorem map_spec :
    ∃ e : pullbackModule (map φ N) (StandardTautological.line R N).sheaf ≅
        (StandardTautological.line S N).sheaf,
      ∀ i, pullSection (map φ N) (StandardTautological.coordinate R N i) ≫ e.hom =
        StandardTautological.coordinate S N i :=
  (Classical.choose_spec ((StandardTautological.chosen R N).universal
    (StandardTautological.space S N) (StandardTautological.toSpec S N ≫ base φ)
    (StandardTautological.line S N).sheaf (StandardTautological.line S N).locallyFree
    (StandardTautological.coordinate S N) (StandardTautological.generates S N))).1

def lineIso : pullbackModule (map φ N) (StandardTautological.line R N).sheaf ≅
    (StandardTautological.line S N).sheaf := Classical.choose (map_spec φ N)

theorem coordinate (i : Fin (N+1)) :
    pullSection (map φ N) (StandardTautological.coordinate R N i) ≫ (lineIso φ N).hom =
      StandardTautological.coordinate S N i := Classical.choose_spec (map_spec φ N) i

theorem universal (T : Scheme.{0})
    (f : T ⟶ StandardTautological.space R N) (s : T ⟶ Spec (CommRingCat.of S))
    (h : f ≫ StandardTautological.toSpec R N = s ≫ base φ) :
    ∃! g : T ⟶ StandardTautological.space S N,
      g ≫ map φ N = f ∧ g ≫ StandardTautological.toSpec S N = s := by
  let D := StandardTautological.chosen R N
  let E := StandardTautological.chosen S N
  let F := pullbackLine f (StandardTautological.line R N)
  let a := fun i => pullSection f (StandardTautological.coordinate R N i)
  have ha : Epi (Sigma.desc a) :=
    pull_generates (StandardTautological.coordinate R N) (StandardTautological.generates R N) f
  obtain ⟨g, ⟨l, hl⟩, huniq⟩ := E.universal T s F.sheaf F.locallyFree a ha
  let c : pullbackModule (g.val ≫ map φ N) (StandardTautological.line R N).sheaf ≅ F.sheaf :=
    ((Scheme.Modules.pullbackComp g.val (map φ N)).app D.sheaf).symm ≪≫
      (Scheme.Modules.pullback g.val).mapIso (lineIso φ N) ≪≫ l
  have hc (i : Fin (N+1)) :
      pullSection (g.val ≫ map φ N) (D.coordinate i) ≫ c.hom = a i := by
    rw [composite_coordinate]
    have hcoord : pullSection (map φ N) (D.coordinate i) ≫ (lineIso φ N).hom =
        E.coordinate i := coordinate φ N i
    exact (congrArg (fun t : AlgebraicSection E.sheaf => pullSection g.val t ≫ l.hom)
      hcoord).trans (hl i)
  have hgb : (g.val ≫ map φ N) ≫ StandardTautological.toSpec R N = s ≫ base φ := by
    rw [Category.assoc, (mapPoint φ N).property, ← Category.assoc, g.property]
  obtain ⟨u, _, hu⟩ := D.universal T (s ≫ base φ) F.sheaf F.locallyFree a ha
  have hgf : g.val ≫ map φ N = f :=
    congrArg Subtype.val ((hu ⟨g.val ≫ map φ N, hgb⟩ ⟨c, hc⟩).trans
      (hu ⟨f, h⟩ ⟨Iso.refl _, fun i => Category.comp_id _⟩).symm)
  refine ⟨g.val, ⟨hgf, g.property⟩, ?_⟩
  intro k hk
  have hkf := hk.1
  let e : pullbackModule k E.sheaf ≅ F.sheaf :=
    (Scheme.Modules.pullback k).mapIso (lineIso φ N).symm ≪≫
      (Scheme.Modules.pullbackComp k (map φ N)).app D.sheaf ≪≫
      (Scheme.Modules.pullbackCongr hkf).app D.sheaf
  have he (i : Fin (N+1)) : pullSection k (E.coordinate i) ≫ e.hom = a i := by
    exact inverse_composite_coordinate k (map φ N) f hkf (D.coordinate i)
      (E.coordinate i) (lineIso φ N) (coordinate φ N i)
  exact congrArg Subtype.val ((huniq ⟨k, hk.2⟩ ⟨e, he⟩).trans
    (huniq g ⟨l, hl⟩).symm)

theorem isPullback : IsPullback (map φ N) (StandardTautological.toSpec S N)
    (StandardTautological.toSpec R N) (base φ) := by
  refine ⟨⟨(mapPoint φ N).property⟩, ⟨?_⟩⟩
  apply PullbackCone.IsLimit.mk _
    (fun c => Classical.choose (universal φ N c.pt c.fst c.snd c.condition))
  · intro c
    exact (Classical.choose_spec (universal φ N c.pt c.fst c.snd c.condition)).1.1
  · intro c
    exact (Classical.choose_spec (universal φ N c.pt c.fst c.snd c.condition)).1.2
  · intro c m hm₁ hm₂
    exact (Classical.choose_spec (universal φ N c.pt c.fst c.snd c.condition)).2 m ⟨hm₁, hm₂⟩

end LeBrunSalamon.StandardProjectiveBaseChange

end
