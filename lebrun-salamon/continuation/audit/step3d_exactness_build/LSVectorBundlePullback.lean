import RecompileExtensionCore

/-!
Local splitting and exact pullback for actual module sheaves.

The sole new admission is the ordinary local splitting statement of EGA I,
chapitre 0, (5.4.9), printed p.52. Its hypotheses and conclusion concern the
original short exact sequence and actual restrictions on the underlying scheme.
The arbitrary-base-change statement is proved separately below.

The actual pullback and fiber translations are checked separately; source-graph
acceptance is recorded in the accompanying compiler receipts.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.Skeleton

namespace LeBrunSalamon.VectorBundlePullback

/-- Ordinary local finite freeness, expressed using actual restrictions and
finite free sheaves. The rank may vary between the neighborhoods. -/
def LocallyFiniteFree {X : Scheme.{0}} (E : OModule X) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ r : ℕ, Nonempty
    (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin r) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj E)

/-- EGA I (1960), chapitre 0, (5.4.9), printed p.52: an extension with
finite locally free quotient is locally split. The local retraction is
the complement to the section of the original quotient constructed there.
Publication: https://numdam.org/item/PMIHES_1960__4__5_0/ . -/
theorem _root_.LeBrunSalamon.PublishedInputs.LocalSplitting.finiteFreeQuotient
    {X : Scheme.{0}} {E F G : OModule X}
    (i : E ⟶ F) (q : F ⟶ G) (hz : i ≫ q = 0)
    (hex : (ShortComplex.mk i q hz).ShortExact) (hG : LocallyFiniteFree G)
    (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      ∃ r : (Scheme.Modules.restrictFunctor U.ι).obj F ⟶
          (Scheme.Modules.restrictFunctor U.ι).obj E,
        (Scheme.Modules.restrictFunctor U.ι).map i ≫ r = 𝟙 _ := by
  sorry

/-- A project vector bundle supplies the actual finite free local frames. -/
theorem locallyFiniteFree_of_rank {X : Scheme.{0}} {E : OModule X} {r : ℕ}
    (hE : IsLocallyFreeOfRank E r) : LocallyFiniteFree E := by
  obtain ⟨q, hq, hr⟩ := hE
  letI := hq
  intro x
  obtain ⟨a, hxa⟩ := ((Opens.coversTop_iff X q.X).mp q.coversTop).exists_mem x
  let U : X.Opens := q.X a
  refine ⟨U, hxa, r, ⟨?_⟩⟩
  exact PhaseTwentyEight.DominantSectionInjectivityProof.localFreePullbackIso q hr a ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app E).symm

/-- Isomorphic functors preserve the same monomorphism property. -/
theorem mono_map_of_iso {C D : Type*} [Category C] [Category D]
    {A B : C ⥤ D} (e : A ≅ B) {E F : C} (i : E ⟶ F)
    [Mono (A.map i)] : Mono (B.map i) := by
  constructor
  intro Z u v h
  apply (cancel_mono (e.inv.app E)).1
  apply (cancel_mono (A.map i)).1
  simpa only [Category.assoc, ← e.inv.naturality i] using
    congrArg (fun w => w ≫ e.inv.app F) h

/-- A displayed left inverse makes the original morphism mono. -/
theorem mono_of_retraction {C : Type*} [Category C] {E F : C}
    (i : E ⟶ F) (r : F ⟶ E) (h : i ≫ r = 𝟙 E) : Mono i := by
  constructor
  intro Z u v huv
  calc
    u = (u ≫ i) ≫ r := by rw [Category.assoc, h, Category.comp_id]
    _ = (v ≫ i) ≫ r := by rw [huv]
    _ = v := by rw [Category.assoc, h, Category.comp_id]

/-- Pullback equality along an open immersion gives equality of the
literal restricted maps. -/
theorem restrict_map_eq_of_pullback_map_eq {X : Scheme.{0}} {E F : OModule X}
    (U : X.Opens) (a b : E ⟶ F)
    (h : (Scheme.Modules.pullback U.ι).map a =
      (Scheme.Modules.pullback U.ι).map b) :
    (Scheme.Modules.restrictFunctor U.ι).map a =
      (Scheme.Modules.restrictFunctor U.ι).map b := by
  let e := Scheme.Modules.restrictFunctorIsoPullback U.ι
  apply (cancel_mono (e.hom.app F)).1
  rw [e.hom.naturality a, e.hom.naturality b, h]

/-- Actual local pullbacks detect a mono, by the sheaf axiom on every open. -/
theorem mono_of_locally_mono {X : Scheme.{0}} {E F : OModule X} (i : E ⟶ F)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Mono ((Scheme.Modules.pullback U.ι).map i)) : Mono i := by
  choose U hxU hm using h
  constructor
  intro Z a b hab
  have habU (x : X) :
      (Scheme.Modules.restrictFunctor (U x).ι).map a =
        (Scheme.Modules.restrictFunctor (U x).ι).map b := by
    apply restrict_map_eq_of_pullback_map_eq
    letI := hm x
    apply (cancel_mono ((Scheme.Modules.pullback (U x).ι).map i)).1
    simpa only [← Functor.map_comp] using
      congrArg (fun w => (Scheme.Modules.pullback (U x).ι).map w) hab
  apply Scheme.Modules.hom_ext
  intro W
  apply AddCommGrpCat.ext
  intro s
  apply (TwoChartSections.sectionSheaf E).eq_of_locally_eq'
    (fun x => U x ⊓ W) W (fun _ => homOfLE inf_le_right)
    (by intro x hx; exact (le_iSup (fun y : X => U y ⊓ W) x) ⟨hxU x, hx⟩)
  intro x
  change E.presheaf.map (homOfLE (inf_le_right : U x ⊓ W ≤ W)).op (a.app W s) =
    E.presheaf.map (homOfLE (inf_le_right : U x ⊓ W ≤ W)).op (b.app W s)
  rw [sheafHom_naturality, sheafHom_naturality]
  have he := congrArg (fun f => f.app ((U x).ι ⁻¹ᵁ W)) (habU x)
  change a.app ((U x).ι ''ᵁ ((U x).ι ⁻¹ᵁ W)) =
    b.app ((U x).ι ''ᵁ ((U x).ι ⁻¹ᵁ W)) at he
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] at he
  exact congrArg (fun f => f (Z.presheaf.map (homOfLE inf_le_right).op s)) he

/-- The local retractions in EGA's statement pull back along the actual
restricted morphism. The pullback-composition isomorphisms identify their
maps with the restriction of the original global pullback map. -/
theorem pullback_mono_of_locallyFiniteFree_quotient
    {X Y : Scheme.{0}} (f : X ⟶ Y) {E F G : OModule Y}
    (i : E ⟶ F) (q : F ⟶ G) (hz : i ≫ q = 0)
    (hex : (ShortComplex.mk i q hz).ShortExact) (hG : LocallyFiniteFree G) :
    Mono ((Scheme.Modules.pullback f).map i) := by
  apply mono_of_locally_mono
  intro x
  obtain ⟨U, hxU, r, hr⟩ :=
    PublishedInputs.LocalSplitting.finiteFreeQuotient i q hz hex hG (f x)
  let V := f ⁻¹ᵁ U
  let e := Scheme.Modules.restrictFunctorIsoPullback U.ι
  let rU : (Scheme.Modules.pullback U.ι).obj F ⟶
      (Scheme.Modules.pullback U.ι).obj E :=
    e.inv.app F ≫ r ≫ e.hom.app E
  have hrU : (Scheme.Modules.pullback U.ι).map i ≫ rU = 𝟙 _ := by
    dsimp only [rU]
    rw [← Category.assoc, e.inv.naturality]
    have he := congrArg (fun w => e.inv.app E ≫ w ≫ e.hom.app E) hr
    simpa only [Category.assoc, Category.id_comp, e.inv_hom_id_app] using he
  let H := Scheme.Modules.pullback (f ∣_ U)
  have hrV : H.map ((Scheme.Modules.pullback U.ι).map i) ≫ H.map rU = 𝟙 _ := by
    rw [← H.map_comp, hrU, H.map_id]
  letI : Mono ((Scheme.Modules.pullback U.ι ⋙ H).map i) :=
    mono_of_retraction _ _ hrV
  let eV : Scheme.Modules.pullback U.ι ⋙ H ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback V.ι :=
    Scheme.Modules.pullbackComp (f ∣_ U) U.ι ≪≫
      Scheme.Modules.pullbackCongr (morphismRestrict_ι f U) ≪≫
      (Scheme.Modules.pullbackComp V.ι f).symm
  exact ⟨V, hxU, mono_map_of_iso eV i⟩

/-- Exact pullback of the actual sequence follows from the proved left
monomorphism and the ordinary right exactness of the pullback functor. -/
theorem pullback_shortExact_of_locallyFiniteFree_quotient
    {X Y : Scheme.{0}} (f : X ⟶ Y) {E F G : OModule Y}
    (i : E ⟶ F) (q : F ⟶ G) (hz : i ≫ q = 0)
    (hex : (ShortComplex.mk i q hz).ShortExact) (hG : LocallyFiniteFree G) :
    ((ShortComplex.mk i q hz).map (Scheme.Modules.pullback f)).ShortExact := by
  let H := Scheme.Modules.pullback f
  letI : H.IsLeftAdjoint := (Scheme.Modules.pullbackPushforwardAdjunction f).isLeftAdjoint
  letI : Epi q := hex.epi_g
  exact
    { mono_f := pullback_mono_of_locallyFiniteFree_quotient f i q hz hex hG
      epi_g := by change Epi (H.map q); infer_instance
      exact := hex.exact.map_of_epi_of_preservesCokernel H hex.epi_g inferInstance }

/-- Project bundle specialization; all maps are the originals. -/
theorem vectorBundle_pullback_shortExact
    {X Y : Scheme.{0}} (f : X ⟶ Y) {a b c : ℕ}
    (E : AlgebraicVectorBundle Y a) (F : AlgebraicVectorBundle Y b)
    (G : AlgebraicVectorBundle Y c)
    (i : E.sheaf ⟶ F.sheaf) (q : F.sheaf ⟶ G.sheaf)
    (hz : i ≫ q = 0) (hex : (ShortComplex.mk i q hz).ShortExact) :
    ((ShortComplex.mk i q hz).map (Scheme.Modules.pullback f)).ShortExact :=
  pullback_shortExact_of_locallyFiniteFree_quotient f i q hz hex
    (locallyFiniteFree_of_rank G.locallyFree)

end LeBrunSalamon.VectorBundlePullback
