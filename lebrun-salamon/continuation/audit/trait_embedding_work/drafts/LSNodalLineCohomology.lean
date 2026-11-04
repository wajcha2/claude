import RecompileExtensionsPart04Nodes
import LSFirstCohomologyIso

/-! Actual Yoneda H¹ vanishing on a pushout of two branches.
The correction and represented-section gluing proofs are generalized from
our existing checked normalization arguments; no normal-form assumption
and no new admitted theorem are introduced. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.Construction.Normalization
open LeBrunSalamon.Construction.Normalization.NodeCohomology

namespace LeBrunSalamon.NodalLineCohomology

namespace GlueProof

/-- Equality after the two canonical node comparisons gives equality of the
corresponding maps to the same total bundle. -/
theorem node_maps_eq {Y A B N : Scheme} {r : ℕ}
    {E : AlgebraicVectorBundle Y r} (V : TotalBundle E)
    (f₁ : A ⟶ Y) (f₂ : B ⟶ Y) (p₁ : N ⟶ A) (p₂ : N ⟶ B)
    (z : N ⟶ Y) (h₁ : p₁ ≫ f₁ = z) (h₂ : p₂ ≫ f₂ = z)
    (a : AlgebraicSection (pullbackModule f₁ E.sheaf))
    (b : AlgebraicSection (pullbackModule f₂ E.sheaf))
    (h : pullSection p₁ a ≫ (compositionPullback p₁ f₁ z h₁ E.sheaf).hom =
      pullSection p₂ b ≫ (compositionPullback p₂ f₂ z h₂ E.sheaf).hom) :
    p₁ ≫ (V.mapOfSection f₁ a).val = p₂ ≫ (V.mapOfSection f₂ b).val := by
  exact (V.mapOfSection_naturality f₁ p₁ z h₁ a).trans
    ((congrArg (fun t : AlgebraicSection (pullbackModule z E.sheaf) =>
      (V.mapOfSection z t).val) h).trans
      (V.mapOfSection_naturality f₂ p₂ z h₂ b).symm)

/-- The projection of a glued map is the identity when its two specified
factors lie over the original branch maps. -/
theorem projection_eq_id {Y A B T : Scheme}
    (f₁ : A ⟶ Y) (f₂ : B ⟶ Y)
    (hext : ∀ (u v : Y ⟶ Y), f₁ ≫ u = f₁ ≫ v →
      f₂ ≫ u = f₂ ≫ v → u = v)
    (p : T ⟶ Y) (l : A ⟶ T) (r : B ⟶ T)
    (hl : l ≫ p = f₁) (hr : r ≫ p = f₂)
    (g : Y ⟶ T) (hgl : f₁ ≫ g = l) (hgr : f₂ ≫ g = r) :
    g ≫ p = 𝟙 Y := by
  refine hext (g ≫ p) (𝟙 Y) ?_ ?_
  · exact (Category.assoc f₁ g p).symm.trans
      ((congrArg (fun k : A ⟶ T => k ≫ p) hgl).trans
        (hl.trans (Category.comp_id f₁).symm))
  · exact (Category.assoc f₂ g p).symm.trans
      ((congrArg (fun k : B ⟶ T => k ≫ p) hgr).trans
        (hr.trans (Category.comp_id f₂).symm))

/-- Normalizing the represented section along the identity retains the
same map to the total bundle. -/
theorem represented_global_graph {Y : Scheme} {r : ℕ}
    {E : AlgebraicVectorBundle Y r} (V : TotalBundle E)
    (g : Y ⟶ V.space) (hg : g ≫ V.projection = 𝟙 Y) :
    (V.mapOfSection (𝟙 Y) (pullSection (𝟙 Y)
      (V.representedSection (𝟙 Y) g hg ≫
        (Scheme.Modules.pullbackId Y).hom.app E.sheaf))).val = g := by
  let c := V.representedSection (𝟙 Y) g hg
  let s := c ≫ (Scheme.Modules.pullbackId Y).hom.app E.sheaf
  have hc : c = pullSection (𝟙 Y) s := by
    apply (cancel_mono ((Scheme.Modules.pullbackId Y).hom.app E.sheaf)).mp
    exact (LeBrunSalamon.PhaseTwentyEight.ExternalExchangeCoherenceProof.pullSection_id s).symm
  exact (congrArg (fun t : AlgebraicSection (pullbackModule (𝟙 Y) E.sheaf) =>
    (V.mapOfSection (𝟙 Y) t).val) hc).symm.trans
    (V.mapOfSection_representedSection (𝟙 Y) g hg)

/-- A specified factorization of the total-space map gives the actual
pullback value of its normalized global section. -/
theorem section_eq_of_graph_factor {T Y : Scheme} {r : ℕ}
    {E : AlgebraicVectorBundle Y r} (V : TotalBundle E)
    (s : AlgebraicSection E.sheaf) (g : Y ⟶ V.space)
    (hs : (V.mapOfSection (𝟙 Y) (pullSection (𝟙 Y) s)).val = g)
    (f : T ⟶ Y) (a : AlgebraicSection (pullbackModule f E.sheaf))
    (hf : f ≫ g = (V.mapOfSection f a).val) : pullSection f s = a := by
  apply V.mapOfSection_injective f
  exact ((V.mapOfSection_naturality (𝟙 Y) f f (Category.comp_id f)
    (pullSection (𝟙 Y) s)).trans
    (congrArg (fun t : AlgebraicSection (pullbackModule f E.sheaf) =>
      (V.mapOfSection f t).val)
      (compositionPullback_sections f (𝟙 Y) f (Category.comp_id f) s))).symm.trans
    ((congrArg (fun k : Y ⟶ V.space => f ≫ k) hs).trans hf)

theorem glue_sections_of_pushout {Y A B N : Scheme} {r : ℕ}
    (E : AlgebraicVectorBundle Y r)
    (i₁ : A ⟶ Y) (i₂ : B ⟶ Y) (p₁ : N ⟶ A) (p₂ : N ⟶ B)
    (z : N ⟶ Y) (h₁ : p₁ ≫ i₁ = z) (h₂ : p₂ ≫ i₂ = z)
    (hpush : ∀ (Z : Scheme) (l : A ⟶ Z) (r : B ⟶ Z),
      p₁ ≫ l = p₂ ≫ r → ∃! g : Y ⟶ Z, i₁ ≫ g = l ∧ i₂ ≫ g = r)
    (hext : ∀ (u v : Y ⟶ Y), i₁ ≫ u = i₁ ≫ v →
      i₂ ≫ u = i₂ ≫ v → u = v)
    (a : AlgebraicSection (pullbackModule i₁ E.sheaf))
    (b : AlgebraicSection (pullbackModule i₂ E.sheaf))
    (h : pullSection p₁ a ≫ (compositionPullback p₁ i₁ z h₁ E.sheaf).hom =
      pullSection p₂ b ≫ (compositionPullback p₂ i₂ z h₂ E.sheaf).hom) :
    ∃ s : AlgebraicSection E.sheaf,
      pullSection i₁ s = a ∧ pullSection i₂ s = b := by
  obtain ⟨V⟩ := totalBundle_exists E
  let l := V.mapOfSection i₁ a
  let r := V.mapOfSection i₂ b
  have hn : p₁ ≫ l.val = p₂ ≫ r.val :=
    node_maps_eq V i₁ i₂ p₁ p₂ z h₁ h₂ a b h
  obtain ⟨g, hg, _⟩ := hpush V.space l.val r.val hn
  have ho : g ≫ V.projection = 𝟙 Y :=
    projection_eq_id i₁ i₂ hext V.projection
      l.val r.val l.property r.property g hg.1 hg.2
  let c := V.representedSection (𝟙 Y) g ho
  let s := c ≫ (Scheme.Modules.pullbackId Y).hom.app E.sheaf
  have hs : (V.mapOfSection (𝟙 Y) (pullSection (𝟙 Y) s)).val = g :=
    represented_global_graph V g ho
  exact ⟨s,
    section_eq_of_graph_factor V s g hs i₁ a hg.1,
    section_eq_of_graph_factor V s g hs i₂ b hg.2⟩

end GlueProof

namespace NodeCorrectionProof

/-- Subtraction commutes with the prescribed normalized pullback. -/
theorem normalized_sub {N A Y : Scheme}
    (p : N ⟶ A) (f : A ⟶ Y) (z : N ⟶ Y) (h : p ≫ f = z)
    (M : OModule Y) (a b : AlgebraicSection (pullbackModule f M)) :
    pullSection p (a - b) ≫ (compositionPullback p f z h M).hom =
      (pullSection p a ≫ (compositionPullback p f z h M).hom) -
        (pullSection p b ≫ (compositionPullback p f z h M).hom) := by
  exact (congrArg (fun c : AlgebraicSection (pullbackModule p (pullbackModule f M)) =>
      c ≫ (compositionPullback p f z h M).hom)
    (BundleGluing.pullSection_sub p a b)).trans
      (Preadditive.sub_comp (pullSection p a) (pullSection p b)
        (compositionPullback p f z h M).hom)

/-- The actual sheaf map commutes with the prescribed normalized pullback. -/
theorem normalized_map {N A Y : Scheme}
    (p : N ⟶ A) (f : A ⟶ Y) (z : N ⟶ Y) (h : p ≫ f = z)
    {E M : OModule Y} (i : E ⟶ M)
    (a : AlgebraicSection (pullbackModule f E)) :
    pullSection p (a ≫ (Scheme.Modules.pullback f).map i) ≫
        (compositionPullback p f z h M).hom =
      (pullSection p a ≫ (compositionPullback p f z h E).hom) ≫
        (Scheme.Modules.pullback z).map i := by
  calc
    _ = (pullSection p a ≫
          (Scheme.Modules.pullback p).map ((Scheme.Modules.pullback f).map i)) ≫
            (compositionPullback p f z h M).hom :=
      congrArg (fun b : AlgebraicSection (pullbackModule p (pullbackModule f M)) =>
        b ≫ (compositionPullback p f z h M).hom)
        (pullSection_naturality p a ((Scheme.Modules.pullback f).map i))
    _ = pullSection p a ≫
          ((Scheme.Modules.pullback p).map ((Scheme.Modules.pullback f).map i) ≫
            (compositionPullback p f z h M).hom) :=
      Category.assoc _ _ _
    _ = pullSection p a ≫
          ((compositionPullback p f z h E).hom ≫ (Scheme.Modules.pullback z).map i) :=
      congrArg (fun b : pullbackModule p (pullbackModule f E) ⟶ pullbackModule z M =>
        pullSection p a ≫ b)
        (BundleGluing.compositionPullback_naturality p f z h i)
    _ = _ := (Category.assoc _ _ _).symm

/-- Correct two actual branch lifts on abstract schemes. In particular,
the kernel lift and its correction are checked without unfolding a central fibre. -/
theorem corrected_left {Y A B N : Scheme}
    (fL : A ⟶ Y) (fR : B ⟶ Y) (pL : N ⟶ A) (pR : N ⟶ B)
    (z : N ⟶ Y) (hLnode : pL ≫ fL = z) (hRnode : pR ≫ fR = z)
    {E M : OModule Y} (i : E ⟶ M) (q : M ⟶ structureModule Y)
    (hz : i ≫ q = 0)
    (hN : (ShortComplex.mk ((Scheme.Modules.pullback z).map i)
      (quotientPullback z q) (pullback_zero z i q hz)).ShortExact)
    (hnode : Function.Surjective (fun a : AlgebraicSection (pullbackModule fL E) =>
      pullSection pL a ≫ (compositionPullback pL fL z hLnode E).hom))
    (sL : AlgebraicSection (pullbackModule fL M))
    (sR : AlgebraicSection (pullbackModule fR M))
    (hsL : sL ≫ quotientPullback fL q = 𝟙 (structureModule A))
    (hsR : sR ≫ quotientPullback fR q = 𝟙 (structureModule B)) :
    ∃ v : AlgebraicSection (pullbackModule fL E),
      (sL - v ≫ (Scheme.Modules.pullback fL).map i) ≫
          quotientPullback fL q = 𝟙 (structureModule A) ∧
        pullSection pL (sL - v ≫ (Scheme.Modules.pullback fL).map i) ≫
            (compositionPullback pL fL z hLnode M).hom =
          pullSection pR sR ≫ (compositionPullback pR fR z hRnode M).hom := by
  let iL : pullbackModule fL E ⟶ pullbackModule fL M :=
    (Scheme.Modules.pullback fL).map i
  let iN : pullbackModule z E ⟶ pullbackModule z M :=
    (Scheme.Modules.pullback z).map i
  let qL : pullbackModule fL M ⟶ structureModule A := quotientPullback fL q
  let qN : pullbackModule z M ⟶ structureModule N := quotientPullback z q
  have hzL : iL ≫ qL = 0 := pullback_zero fL i q hz
  let bL : AlgebraicSection (pullbackModule z M) :=
    pullSection pL sL ≫ (compositionPullback pL fL z hLnode M).hom
  let bR : AlgebraicSection (pullbackModule z M) :=
    pullSection pR sR ≫ (compositionPullback pR fR z hRnode M).hom
  have hbL : bL ≫ qN = 𝟙 (structureModule N) :=
    lift_preserved pL fL z hLnode q sL hsL
  have hbR : bR ≫ qN = 𝟙 (structureModule N) :=
    lift_preserved pR fR z hRnode q sR hsR
  have hb : (bL - bR) ≫ qN = 0 :=
    (Preadditive.sub_comp bL bR qN).trans
      ((congrArg₂ (fun a b : AlgebraicSection (structureModule N) => a - b)
        hbL hbR).trans (sub_self (𝟙 (structureModule N))))
  letI : Mono iN := hN.mono_f
  let c : AlgebraicSection (pullbackModule z E) :=
    hN.exact.lift (bL - bR) hb
  have hc : c ≫ iN = bL - bR := hN.exact.lift_f (bL - bR) hb
  obtain ⟨v, hv⟩ := hnode c
  let sL' : AlgebraicSection (pullbackModule fL M) := sL - v ≫ iL
  have hcorrection : (v ≫ iL) ≫ qL = 0 :=
    (Category.assoc v iL qL).trans
      ((congrArg (fun a : pullbackModule fL E ⟶ structureModule A => v ≫ a)
        hzL).trans comp_zero)
  have hsL' : sL' ≫ qL = 𝟙 (structureModule A) :=
    (Preadditive.sub_comp sL (v ≫ iL) qL).trans
      ((congrArg₂ (fun a b : AlgebraicSection (structureModule A) => a - b)
        hsL hcorrection).trans (sub_zero (𝟙 (structureModule A))))
  have hcorrection_node :
      pullSection pL (v ≫ iL) ≫ (compositionPullback pL fL z hLnode M).hom =
        bL - bR :=
    (normalized_map pL fL z hLnode i v).trans
      ((congrArg (fun a : AlgebraicSection (pullbackModule z E) => a ≫ iN) hv).trans hc)
  have hmatch :
      pullSection pL sL' ≫ (compositionPullback pL fL z hLnode M).hom = bR :=
    (normalized_sub pL fL z hLnode M sL (v ≫ iL)).trans
      ((congrArg (fun a : AlgebraicSection (pullbackModule z M) => bL - a)
        hcorrection_node).trans (sub_sub_self bL bR))
  exact ⟨v, hsL', hmatch⟩

end NodeCorrectionProof

/-- The universal property of the actual scheme pushout, in the form
used by the represented-section gluing construction. -/
theorem pushout_universal {Y A B N : Scheme}
    {i₁ : A ⟶ Y} {i₂ : B ⟶ Y} {p₁ : N ⟶ A} {p₂ : N ⟶ B}
    (hpush : IsPushout p₁ p₂ i₁ i₂)
    (Z : Scheme) (l : A ⟶ Z) (r : B ⟶ Z) (h : p₁ ≫ l = p₂ ≫ r) :
    ∃! g : Y ⟶ Z, i₁ ≫ g = l ∧ i₂ ≫ g = r := by
  refine ⟨hpush.desc l r h, ⟨hpush.inl_desc _ _ _, hpush.inr_desc _ _ _⟩, ?_⟩
  intro k hk
  apply hpush.hom_ext
  · exact hk.1.trans (hpush.inl_desc _ _ _).symm
  · exact hk.2.trans (hpush.inr_desc _ _ _).symm

/-- Actual branch pullbacks detect equality of global bundle sections. -/
theorem sections_ext_of_pushout {Y A B N : Scheme} {r : ℕ}
    (E : AlgebraicVectorBundle Y r)
    {i₁ : A ⟶ Y} {i₂ : B ⟶ Y} {p₁ : N ⟶ A} {p₂ : N ⟶ B}
    (hpush : IsPushout p₁ p₂ i₁ i₂)
    {a b : AlgebraicSection E.sheaf}
    (h₁ : pullSection i₁ a = pullSection i₁ b)
    (h₂ : pullSection i₂ a = pullSection i₂ b) : a = b := by
  obtain ⟨V⟩ := totalBundle_exists E
  have hm : (V.mapOfSection (𝟙 Y) (pullSection (𝟙 Y) a)).val =
      (V.mapOfSection (𝟙 Y) (pullSection (𝟙 Y) b)).val := by
    apply hpush.hom_ext
    · rw [V.mapOfSection_naturality (𝟙 Y) i₁ i₁ (Category.comp_id _) (pullSection (𝟙 Y) a),
        V.mapOfSection_naturality (𝟙 Y) i₁ i₁ (Category.comp_id _) (pullSection (𝟙 Y) b),
        compositionPullback_sections, compositionPullback_sections, h₁]
    · rw [V.mapOfSection_naturality (𝟙 Y) i₂ i₂ (Category.comp_id _) (pullSection (𝟙 Y) a),
        V.mapOfSection_naturality (𝟙 Y) i₂ i₂ (Category.comp_id _) (pullSection (𝟙 Y) b),
        compositionPullback_sections, compositionPullback_sections, h₂]
  have hs := V.mapOfSection_injective (𝟙 Y) hm
  have h := congrArg (fun s => s ≫ (Scheme.Modules.pullbackId Y).hom.app E.sheaf) hs
  exact (ExternalExchangeCoherenceProof.pullSection_id a).symm.trans
    (h.trans (ExternalExchangeCoherenceProof.pullSection_id b))

/-- Split on each branch, correct the difference at the node, and glue
through the actual pushout. This proves the original Yoneda predicate. -/
theorem of_pushout {Y A B N : Scheme} {r : ℕ}
    (E : AlgebraicVectorBundle Y r)
    (i₁ : A ⟶ Y) (i₂ : B ⟶ Y) (p₁ : N ⟶ A) (p₂ : N ⟶ B)
    (hpush : IsPushout p₁ p₂ i₁ i₂)
    (h₁ : HasVanishingFirstCohomology (pullbackModule i₁ E.sheaf))
    (h₂ : HasVanishingFirstCohomology (pullbackModule i₂ E.sheaf))
    (hnode : Function.Surjective (fun a : AlgebraicSection (pullbackModule i₁ E.sheaf) =>
      pullSection p₁ a ≫ (compositionPullback p₁ i₁ (p₁ ≫ i₁) rfl E.sheaf).hom)) :
    HasVanishingFirstCohomology E.sheaf := by
  intro M i q hz hex
  let M' : AlgebraicVectorBundle Y (r + 1) :=
    ⟨M, LocalExtensionSplitting.middle_locallyFree E.locallyFree i q hz hex⟩
  have hEL := pullback_shortExact i₁ E M' i q hz hex
  have hER := pullback_shortExact i₂ E M' i q hz hex
  obtain ⟨sL, hsL⟩ := h₁ (pullbackModule i₁ M)
    ((Scheme.Modules.pullback i₁).map i) (quotientPullback i₁ q)
    (pullback_zero i₁ i q hz) hEL
  obtain ⟨sR, hsR⟩ := h₂ (pullbackModule i₂ M)
    ((Scheme.Modules.pullback i₂).map i) (quotientPullback i₂ q)
    (pullback_zero i₂ i q hz) hER
  have hN := pullback_shortExact (p₁ ≫ i₁) E M' i q hz hex
  obtain ⟨v, hv, hmatch⟩ := NodeCorrectionProof.corrected_left
    i₁ i₂ p₁ p₂ (p₁ ≫ i₁) rfl hpush.w.symm i q hz hN hnode sL sR hsL hsR
  let sL' : AlgebraicSection (pullbackModule i₁ M) :=
    sL - v ≫ (Scheme.Modules.pullback i₁).map i
  obtain ⟨s, hsl, hsr⟩ := GlueProof.glue_sections_of_pushout M'
    i₁ i₂ p₁ p₂ (p₁ ≫ i₁) rfl hpush.w.symm
    (pushout_universal hpush) (fun _ _ hl hr => hpush.hom_ext hl hr) sL' sR hmatch
  refine ⟨s, sections_ext_of_pushout (trivialLine Y) hpush ?_ ?_⟩
  · exact of_branches_quotient_restriction i₁ q s sL' hsl hv
  · exact of_branches_quotient_restriction i₂ q s sR hsr hsR

/-- Evaluation on a globally generated P¹ branch is surjective at the
specified actual complex point, with its original composition map. -/
theorem node_surjective (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {Y : Scheme} (i : ProjectiveLine ⟶ Y) (E : OModule Y)
    (hE : IsGloballyGenerated (pullbackModule i E)) :
    Function.Surjective (fun a : AlgebraicSection (pullbackModule i E) =>
      pullSection p.map a ≫ (compositionPullback p.map i (p.map ≫ i) rfl E).hom) := by
  intro v
  let e := compositionPullback p.map i (p.map ≫ i) rfl E
  let w := v ≫ e.inv
  obtain ⟨a, ha⟩ := GeneratedFiberEvaluation.evaluateSection_surjective_of_globallyGenerated
    P.structureMap (pullbackModule i E) p.map p.overC hE (sectionValue w)
  have hs : pullSection p.map (sectionFromValue a) = w := by
    apply (sectionValue_bijective _).injective
    exact ha
  refine ⟨sectionFromValue a, ?_⟩
  change pullSection p.map (sectionFromValue a) ≫ e.hom = v
  exact (congrArg (fun t : AlgebraicSection (pullbackModule p.map (pullbackModule i E)) =>
    t ≫ e.hom) hs).trans (by
      change (v ≫ e.inv) ≫ e.hom = v
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- In particular a line of degrees at least (0,-1) on the two rational
branches has H¹=0. Degree (1,1) satisfies these hypotheses. -/
theorem line_of_degrees (P : ProjectiveLineOverC)
    (mark p q : ProjectiveLinePoint P) {Y : Scheme.{0}}
    (i j : ProjectiveLine ⟶ Y) (hpush : IsPushout p.map q.map i j)
    (L : LineBundle Y)
    (hi : 0 ≤ projectiveLineDegree P mark (pullbackLine i L))
    (hj : -1 ≤ projectiveLineDegree P mark (pullbackLine j L)) :
    HasVanishingFirstCohomology L.sheaf := by
  apply of_pushout L i j p.map q.map hpush
  · exact FirstCohomology.line_of_degree P mark (pullbackLine i L) (by omega)
  · exact FirstCohomology.line_of_degree P mark (pullbackLine j L) hj
  · apply node_surjective P p i L.sheaf
    obtain ⟨e⟩ := projectiveLineDegree_spec P mark (pullbackLine i L)
    exact (DirectSumGeometry.globallyGenerated_iso_iff e).mpr
      ((P1TwistGeneration.globallyGenerated_iff P mark _).mpr hi)

end LeBrunSalamon.NodalLineCohomology
end
