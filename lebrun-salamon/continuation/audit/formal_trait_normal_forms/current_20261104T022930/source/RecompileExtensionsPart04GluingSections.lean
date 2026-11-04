import RecompileExtensionsPart04Gluing

noncomputable section

set_option autoImplicit false
open Bundle
open scoped Bundle ContDiff ENNReal
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing
open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.Limits

namespace LeBrunSalamon.Construction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseSeven
open LeBrunSalamon.PhaseEight LeBrunSalamon.PhaseTen
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFour LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton

namespace Normalization
open Lines Smoothing

namespace BundleGluing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A global bundle section is determined by its actual branch pullbacks. -/
theorem sections_ext {F : StandardSource} (m : SourceMarks F) {r : ℕ}
    (E : AlgebraicVectorBundle (CentralFiber F) r)
    {a b : AlgebraicSection E.sheaf}
    (hl : pullSection (leftBranch m) a = pullSection (leftBranch m) b)
    (hr : pullSection (rightBranch m) a = pullSection (rightBranch m) b) : a = b := by
  obtain ⟨V⟩ := totalBundle_exists E
  have hm : (V.mapOfSection (𝟙 (CentralFiber F))
      (pullSection (𝟙 (CentralFiber F)) a)).val =
      (V.mapOfSection (𝟙 (CentralFiber F))
      (pullSection (𝟙 (CentralFiber F)) b)).val := by
    apply centralFiber_hom_ext m
    · rw [V.mapOfSection_naturality (𝟙 (CentralFiber F)) (leftBranch m)
        (leftBranch m) (Category.comp_id _) (pullSection (𝟙 (CentralFiber F)) a),
        V.mapOfSection_naturality (𝟙 (CentralFiber F)) (leftBranch m)
        (leftBranch m) (Category.comp_id _) (pullSection (𝟙 (CentralFiber F)) b),
        compositionPullback_sections, compositionPullback_sections, hl]
    · rw [V.mapOfSection_naturality (𝟙 (CentralFiber F)) (rightBranch m)
        (rightBranch m) (Category.comp_id _) (pullSection (𝟙 (CentralFiber F)) a),
        V.mapOfSection_naturality (𝟙 (CentralFiber F)) (rightBranch m)
        (rightBranch m) (Category.comp_id _) (pullSection (𝟙 (CentralFiber F)) b),
        compositionPullback_sections, compositionPullback_sections, hr]
  have hs := V.mapOfSection_injective (𝟙 (CentralFiber F)) hm
  have h := congrArg (fun s => s ≫
    (Scheme.Modules.pullbackId (CentralFiber F)).hom.app E.sheaf) hs
  exact (LeBrunSalamon.PhaseTwentyEight.ExternalExchangeCoherenceProof.pullSection_id a).symm.trans
    (h.trans (LeBrunSalamon.PhaseTwentyEight.ExternalExchangeCoherenceProof.pullSection_id b))

namespace GlueProof

/-- Equality after the two canonical node comparisons gives equality of the
corresponding maps to the same total bundle. -/
private theorem node_maps_eq {Y A B N : Scheme} {r : ℕ}
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
private theorem projection_eq_id {Y A B T : Scheme}
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
private theorem represented_global_graph {Y : Scheme} {r : ℕ}
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
private theorem section_eq_of_graph_factor {T Y : Scheme} {r : ℕ}
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

private theorem glue_sections_of_pushout {Y A B N : Scheme} {r : ℕ}
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

/-- Transport through the named generic node operation, then unfold it only
inside the proof over abstract schemes. -/
private theorem glue_sections_with_node_maps {Y A B N : Scheme} {r : ℕ}
    (E : AlgebraicVectorBundle Y r)
    (i₁ : A ⟶ Y) (i₂ : B ⟶ Y) (p₁ : N ⟶ A) (p₂ : N ⟶ B)
    (z : N ⟶ Y) (h₁ : p₁ ≫ i₁ = z) (h₂ : p₂ ≫ i₂ = z)
    (hpush : ∀ (Z : Scheme) (l : A ⟶ Z) (r : B ⟶ Z),
      p₁ ≫ l = p₂ ≫ r → ∃! g : Y ⟶ Z, i₁ ≫ g = l ∧ i₂ ≫ g = r)
    (hext : ∀ (u v : Y ⟶ Y), i₁ ≫ u = i₁ ≫ v →
      i₂ ≫ u = i₂ ≫ v → u = v)
    (lAt : AlgebraicSection (pullbackModule i₁ E.sheaf) →
      AlgebraicSection (pullbackModule z E.sheaf))
    (rAt : AlgebraicSection (pullbackModule i₂ E.sheaf) →
      AlgebraicSection (pullbackModule z E.sheaf))
    (hlAt : ∀ a, lAt a = nodeEval i₁ p₁ z h₁ E.sheaf a)
    (hrAt : ∀ b, rAt b = nodeEval i₂ p₂ z h₂ E.sheaf b)
    (a : AlgebraicSection (pullbackModule i₁ E.sheaf))
    (b : AlgebraicSection (pullbackModule i₂ E.sheaf))
    (h : lAt a = rAt b) :
    ∃ s : AlgebraicSection E.sheaf,
      pullSection i₁ s = a ∧ pullSection i₂ s = b := by
  simp only [nodeEval] at hlAt hrAt
  exact glue_sections_of_pushout E i₁ i₂ p₁ p₂ z h₁ h₂ hpush hext a b
    ((hlAt a).symm.trans (h.trans (hrAt b)))


end GlueProof

/-- Gluing sections is proved from gluing their maps to the total bundle.
The compatibility is the canonical equality over the actual node. -/
theorem glue_sections {F : StandardSource} (m : SourceMarks F) {r : ℕ}
    (E : AlgebraicVectorBundle (CentralFiber F) r)
    (a : AlgebraicSection (pullbackModule (leftBranch m) E.sheaf))
    (b : AlgebraicSection (pullbackModule (rightBranch m) E.sheaf))
    (h : leftAtNode m E.sheaf a = rightAtNode m E.sheaf b) :
    ∃ s : AlgebraicSection E.sheaf,
      pullSection (leftBranch m) s = a ∧ pullSection (rightBranch m) s = b := by
  exact GlueProof.glue_sections_with_node_maps
    (Y := CentralFiber F) (A := ProjectiveLine) (B := ProjectiveLine)
    (N := ComplexBase) (r := r)
    E (leftBranch m) (rightBranch m) marking.map marking.map
    (node m) rfl (rightBranch_to_node m)
    (centralFiber_pushout m)
    (fun _ _ hl hr => centralFiber_hom_ext m hl hr)
    (leftAtNode m E.sheaf) (rightAtNode m E.sheaf)
    (leftAtNode_explicit m E.sheaf) (rightAtNode_explicit m E.sheaf)
    a b h

theorem pullSection_sub {Y Z : Scheme} (f : Y ⟶ Z) {E : OModule Z}
    (a b : AlgebraicSection E) : pullSection f (a - b) = pullSection f a - pullSection f b := by
  simp only [pullSection, restrictSection, Functor.map_sub, Preadditive.comp_sub]

theorem leftAtNode_sub {F : StandardSource} (m : SourceMarks F)
    (E : OModule (CentralFiber F))
    (a b : AlgebraicSection (pullbackModule (leftBranch m) E)) :
    leftAtNode m E (a - b) = leftAtNode m E a - leftAtNode m E b := by
  simp only [leftAtNode, pullSection_sub, Preadditive.sub_comp]

/-- The comparison is natural for the actual sheaf map. -/
theorem compositionPullback_naturality {T Y Z : Scheme}
    (g : T ⟶ Y) (f : Y ⟶ Z) (k : T ⟶ Z) (hk : g ≫ f = k)
    {E M : OModule Z} (i : E ⟶ M) :
    (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback f).map i) ≫
        (compositionPullback g f k hk M).hom =
      (compositionPullback g f k hk E).hom ≫ (Scheme.Modules.pullback k).map i := by
  subst k
  simpa only [compositionPullback, Iso.trans_hom, Iso.app_hom, eqToIso.hom,
    eqToHom_refl, Category.comp_id, Functor.comp_map] using
    (Scheme.Modules.pullbackComp g f).hom.naturality i

theorem leftAtNode_map {F : StandardSource} (m : SourceMarks F)
    {E M : OModule (CentralFiber F)} (i : E ⟶ M)
    (a : AlgebraicSection (pullbackModule (leftBranch m) E)) :
    leftAtNode m M (a ≫ (Scheme.Modules.pullback (leftBranch m)).map i) =
      leftAtNode m E a ≫ (Scheme.Modules.pullback (node m)).map i := by
  rw [leftAtNode, pullSection_naturality, Category.assoc,
    compositionPullback_naturality marking.map (leftBranch m) (node m) rfl i,
    ← Category.assoc]
  rfl

end BundleGluing

end Normalization
end LeBrunSalamon.Construction
end
