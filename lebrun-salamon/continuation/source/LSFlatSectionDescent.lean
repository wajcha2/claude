import RecompileExtensionsPart04
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Descent of actual vector-bundle sections along flat covers

Mathlib proves that a surjective flat morphism locally of finite
presentation is an effective epimorphism of schemes.  The existing total
bundle represents sections on all test schemes.  Descending its actual
representing map therefore descends a compatible section, with the
specified pullback-square comparison.  This file adds no admitted input.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Refinement
open LeBrunSalamon.PhaseTwentyEight.ExternalExchangeCoherenceProof
open LeBrunSalamon.Construction.Normalization

namespace LeBrunSalamon.Construction.FlatSectionDescent

/-- The actual square comparison followed by its second composition
comparison is its first composition comparison. -/
theorem squareIso_comp_composition {T Y W Z : Scheme}
    (a : T ⟶ Y) (b : Y ⟶ Z) (c : T ⟶ W) (d : W ⟶ Z)
    (h : a ≫ b = c ≫ d) (E : OModule Z) :
    (pullbackSquareIso a b c d h E).hom ≫
        (compositionPullback c d (c ≫ d) rfl E).hom =
      (compositionPullback a b (c ≫ d) h E).hom := by
  simp [pullbackSquareIso, compositionPullback, Category.assoc]

namespace Represented

variable {Y : Scheme} {r : ℕ} {E : AlgebraicVectorBundle Y r}
    (V : TotalBundle E)

/-- A global section gives its actual graph in the total vector bundle. -/
def graph (s : AlgebraicSection E.sheaf) : Y ⟶ V.space :=
  (V.mapOfSection (𝟙 Y) (pullSection (𝟙 Y) s)).val

theorem graph_over (s : AlgebraicSection E.sheaf) :
    graph V s ≫ V.projection = 𝟙 Y :=
  (V.mapOfSection (𝟙 Y) (pullSection (𝟙 Y) s)).property

theorem graph_naturality {T : Scheme} (f : T ⟶ Y)
    (s : AlgebraicSection E.sheaf) :
    f ≫ graph V s = (V.mapOfSection f (pullSection f s)).val := by
  simpa only [graph, compositionPullback_sections] using
    V.mapOfSection_naturality (𝟙 Y) f f (Category.comp_id f)
      (pullSection (𝟙 Y) s)

theorem graph_injective : Function.Injective (graph V) := by
  intro s t h
  have hi := V.mapOfSection_injective (𝟙 Y) h
  have hh := congrArg
    (fun a : AlgebraicSection (pullbackModule (𝟙 Y) E.sheaf) =>
      a ≫ (Scheme.Modules.pullbackId Y).hom.app E.sheaf) hi
  exact (LeBrunSalamon.PhaseTwentyEight.ExternalExchangeCoherenceProof.pullSection_id s).symm.trans
    (hh.trans (LeBrunSalamon.PhaseTwentyEight.ExternalExchangeCoherenceProof.pullSection_id t))

/-- The stated section compatibility gives equality of the actual maps
on the scheme-theoretic kernel pair, including nonreduced test schemes. -/
theorem kernelPair {T : Scheme} (f : T ⟶ Y)
    (a : AlgebraicSection (pullbackModule f E.sheaf))
    (ha : pullSection (pullback.fst f f) a ≫
        (pullbackSquareIso (pullback.fst f f) f (pullback.snd f f) f
          pullback.condition E.sheaf).hom =
      pullSection (pullback.snd f f) a) :
    pullback.fst f f ≫ (V.mapOfSection f a).val =
      pullback.snd f f ≫ (V.mapOfSection f a).val := by
  rw [V.mapOfSection_naturality f (pullback.fst f f)
      (pullback.snd f f ≫ f) pullback.condition a,
    V.mapOfSection_naturality f (pullback.snd f f)
      (pullback.snd f f ≫ f) rfl a]
  apply congrArg (fun s => (V.mapOfSection (pullback.snd f f ≫ f) s).val)
  have h := congrArg (fun s => s ≫
    (compositionPullback (pullback.snd f f) f (pullback.snd f f ≫ f)
      rfl E.sheaf).hom) ha
  rw [Category.assoc, squareIso_comp_composition] at h
  exact h

end Represented

/-- Pullback of sections is injective along a scheme epimorphism.  The
proof uses the total bundle, so no reducedness or pointwise criterion is
required. -/
theorem pullSection_injective_of_epi {T Y : Scheme} (f : T ⟶ Y) [Epi f]
    {r : ℕ} (E : AlgebraicVectorBundle Y r) :
    Function.Injective (fun s : AlgebraicSection E.sheaf => pullSection f s) := by
  obtain ⟨V⟩ := totalBundle_exists E
  intro s t h
  apply Represented.graph_injective V
  apply (cancel_epi f).mp
  exact (Represented.graph_naturality V f s).trans
    ((congrArg (fun a : AlgebraicSection (pullbackModule f E.sheaf) =>
      (V.mapOfSection f a).val) h).trans
        (Represented.graph_naturality V f t).symm)

/-- Descent follows from the effective-epimorphism property of the actual
cover and the all-test-scheme universal property of the total bundle. -/
theorem existsUnique_of_effectiveEpi {T Y : Scheme} (f : T ⟶ Y) [EffectiveEpi f]
    {r : ℕ} (E : AlgebraicVectorBundle Y r)
    (a : AlgebraicSection (pullbackModule f E.sheaf))
    (ha : pullSection (pullback.fst f f) a ≫
        (pullbackSquareIso (pullback.fst f f) f (pullback.snd f f) f
          pullback.condition E.sheaf).hom =
      pullSection (pullback.snd f f) a) :
    ∃! s : AlgebraicSection E.sheaf, pullSection f s = a := by
  obtain ⟨V⟩ := totalBundle_exists E
  let e : T ⟶ V.space := (V.mapOfSection f a).val
  have hp : pullback.fst f f ≫ e = pullback.snd f f ≫ e :=
    Represented.kernelPair V f a ha
  have hrel : ∀ {W : Scheme} (g₁ g₂ : W ⟶ T),
      g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e := by
    intro W g₁ g₂ hg
    have h := congrArg (fun k => pullback.lift g₁ g₂ hg ≫ k) hp
    simpa only [← Category.assoc, pullback.lift_fst, pullback.lift_snd] using h
  let g : Y ⟶ V.space := EffectiveEpi.desc f e hrel
  have hg : f ≫ g = e := EffectiveEpi.fac f e hrel
  have ho : g ≫ V.projection = 𝟙 Y := by
    apply (cancel_epi f).mp
    rw [← Category.assoc, hg, Category.comp_id]
    exact (V.mapOfSection f a).property
  let c : AlgebraicSection (pullbackModule (𝟙 Y) E.sheaf) :=
    V.representedSection (𝟙 Y) g ho
  let s : AlgebraicSection E.sheaf :=
    c ≫ (Scheme.Modules.pullbackId Y).hom.app E.sheaf
  have hc : c = pullSection (𝟙 Y) s := by
    apply (cancel_mono ((Scheme.Modules.pullbackId Y).hom.app E.sheaf)).mp
    exact (LeBrunSalamon.PhaseTwentyEight.ExternalExchangeCoherenceProof.pullSection_id s).symm
  have hs : Represented.graph V s = g := by
    change (V.mapOfSection (𝟙 Y) (pullSection (𝟙 Y) s)).val = g
    rw [← hc]
    exact V.mapOfSection_representedSection (𝟙 Y) g ho
  have hvalue : pullSection f s = a := by
    apply V.mapOfSection_injective f
    rw [← Represented.graph_naturality, hs]
    exact hg
  refine ⟨s, hvalue, ?_⟩
  intro t ht
  exact pullSection_injective_of_epi f E (ht.trans hvalue.symm)

/-- Actual pullbacks always satisfy the specified kernel-pair equation. -/
theorem pullSection_compatible {T Y : Scheme} (f : T ⟶ Y)
    {r : ℕ} (E : AlgebraicVectorBundle Y r) (s : AlgebraicSection E.sheaf) :
    pullSection (pullback.fst f f) (pullSection f s) ≫
        (pullbackSquareIso (pullback.fst f f) f (pullback.snd f f) f
          pullback.condition E.sheaf).hom =
      pullSection (pullback.snd f f) (pullSection f s) :=
  pullbackSquareIso_onSections (pullback.fst f f) f (pullback.snd f f) f
    pullback.condition s

/-- A surjective flat locally finitely presented morphism gives the
ordinary unique descent of compatible actual bundle sections. -/
theorem existsUnique_fppf {T Y : Scheme} (f : T ⟶ Y)
    [Flat f] [Surjective f] [LocallyOfFinitePresentation f]
    {r : ℕ} (E : AlgebraicVectorBundle Y r)
    (a : AlgebraicSection (pullbackModule f E.sheaf))
    (ha : pullSection (pullback.fst f f) a ≫
        (pullbackSquareIso (pullback.fst f f) f (pullback.snd f f) f
          pullback.condition E.sheaf).hom =
      pullSection (pullback.snd f f) a) :
    ∃! s : AlgebraicSection E.sheaf, pullSection f s = a :=
  existsUnique_of_effectiveEpi f E a ha

/-- The same construction applies to a surjective flat quasi-compact
morphism, using Mathlib's effective epimorphism for an fpqc cover. -/
theorem existsUnique_fpqc {T Y : Scheme} (f : T ⟶ Y)
    [Flat f] [Surjective f] [QuasiCompact f]
    {r : ℕ} (E : AlgebraicVectorBundle Y r)
    (a : AlgebraicSection (pullbackModule f E.sheaf))
    (ha : pullSection (pullback.fst f f) a ≫
        (pullbackSquareIso (pullback.fst f f) f (pullback.snd f f) f
          pullback.condition E.sheaf).hom =
      pullSection (pullback.snd f f) a) :
    ∃! s : AlgebraicSection E.sheaf, pullSection f s = a :=
  existsUnique_of_effectiveEpi f E a ha

theorem pullSection_injective_fppf {T Y : Scheme} (f : T ⟶ Y)
    [Flat f] [Surjective f] [LocallyOfFinitePresentation f]
    {r : ℕ} (E : AlgebraicVectorBundle Y r) :
    Function.Injective (fun s : AlgebraicSection E.sheaf => pullSection f s) :=
  pullSection_injective_of_epi f E

theorem section_eq_of_fppf_pullback {T Y : Scheme} (f : T ⟶ Y)
    [Flat f] [Surjective f] [LocallyOfFinitePresentation f]
    {r : ℕ} (E : AlgebraicVectorBundle Y r) {s t : AlgebraicSection E.sheaf}
    (h : pullSection f s = pullSection f t) : s = t :=
  pullSection_injective_fppf f E h

end LeBrunSalamon.Construction.FlatSectionDescent

end
