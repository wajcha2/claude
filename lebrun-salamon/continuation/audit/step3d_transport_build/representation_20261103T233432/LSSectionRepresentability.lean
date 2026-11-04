import RecompileExtensionsPart02

/-!
The actual section presheaf of a finite locally free sheaf.

EGA IV, quatrième partie, (18.5.1), printed p.125, states precisely that
X' ↦ Γ(X', E_X') with pullback of sections is representable, for a finite
locally free sheaf E on an arbitrary scheme X. The one published input below
is this generic representability statement. The tautological section and the
project's particular composition-pullback formula are obtained by naturality.

Compiler receipts record the exact source and the scope of dependency verification.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton
open LeBrunSalamon.Construction
open LeBrunSalamon.PhaseTwentyEight.ExternalExchangeCoherenceProof

namespace LeBrunSalamon.SectionRepresentability

/-- The actual map on sections for an arrow over the fixed base. -/
def sectionPullback {Z : Scheme.{0}} (E : OModule Z) {T Y : Over Z}
    (f : T ⟶ Y) (s : AlgebraicSection (pullbackModule Y.hom E)) :
    AlgebraicSection (pullbackModule T.hom E) :=
  pullSection f.left s ≫ (compositionPullback f.left Y.hom T.hom f.w E).hom

/-- Evaluation at 1 identifies this actual arrow map with the usual pullback
of global sections through the adjunction unit and the canonical comparison.
Thus the Hom-from-unit notation is the same section functor as in EGA. -/
theorem sectionPullback_value {Z : Scheme.{0}} (E : OModule Z) {T Y : Over Z}
    (f : T ⟶ Y) (s : AlgebraicSection (pullbackModule Y.hom E)) :
    sectionValue (sectionPullback E f s) =
      (compositionPullback f.left Y.hom T.hom f.w E).hom.app ⊤
        (((Scheme.Modules.pullbackPushforwardAdjunction f.left).unit.app
          (pullbackModule Y.hom E)).app ⊤ (sectionValue s)) := by
  rw [sectionPullback, sectionValue_comp, pullSection_value]

/-- Coherence uses the actual pullback pseudofunctor, including equality
transport for each triangle in the category of schemes over Z. -/
theorem compositionPullback_assoc {T Y W Z : Scheme.{0}}
    (f : T ⟶ Y) (g : Y ⟶ W) (h : W ⟶ Z)
    (k : Y ⟶ Z) (l : T ⟶ Z) (hg : g ≫ h = k) (hf : f ≫ k = l)
    (hfg : (f ≫ g) ≫ h = l) (E : OModule Z) :
    (Scheme.Modules.pullback f).map (compositionPullback g h k hg E).hom ≫
      (compositionPullback f k l hf E).hom =
    (Scheme.Modules.pullbackComp f g).hom.app (pullbackModule h E) ≫
      (compositionPullback (f ≫ g) h l hfg E).hom := by
  subst k
  subst l
  simpa only [compositionPullback, Iso.trans_hom, Iso.app_hom,
    eqToIso.hom, eqToHom_refl, Category.comp_id] using
    projection_pullbackComp_assoc f g h E

@[simp]
theorem sectionPullback_id {Z : Scheme.{0}} (E : OModule Z) (T : Over Z)
    (s : AlgebraicSection (pullbackModule T.hom E)) :
    sectionPullback E (𝟙 T) s = s := by
  change pullSection (𝟙 T.left) s ≫
    ((Scheme.Modules.pullbackComp (𝟙 T.left) T.hom).hom.app E ≫
      (Scheme.Modules.pullbackCongr (Category.id_comp T.hom)).hom.app E) = s
  rw [projection_pullbackComp_eq_id (𝟙 T.left) rfl T.hom (Category.id_comp T.hom)]
  simpa only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_refl,
    NatTrans.id_app, Category.id_comp] using pullSection_id s

@[simp]
theorem sectionPullback_comp {Z : Scheme.{0}} (E : OModule Z)
    {T Y W : Over Z} (f : T ⟶ Y) (g : Y ⟶ W)
    (s : AlgebraicSection (pullbackModule W.hom E)) :
    sectionPullback E f (sectionPullback E g s) = sectionPullback E (f ≫ g) s := by
  dsimp only [sectionPullback]
  rw [pullSection_map]
  simp only [Category.assoc]
  rw [compositionPullback_assoc f.left g.left W.hom Y.hom T.hom g.w f.w
    (f ≫ g).w E]
  rw [← Category.assoc, Construction.pullSection_comp]
  rfl

/-- The genuine contravariant section functor, not an arbitrary functor with
isomorphic object values. Its arrow maps are the original pullbacks. -/
def sectionFunctor {Z : Scheme.{0}} (E : OModule Z) : (Over Z)ᵒᵖ ⥤ Type _ where
  obj T := AlgebraicSection (pullbackModule T.unop.hom E)
  map f := ↾(sectionPullback E f.unop)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro s
    exact sectionPullback_id E T.unop s
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (sectionPullback_comp E g.unop f.unop s).symm

/-- EGA IV, quatrième partie, (18.5.1), printed p.125.
The statement explicitly defines this section functor on all schemes over Z,
including pullback maps, and identifies V(E dual) as a representing scheme.
The constant finite rank hypothesis here is a direct special case of the
published finite locally free hypothesis.
Primary publication: https://numdam.org/item/10.1007/BF02732123.pdf . -/
theorem _root_.LeBrunSalamon.PublishedInputs.SectionRepresentability.finiteFree
    {Z : Scheme.{0}} {E : OModule Z} {r : ℕ} (hE : IsLocallyFreeOfRank E r) :
    (sectionFunctor E).IsRepresentable := by
  sorry

/-- Forgetting the categorical packaging identifies morphisms over Z with
the literal subtype used by the project's TotalBundle API. -/
def overHomEquiv {Z : Scheme.{0}} (V : Over Z) (T : Scheme.{0}) (f : T ⟶ Z) :
    {h : T ⟶ V.left // h ≫ V.hom = f} ≃ (Over.mk f ⟶ V) where
  toFun h := Over.homMk h.val h.property
  invFun h := ⟨h.left, h.w⟩
  left_inv _ := rfl
  right_inv h := by ext; rfl

/-- A representing natural equivalence supplies a universal section by
applying it to the identity, and its naturality gives the exact project map.
This is the substantive conversion missing from the former composite leaf. -/
theorem represented_section_data {Z : Scheme.{0}} {E : OModule Z} {r : ℕ}
    (hE : IsLocallyFreeOfRank E r) :
    ∃ (V : Scheme.{0}) (p : V ⟶ Z)
      (τ : AlgebraicSection (pullbackModule p E)),
      ∀ (T : Scheme.{0}) (f : T ⟶ Z),
        Function.Bijective (fun h : {h : T ⟶ V // h ≫ p = f} =>
          pullSection h.val τ ≫ (compositionPullback h.val p f h.property E).hom) := by
  letI := PublishedInputs.SectionRepresentability.finiteFree hE
  obtain ⟨V, ⟨e⟩⟩ := Functor.IsRepresentable.has_representation (F := sectionFunctor E)
  let τ := e.homEquiv (𝟙 V)
  refine ⟨V.left, V.hom, τ, ?_⟩
  intro T f
  let k := overHomEquiv V T f
  have he (h : {h : T ⟶ V.left // h ≫ V.hom = f}) :
      pullSection h.val τ ≫ (compositionPullback h.val V.hom f h.property E).hom =
        e.homEquiv (k h) := by
    exact (e.homEquiv_eq (k h)).symm
  have hm : (fun h : {h : T ⟶ V.left // h ≫ V.hom = f} =>
      pullSection h.val τ ≫ (compositionPullback h.val V.hom f h.property E).hom) =
      (k.trans e.homEquiv) := funext he
  rw [hm]
  exact (k.trans e.homEquiv).bijective

end LeBrunSalamon.SectionRepresentability

end
