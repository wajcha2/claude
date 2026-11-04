import LSFamilyBivectors
import LSFlatSectionDescent
import LSLineValueDescent
import LSReducedCover

/-!
# Canonical section transport and relative external products.

This namespace block is extracted verbatim from the candidate descent
source. Public names, statements and proof bodies are retained. The preceding
transport blocks are imported so each completed native output can be reused.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.PhaseTwentyEight.ExternalExchangeCoherenceProof

namespace LeBrunSalamon.Construction.FamilyBivectors

namespace SectionTransport

theorem pull_sum {Y Z : Scheme} (f : Y ⟶ Z) {E : OModule Z}
    {N : ℕ} (a : Fin N → AlgebraicSection E) :
    pullSection f (∑ i, a i) = ∑ i, pullSection f (a i) := by
  simp only [pullSection, restrictSection, Functor.map_sum, Preadditive.comp_sum]

/-- Associativity of canonical composition pullbacks, with all three
composite morphisms named explicitly. -/
theorem composition_assoc {T Y Z W : Scheme}
    (f : T ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (fg : T ⟶ Z) (gh : Y ⟶ W) (fgh : T ⟶ W)
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hfgh : f ≫ gh = fgh) (hfgh' : fg ≫ h = fgh)
    (E : OModule W) :
    (Scheme.Modules.pullback f).map (compositionPullback g h gh hgh E).hom ≫
        (compositionPullback f gh fgh hfgh E).hom =
      (compositionPullback f g fg hfg (pullbackModule h E)).hom ≫
        (compositionPullback fg h fgh hfgh' E).hom :=
  Descent.TotalLine.compositionPullback_assoc f g h gh hgh fg hfg fgh hfgh hfgh' E

/-- Evaluation of a pulled square comparison followed by the actual
target composition is independent of the route around the square. -/
theorem square_comp {T Y C W Z : Scheme}
    (f : T ⟶ Y) (a : Y ⟶ C) (b : C ⟶ Z)
    (c : Y ⟶ W) (d : W ⟶ Z) (h : a ≫ b = c ≫ d)
    (r : T ⟶ W) (hfr : f ≫ c = r)
    (k : T ⟶ Z) (hrk : r ≫ d = k)
    (hfk : (f ≫ a) ≫ b = k) (E : OModule Z) :
    (Scheme.Modules.pullback f).map (pullbackSquareIso a b c d h E).hom ≫
        (compositionPullback f c r hfr (pullbackModule d E)).hom ≫
        (compositionPullback r d k hrk E).hom =
      (compositionPullback f a (f ≫ a) rfl (pullbackModule b E)).hom ≫
        (compositionPullback (f ≫ a) b k hfk E).hom := by
  have hfc : f ≫ (c ≫ d) = k := by rw [← Category.assoc, hfr, hrk]
  rw [← composition_assoc f c d r (c ≫ d) k hfr rfl hfc hrk E]
  rw [← Category.assoc, ← Functor.map_comp,
    FlatSectionDescent.squareIso_comp_composition]
  exact composition_assoc f a b (f ≫ a) (c ≫ d) k rfl h hfc hfk E

/-- Specialization of a section remains valid after any further
pullback, with the endpoint identified by its actual composite map. -/
theorem pull_specialization {T Y Z W : Scheme}
    (f : T ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (fg : T ⟶ Z) (gh : Y ⟶ W) (fgh : T ⟶ W)
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hfgh : f ≫ gh = fgh) (hfgh' : fg ≫ h = fgh)
    {E : OModule W} (a : AlgebraicSection (pullbackModule h E))
    (b : AlgebraicSection (pullbackModule gh E))
    (hab : pullSection g a ≫ (compositionPullback g h gh hgh E).hom = b) :
    pullSection fg a ≫ (compositionPullback fg h fgh hfgh' E).hom =
      pullSection f b ≫ (compositionPullback f gh fgh hfgh E).hom := by
  rw [← hab, pullSection_naturality, Category.assoc,
    composition_assoc f g h fg gh fgh hfg hgh hfgh hfgh' E,
    ← Category.assoc, compositionPullback_sections]

/-- Tensor two sections of actual pulled-back bundles, in the actual
pullback of their tensor product. -/
def tensor {Y Z : Scheme} (g : Y ⟶ Z) {E F : OModule Z}
    (a : AlgebraicSection (pullbackModule g E))
    (b : AlgebraicSection (pullbackModule g F)) :
    AlgebraicSection (pullbackModule g (tensorSheaf E F)) :=
  tensorSection a b ≫ tensorPullbackComparison g E F

/-- The tensor pullback comparison commutes with composition on
sections. Equality of the composite maps is transported explicitly. -/
theorem tensor_pullback {T Y Z : Scheme} (f : T ⟶ Y) (g : Y ⟶ Z)
    (r : T ⟶ Z) (h : f ≫ g = r) {E F : OModule Z}
    (a : AlgebraicSection (pullbackModule g E))
    (b : AlgebraicSection (pullbackModule g F)) :
    pullSection f (tensor g a b) ≫
        (compositionPullback f g r h (tensorSheaf E F)).hom =
      tensor r
        (pullSection f a ≫ (compositionPullback f g r h E).hom)
        (pullSection f b ≫ (compositionPullback f g r h F).hom) := by
  subst r
  simp only [compositionPullback, Iso.trans_hom, Iso.app_hom,
    eqToIso_refl, Iso.refl_hom, Category.comp_id]
  unfold tensor
  rw [pullSection_naturality, ← tensorPullbackComparison_onSections]
  simp only [Category.assoc]
  rw [← ExternalExchangeCoherenceProof.comparison_comp]
  rw [← Category.assoc, tensorSection_map]

/-- Two compatible sections remain compatible after a bundle map.
This records the target's actual square comparison as well. -/
theorem compatibility_map {T Y : Scheme} (f : T ⟶ Y)
    {E E' : OModule Y} (v : E ⟶ E')
    (a : AlgebraicSection (pullbackModule f E))
    (ha : pullSection (pullback.fst f f) a ≫
        (pullbackSquareIso (pullback.fst f f) f (pullback.snd f f) f
          pullback.condition E).hom = pullSection (pullback.snd f f) a) :
    pullSection (pullback.fst f f) (a ≫ (Scheme.Modules.pullback f).map v) ≫
        (pullbackSquareIso (pullback.fst f f) f (pullback.snd f f) f
          pullback.condition E').hom =
      pullSection (pullback.snd f f) (a ≫ (Scheme.Modules.pullback f).map v) := by
  rw [pullSection_naturality, Category.assoc, pullbackSquare_naturality,
    ← Category.assoc, ha, pullSection_naturality]

/-- Point detection on the actual kernel pair. The hypothesis compares
the two actual pullbacks in their common endpoint bundle. -/
theorem compatible_of_point_values {T Y : Scheme}
    (f : T ⟶ Y) (sY : Y ⟶ ComplexBase)
    [AlgebraicGeometry.IsReduced (pullback f f)]
    [LocallyOfFiniteType ((pullback.fst f f) ≫ f ≫ sY)]
    {r : ℕ} (E : AlgebraicVectorBundle Y r)
    (a : AlgebraicSection (pullbackModule f E.sheaf))
    (ha : ∀ (q₀ q₁ : PointsOver ComplexBase (𝟙 ComplexBase) T (f ≫ sY))
      (h : q₀.val ≫ f = q₁.val ≫ f),
      pullSection q₀.val a ≫
          (compositionPullback q₀.val f (q₁.val ≫ f) h E.sheaf).hom =
        pullSection q₁.val a ≫
          (compositionPullback q₁.val f (q₁.val ≫ f) rfl E.sheaf).hom) :
    pullSection (pullback.fst f f) a ≫
        (pullbackSquareIso (pullback.fst f f) f (pullback.snd f f) f
          pullback.condition E.sheaf).hom =
      pullSection (pullback.snd f f) a := by
  let E₂ : AlgebraicVectorBundle (pullback f f) r := {
    sheaf := pullbackModule (pullback.snd f f) (pullbackModule f E.sheaf)
    locallyFree := pullback_locallyFree (pullback.snd f f)
      (pullback_locallyFree f E.locallyFree) }
  apply ComplexPointSectionDetection.section_eq
    ((pullback.fst f f) ≫ f ≫ sY) E₂
  intro z
  let q₀ : PointsOver ComplexBase (𝟙 ComplexBase) T (f ≫ sY) :=
    ⟨z.val ≫ pullback.fst f f, by simpa only [Category.assoc] using z.property⟩
  have h : (z.val ≫ pullback.fst f f) ≫ f =
      (z.val ≫ pullback.snd f f) ≫ f := by
    simpa only [Category.assoc] using congrArg (fun k => z.val ≫ k)
      (pullback.condition (f := f) (g := f))
  let q₁ : PointsOver ComplexBase (𝟙 ComplexBase) T (f ≫ sY) :=
    ⟨z.val ≫ pullback.snd f f, by
      rw [← Category.assoc, ← h]
      simpa only [q₀, Category.assoc] using q₀.property⟩
  let A := compositionPullback z.val (pullback.snd f f) q₁.val rfl
    (pullbackModule f E.sheaf)
  let B := compositionPullback q₁.val f (q₁.val ≫ f) rfl E.sheaf
  apply (cancel_mono (A.hom ≫ B.hom)).mp
  rw [pullSection_naturality]
  simp only [Category.assoc]
  rw [square_comp z.val (pullback.fst f f) f (pullback.snd f f) f
    pullback.condition q₁.val rfl (q₁.val ≫ f) rfl h E.sheaf]
  rw [← Category.assoc, compositionPullback_sections, ha q₀ q₁ h]
  rw [← Category.assoc, compositionPullback_sections]

/-- Converting a section from a named composite bundle to the iterated
pullback does not change its normalized value on any test scheme. -/
theorem inverse_composition_value {A T Y Z : Scheme}
    (q : A ⟶ T) (f : T ⟶ Y) (p : Y ⟶ Z) (r : T ⟶ Z) (h : f ≫ p = r)
    (y : A ⟶ Y) (hy : q ≫ f = y)
    (z : A ⟶ Z) (hz : y ≫ p = z) (hqr : q ≫ r = z)
    {E : OModule Z} (a : AlgebraicSection (pullbackModule r E)) :
    pullSection q (a ≫ (compositionPullback f p r h E).inv) ≫
        (compositionPullback q f y hy (pullbackModule p E)).hom ≫
        (compositionPullback y p z hz E).hom =
      pullSection q a ≫ (compositionPullback q r z hqr E).hom := by
  rw [pullSection_naturality]
  simp only [Category.assoc]
  rw [← composition_assoc q f p y r z hy h hqr hz E]
  rw [← Category.assoc ((Scheme.Modules.pullback q).map _), ← Functor.map_comp]
  simp only [Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

end SectionTransport

namespace RelativeSquare

variable {C B : Scheme} (pi : C ⟶ B)

/-- Decomposable sections on the actual relative square. -/
def productSection {E F : OModule C}
    (a : AlgebraicSection E) (b : AlgebraicSection F) :
    AlgebraicSection (box pi E F) :=
  tensorSection (pullSection (left pi) a) (pullSection (right pi) b)

@[reassoc] theorem productSection_map {E E' F F' : OModule C}
    (a : AlgebraicSection E) (b : AlgebraicSection F)
    (u : E ⟶ E') (v : F ⟶ F') :
    productSection pi a b ≫ boxMap pi u v =
      productSection pi (a ≫ u) (b ≫ v) := by
  unfold productSection boxMap
  rw [tensorSection_map, pullSection_naturality, pullSection_naturality]

@[reassoc] theorem comparison_onProducts {X : Scheme} (sX : X ⟶ ComplexBase)
    (sB : B ⟶ ComplexBase) (e : C ⟶ X) (he : e ≫ sX = pi ≫ sB)
    {E F : OModule X} (a : AlgebraicSection E) (b : AlgebraicSection F) :
    productSection pi (pullSection e a) (pullSection e b) ≫
        comparison pi sX sB e he E F =
      pullSection (evaluation pi sX sB e he) (externalProductSection sX a b) := by
  unfold productSection comparison externalProductSection
  rw [← Category.assoc, tensorSection_map,
    pullbackSquareIso_onSections, pullbackSquareIso_onSections,
    tensorPullbackComparison_onSections]

/-- A product section followed by the relative external comparison is
the tensor of the two canonically transported endpoint sections. -/
theorem product_comparison {X : Scheme} (sX : X ⟶ ComplexBase)
    (sB : B ⟶ ComplexBase) (e : C ⟶ X) (he : e ≫ sX = pi ≫ sB)
    {E F : OModule X}
    (a : AlgebraicSection (pullbackModule e E))
    (b : AlgebraicSection (pullbackModule e F)) :
    productSection pi a b ≫ comparison pi sX sB e he E F =
      SectionTransport.tensor (evaluation pi sX sB e he)
        (pullSection (left pi) a ≫
          (pullbackSquareIso (left pi) e (evaluation pi sX sB e he)
            (firstProjection sX) (evaluation_left pi sX sB e he).symm E).hom)
        (pullSection (right pi) b ≫
          (pullbackSquareIso (right pi) e (evaluation pi sX sB e he)
            (secondProjection sX) (evaluation_right pi sX sB e he).symm F).hom) := by
  unfold productSection comparison SectionTransport.tensor
  rw [← Category.assoc, tensorSection_map]

/-- Pullback of a relative product to any test scheme, expressed in
the actual two endpoint fibres. This is the tensor coherence required
both for complex-point detection and for whole-member comparisons. -/
theorem product_pullback {X T : Scheme} (sX : X ⟶ ComplexBase)
    (sB : B ⟶ ComplexBase) (e : C ⟶ X) (he : e ≫ sX = pi ≫ sB)
    (q : T ⟶ Space pi) (r : T ⟶ SelfProduct sX)
    (hqr : q ≫ evaluation pi sX sB e he = r)
    (x₁ x₂ : T ⟶ X)
    (hx₁ : r ≫ firstProjection sX = x₁)
    (hx₂ : r ≫ secondProjection sX = x₂)
    (hq₁ : (q ≫ left pi) ≫ e = x₁)
    (hq₂ : (q ≫ right pi) ≫ e = x₂)
    {E F : OModule X}
    (a : AlgebraicSection (pullbackModule e E))
    (b : AlgebraicSection (pullbackModule e F)) :
    pullSection q (productSection pi a b ≫ comparison pi sX sB e he E F) ≫
        (compositionPullback q (evaluation pi sX sB e he) r hqr
          (externalTensor sX E F)).hom ≫
        (Descent.LineValue.externalAlongIso sX r x₁ x₂ hx₁ hx₂ E F).inv =
      tensorSection
        (pullSection (q ≫ left pi) a ≫
          (compositionPullback (q ≫ left pi) e x₁ hq₁ E).hom)
        (pullSection (q ≫ right pi) b ≫
          (compositionPullback (q ≫ right pi) e x₂ hq₂ F).hom) := by
  letI := tensorPullbackComparison_isIso r
    (pullbackModule (firstProjection sX) E)
    (pullbackModule (secondProjection sX) F)
  rw [product_comparison, ← Category.assoc]
  erw [SectionTransport.tensor_pullback q (evaluation pi sX sB e he) r hqr
    (E := pullbackModule (firstProjection sX) E)
    (F := pullbackModule (secondProjection sX) F)]
  simp only [SectionTransport.tensor, Descent.LineValue.externalAlongIso,
    Iso.trans_inv, Iso.symm_inv, tensorIso, asIso_inv,
    Category.assoc, IsIso.hom_inv_id_assoc]
  rw [tensorSection_map]
  congr 1
  · rw [pullSection_naturality]
    simp only [Category.assoc]
    rw [SectionTransport.square_comp q (left pi) e
      (evaluation pi sX sB e he) (firstProjection sX)
      (evaluation_left pi sX sB e he).symm r hqr x₁ hx₁ hq₁ E,
      ← Category.assoc, compositionPullback_sections]
  · rw [pullSection_naturality]
    simp only [Category.assoc]
    rw [SectionTransport.square_comp q (right pi) e
      (evaluation pi sX sB e he) (secondProjection sX)
      (evaluation_right pi sX sB e he).symm r hqr x₂ hx₂ hq₂ F,
      ← Category.assoc, compositionPullback_sections]

/-- The external comparison can be normalized directly in the two
endpoint bundles, without introducing an identity pullback. -/
theorem product_normalize {X : Scheme} (sX : X ⟶ ComplexBase)
    (sB : B ⟶ ComplexBase) (e : C ⟶ X) (he : e ≫ sX = pi ≫ sB)
    {E F : OModule X}
    (a : AlgebraicSection (pullbackModule e E))
    (b : AlgebraicSection (pullbackModule e F)) :
    (productSection pi a b ≫ comparison pi sX sB e he E F) ≫
        (Descent.LineValue.externalAlongIso sX
          (evaluation pi sX sB e he) (left pi ≫ e) (right pi ≫ e)
          (evaluation_left pi sX sB e he) (evaluation_right pi sX sB e he) E F).inv =
      tensorSection
        (pullSection (left pi) a ≫
          (compositionPullback (left pi) e (left pi ≫ e) rfl E).hom)
        (pullSection (right pi) b ≫
          (compositionPullback (right pi) e (right pi ≫ e) rfl F).hom) := by
  letI := tensorPullbackComparison_isIso (evaluation pi sX sB e he)
    (pullbackModule (firstProjection sX) E)
    (pullbackModule (secondProjection sX) F)
  rw [product_comparison]
  simp only [SectionTransport.tensor, Descent.LineValue.externalAlongIso,
    Iso.trans_inv, Iso.symm_inv, tensorIso, asIso_inv,
    Category.assoc, IsIso.hom_inv_id_assoc]
  rw [tensorSection_map]
  congr 1
  · rw [Category.assoc]
    apply congrArg (fun k => pullSection (left pi) a ≫ k)
    simp [pullbackSquareIso, compositionPullback, Category.assoc]
  · rw [Category.assoc]
    apply congrArg (fun k => pullSection (right pi) b ≫ k)
    simp [pullbackSquareIso, compositionPullback, Category.assoc]

/-- If the two endpoint sections specialize along an entire source
curve, their compared tensor specializes along the whole source square.
The diagonal is included in this equality. -/
theorem product_atCurve (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) (sB : B ⟶ ComplexBase)
    (e : C ⟶ X.scheme) (he : e ≫ X.structureMap = pi ≫ sB)
    (j : ProjectiveLine ⟶ C) (f : RationalCurve P X) (hf : j ≫ e = f.map)
    (k : SelfProduct P.structureMap ⟶ Space pi)
    (hk₁ : k ≫ left pi = firstProjection P.structureMap ≫ j)
    (hk₂ : k ≫ right pi = secondProjection P.structureMap ≫ j)
    (hk : k ≫ evaluation pi X.structureMap sB e he = curveSquareMap P f)
    {E F : OModule X.scheme}
    (a : AlgebraicSection (pullbackModule e E))
    (b : AlgebraicSection (pullbackModule e F))
    (a₀ : AlgebraicSection (pullbackModule f.map E))
    (b₀ : AlgebraicSection (pullbackModule f.map F))
    (ha : pullSection j a ≫ (compositionPullback j e f.map hf E).hom = a₀)
    (hb : pullSection j b ≫ (compositionPullback j e f.map hf F).hom = b₀) :
    pullSection k (productSection pi a b ≫ comparison pi X.structureMap sB e he E F) ≫
        (compositionPullback k (evaluation pi X.structureMap sB e he)
          (curveSquareMap P f) hk (externalTensor X.structureMap E F)).hom =
      externalProductSection P.structureMap a₀ b₀ ≫ curveExternalComparison P f E F := by
  let A := Descent.LineValue.externalAlongIso X.structureMap (curveSquareMap P f)
    (firstProjection P.structureMap ≫ f.map) (secondProjection P.structureMap ≫ f.map)
    (curveSquareMap_first P f) (curveSquareMap_second P f) E F
  have hke₁ : (k ≫ left pi) ≫ e = firstProjection P.structureMap ≫ f.map := by
    rw [hk₁, Category.assoc, hf]
  have hke₂ : (k ≫ right pi) ≫ e = secondProjection P.structureMap ≫ f.map := by
    rw [hk₂, Category.assoc, hf]
  apply (cancel_mono A.inv).mp
  rw [Category.assoc]
  rw [product_pullback pi X.structureMap sB e he k (curveSquareMap P f) hk
    (firstProjection P.structureMap ≫ f.map) (secondProjection P.structureMap ≫ f.map)
    (curveSquareMap_first P f) (curveSquareMap_second P f) hke₁ hke₂ a b]
  have ha' := SectionTransport.pull_specialization
    (firstProjection P.structureMap) j e (k ≫ left pi) f.map
    (firstProjection P.structureMap ≫ f.map) hk₁.symm hf rfl hke₁ a a₀ ha
  have hb' := SectionTransport.pull_specialization
    (secondProjection P.structureMap) j e (k ≫ right pi) f.map
    (secondProjection P.structureMap ≫ f.map) hk₂.symm hf rfl hke₂ b b₀ hb
  rw [ha', hb']
  exact (product_normalize P.structureMap X.structureMap (𝟙 ComplexBase)
    f.map (by simpa only [Category.comp_id] using f.overC) a₀ b₀).symm

/-- Finite sums of compared endpoint products restrict along the whole source
square. All bundles, sections and source/target tensors are parameters. -/
theorem sum_products_atCurve (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) (sB : B ⟶ ComplexBase)
    (e : C ⟶ X.scheme) (he : e ≫ X.structureMap = pi ≫ sB)
    (j : ProjectiveLine ⟶ C) (f : RationalCurve P X) (hf : j ≫ e = f.map)
    (k : SelfProduct P.structureMap ⟶ Space pi)
    (hk₁ : k ≫ left pi = firstProjection P.structureMap ≫ j)
    (hk₂ : k ≫ right pi = secondProjection P.structureMap ≫ j)
    (hk : k ≫ evaluation pi X.structureMap sB e he = curveSquareMap P f)
    {E F : OModule X.scheme} {N : ℕ}
    (a : Fin N → AlgebraicSection (pullbackModule e E))
    (b : Fin N → AlgebraicSection (pullbackModule e F))
    (a₀ : Fin N → AlgebraicSection (pullbackModule f.map E))
    (b₀ : Fin N → AlgebraicSection (pullbackModule f.map F))
    (S : AlgebraicSection (pullbackModule (evaluation pi X.structureMap sB e he)
      (externalTensor X.structureMap E F)))
    (T : AlgebraicSection (pullbackModule (curveSquareMap P f)
      (externalTensor X.structureMap E F)))
    (hS : S = ∑ i, productSection pi (a i) (b i) ≫
      comparison pi X.structureMap sB e he E F)
    (hT : T = ∑ i, externalProductSection P.structureMap (a₀ i) (b₀ i) ≫
      curveExternalComparison P f E F)
    (ha : ∀ i, pullSection j (a i) ≫
      (compositionPullback j e f.map hf E).hom = a₀ i)
    (hb : ∀ i, pullSection j (b i) ≫
      (compositionPullback j e f.map hf F).hom = b₀ i) :
    pullSection k S ≫
      (compositionPullback k (evaluation pi X.structureMap sB e he)
        (curveSquareMap P f) hk (externalTensor X.structureMap E F)).hom = T := by
  rw [hS, hT, SectionTransport.pull_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  exact product_atCurve pi P X sB e he j f hf k hk₁ hk₂ hk
    (a i) (b i) (a₀ i) (b₀ i) (ha i) (hb i)

end RelativeSquare

end LeBrunSalamon.Construction.FamilyBivectors

end
