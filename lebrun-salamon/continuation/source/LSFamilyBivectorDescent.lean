import LSFamilyBivectors
import LSFlatSectionDescent
import LSLineValueDescent
import LSReducedCover

/-!
# Canonical pullback of the moving-pair tensors and smooth-family descent

All section comparisons in this file use the actual pullback square.
The point-detection step is applied only to reduced schemes locally of
finite type over C. The parametrization cover is the actual smooth
surjection in `FullHomComparison`.
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
      simpa only [Category.assoc] using q₀.property⟩
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
  rw [product_comparison, ← Category.assoc, SectionTransport.tensor_pullback]
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
  congr 1 <;> apply congrArg (fun k => _ ≫ k)
  · simp [pullbackSquareIso, compositionPullback, Category.assoc]
  · simp [pullbackSquareIso, compositionPullback, Category.assoc]

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

end RelativeSquare

namespace Curve

variable (P : ProjectiveLineOverC) {n : ℕ} (X : ContactFanoManifold n)
variable (f : RationalCurve P X.variety)

theorem leftSection_expansion
    (E : ExternalExpansion (projectiveLineVariety P)
      (identityCurveContact P).sequence.line (sourceBivector P)) :
    leftSection P X f = ∑ i,
      externalProductSection P.structureMap
        (E.left i ≫ differential P X f)
        (E.right i ≫ curveContactVelocity P X.contact f) ≫
      curveExternalComparison P f (tangentSheaf X.variety.structureMap)
        X.contact.sequence.line.sheaf := by
  rw [leftSection, leftRaw, E.equation]
  simp only [Preadditive.sum_comp, externalProductSection, externalTensorMap,
    tensorSection_map, pullSection_naturality]

theorem rightSection_expansion
    (E : ExternalExpansion (projectiveLineVariety P)
      (identityCurveContact P).sequence.line (sourceBivector P)) :
    rightSection P X f = ∑ i,
      externalProductSection P.structureMap
        (E.left i ≫ curveContactVelocity P X.contact f)
        (E.right i ≫ differential P X f) ≫
      curveExternalComparison P f X.contact.sequence.line.sheaf
        (tangentSheaf X.variety.structureMap) := by
  rw [rightSection, rightRaw, E.equation]
  simp only [Preadditive.sum_comp, externalProductSection, externalTensorMap,
    tensorSection_map, pullSection_naturality]

@[reassoc] theorem leftSection_contact :
    leftSection P X f ≫ (Scheme.Modules.pullback (curveSquareMap P f)).map
      (movingPairContactLeft X.variety X.contact) = sourceContactValue P X.contact f := by
  change (sourceBivector P ≫ RelativeSquare.boxMap P.structureMap
    (differential P X f) (curveContactVelocity P X.contact f) ≫
    RelativeSquare.comparison P.structureMap X.variety.structureMap (𝟙 ComplexBase)
      f.map (by simpa only [Category.comp_id] using f.overC)
      (tangentSheaf X.variety.structureMap) X.contact.sequence.line.sheaf) ≫
    (Scheme.Modules.pullback (curveSquareMap P f)).map
      (externalTensorMap X.variety.structureMap X.contact.sequence.form (𝟙 _)) = _
  rw [Category.assoc, Category.assoc, ← RelativeSquare.comparison_naturality,
    ← Category.assoc, RelativeSquare.boxMap_comp]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

@[reassoc] theorem rightSection_contact :
    rightSection P X f ≫ (Scheme.Modules.pullback (curveSquareMap P f)).map
      (movingPairContactRight X.variety X.contact) = sourceContactValue P X.contact f := by
  change (sourceBivector P ≫ RelativeSquare.boxMap P.structureMap
    (curveContactVelocity P X.contact f) (differential P X f) ≫
    RelativeSquare.comparison P.structureMap X.variety.structureMap (𝟙 ComplexBase)
      f.map (by simpa only [Category.comp_id] using f.overC)
      X.contact.sequence.line.sheaf (tangentSheaf X.variety.structureMap)) ≫
    (Scheme.Modules.pullback (curveSquareMap P f)).map
      (externalTensorMap X.variety.structureMap (𝟙 _) X.contact.sequence.form) = _
  rw [Category.assoc, Category.assoc, ← RelativeSquare.comparison_naturality,
    ← Category.assoc, RelativeSquare.boxMap_comp]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

end Curve

namespace Parametrized

variable (P : ProjectiveLineOverC) {B : Scheme} (sB : B ⟶ ComplexBase)

/-- The canonical bivector has a finite expansion by actual global
source vector fields. This expands the already fixed tensor; the result
is independent of the selected expansion. -/
theorem bivector_expansion
    (E : ExternalExpansion (projectiveLineVariety P)
      (identityCurveContact P).sequence.line (sourceBivector P)) :
    bivector P sB = ∑ i, RelativeSquare.productSection (parameter P sB)
      (pullSection (projection P sB) (E.left i))
      (pullSection (projection P sB) (E.right i)) := by
  letI := sourceComparison_isIso P sB
  apply (cancel_mono (sourceComparison P sB)).mp
  rw [bivector_comparison, Preadditive.sum_comp]
  simp_rw [sourceComparison, RelativeSquare.comparison_onProducts]
  have h := congrArg (fun a => pullSection (sourceSquare P sB) a) E.equation
  simpa only [pullSection, restrictSection, Functor.map_sum,
    Preadditive.comp_sum] using h

/-- A global vector field on P1 gives its actual relative derivative
along the parametrized family. -/
def vector {d : ℕ} (X : SmoothProperComplexVariety d)
    (e : Source P sB ⟶ X.scheme)
    (he : e ≫ X.structureMap = parameter P sB ≫ sB)
    (v : AlgebraicSection (tangentSheaf P.structureMap)) :
    AlgebraicSection (pullbackModule e (tangentSheaf X.structureMap)) :=
  pullSection (projection P sB) v ≫ differential P sB X e he

/-- The actual derivative section specializes on an entire complex
fibre. This is a statement about sheaf sections on P1, including every
source point, and not only a statement about tangent vectors at a point. -/
theorem vector_atSection {d : ℕ} (X : SmoothProperComplexVariety d)
    (e : Source P sB ⟶ X.scheme)
    (he : e ≫ X.structureMap = parameter P sB ≫ sB)
    (b : ComplexBase ⟶ B) (hb : b ≫ sB = 𝟙 ComplexBase)
    (j : ProjectiveLine ⟶ Source P sB)
    (hj₁ : j ≫ projection P sB = 𝟙 ProjectiveLine)
    (hj₂ : j ≫ parameter P sB = P.structureMap ≫ b)
    (hf : (j ≫ e) ≫ X.structureMap = P.structureMap)
    (v : AlgebraicSection (tangentSheaf P.structureMap)) :
    pullSection j (vector P sB X e he v) ≫
        (Scheme.Modules.pullbackComp j e).hom.app (tangentSheaf X.structureMap) =
      v ≫ differentialOver (projectiveLineVariety P) X (j ≫ e) hf := by
  let S := RelativeDifferential.sectionPullbackIso j (projection P sB) hj₁
    (tangentSheaf P.structureMap)
  have hsource : pullSection j (pullSection (projection P sB) v) ≫ S.hom = v := by
    change pullSection j (pullSection (projection P sB) v) ≫
        ((compositionPullback j (projection P sB) (𝟙 ProjectiveLine) hj₁
          (tangentSheaf P.structureMap)).hom ≫
            (Scheme.Modules.pullbackId ProjectiveLine).hom.app
              (tangentSheaf P.structureMap)) = v
    rw [← Category.assoc, compositionPullback_sections, pullSection_id]
  have hsource' : pullSection j (pullSection (projection P sB) v) = v ≫ S.inv := by
    calc
      _ = (pullSection j (pullSection (projection P sB) v) ≫ S.hom) ≫ S.inv := by
        simp only [Category.assoc, S.hom_inv_id, Category.comp_id]
      _ = v ≫ S.inv := congrArg (fun a => a ≫ S.inv) hsource
  rw [vector, pullSection_naturality, hsource']
  simp only [Category.assoc]
  exact congrArg (fun k => v ≫ k)
    (differential_atSection P sB X e he b hb j hj₁ hj₂ hf)

/-- The same fibre specialization with a separately named original
curve. The equality transport is the canonical composition pullback. -/
theorem vector_atCurve {d : ℕ} (X : SmoothProperComplexVariety d)
    (e : Source P sB ⟶ X.scheme)
    (he : e ≫ X.structureMap = parameter P sB ≫ sB)
    (b : ComplexBase ⟶ B) (hb : b ≫ sB = 𝟙 ComplexBase)
    (j : ProjectiveLine ⟶ Source P sB)
    (hj₁ : j ≫ projection P sB = 𝟙 ProjectiveLine)
    (hj₂ : j ≫ parameter P sB = P.structureMap ≫ b)
    (f : RationalCurve P X) (hf : j ≫ e = f.map)
    (v : AlgebraicSection (tangentSheaf P.structureMap)) :
    pullSection j (vector P sB X e he v) ≫
        (compositionPullback j e f.map hf (tangentSheaf X.structureMap)).hom =
      v ≫ differentialOver (projectiveLineVariety P) X f.map f.overC := by
  rcases f with ⟨fm, hfm, hfn⟩
  change j ≫ e = fm at hf
  subst fm
  simpa only [compositionPullback, Iso.trans_hom, Iso.app_hom,
    eqToIso_refl, Iso.refl_hom, Category.comp_id] using
    vector_atSection P sB X e he b hb j hj₁ hj₂ hfm v

/-- Inclusion of the entire square of a complex source fibre. -/
def squareAtSection (b : ComplexBase ⟶ B)
    (j : ProjectiveLine ⟶ Source P sB)
    (hj : j ≫ parameter P sB = P.structureMap ≫ b) :
    SelfProduct P.structureMap ⟶ Square P sB :=
  pullback.lift (firstProjection P.structureMap ≫ j)
    (secondProjection P.structureMap ≫ j) (by
      simp only [Category.assoc, hj]
      simpa only [Category.assoc] using congrArg (fun k => k ≫ b)
        (pullback.condition (f := P.structureMap) (g := P.structureMap)))

@[reassoc] theorem squareAtSection_left (b : ComplexBase ⟶ B)
    (j : ProjectiveLine ⟶ Source P sB)
    (hj : j ≫ parameter P sB = P.structureMap ≫ b) :
    squareAtSection P sB b j hj ≫ RelativeSquare.left (parameter P sB) =
      firstProjection P.structureMap ≫ j := pullback.lift_fst _ _ _

@[reassoc] theorem squareAtSection_right (b : ComplexBase ⟶ B)
    (j : ProjectiveLine ⟶ Source P sB)
    (hj : j ≫ parameter P sB = P.structureMap ≫ b) :
    squareAtSection P sB b j hj ≫ RelativeSquare.right (parameter P sB) =
      secondProjection P.structureMap ≫ j := pullback.lift_snd _ _ _

@[reassoc] theorem squareAtSection_evaluation {d : ℕ}
    (X : SmoothProperComplexVariety d) (e : Source P sB ⟶ X.scheme)
    (he : e ≫ X.structureMap = parameter P sB ≫ sB)
    (b : ComplexBase ⟶ B) (j : ProjectiveLine ⟶ Source P sB)
    (hj : j ≫ parameter P sB = P.structureMap ≫ b)
    (f : RationalCurve P X) (hf : j ≫ e = f.map) :
    squareAtSection P sB b j hj ≫ evaluationSquare P sB X e he =
      curveSquareMap P f := by
  apply pullback.hom_ext
  · simp only [evaluationSquare, Category.assoc,
      RelativeSquare.evaluation_left, squareAtSection_left_assoc,
      hf, curveSquareMap_first]
  · simp only [evaluationSquare, Category.assoc,
      RelativeSquare.evaluation_right, squareAtSection_right_assoc,
      hf, curveSquareMap_second]

end Parametrized

namespace ParametrizedContact

variable (P : ProjectiveLineOverC) {B : Scheme} (sB : B ⟶ ComplexBase)
variable {n : ℕ} (X : ContactFanoManifold n)
variable (e : Parametrized.Source P sB ⟶ X.variety.scheme)
variable (he : e ≫ X.variety.structureMap = Parametrized.parameter P sB ≫ sB)

/-- The contact image of a global source field in the actual family. -/
def contactVector (v : AlgebraicSection (tangentSheaf P.structureMap)) :
    AlgebraicSection (pullbackModule e X.contact.sequence.line.sheaf) :=
  pullSection (Parametrized.projection P sB) v ≫ velocity P sB X e he

theorem contactVector_atCurve
    (b : ComplexBase ⟶ B) (hb : b ≫ sB = 𝟙 ComplexBase)
    (j : ProjectiveLine ⟶ Parametrized.Source P sB)
    (hj₁ : j ≫ Parametrized.projection P sB = 𝟙 ProjectiveLine)
    (hj₂ : j ≫ Parametrized.parameter P sB = P.structureMap ≫ b)
    (f : RationalCurve P X.variety) (hf : j ≫ e = f.map)
    (v : AlgebraicSection (tangentSheaf P.structureMap)) :
    pullSection j (contactVector P sB X e he v) ≫
        (compositionPullback j e f.map hf X.contact.sequence.line.sheaf).hom =
      v ≫ curveContactVelocity P X.contact f := by
  have hv : contactVector P sB X e he v = Parametrized.vector P sB X.variety e he v ≫
      (Scheme.Modules.pullback e).map X.contact.sequence.form := by
    simp only [contactVector, velocity, Parametrized.vector, Category.assoc]
  rw [hv]
  rw [pullSection_naturality, Category.assoc,
    Normalization.BundleGluing.compositionPullback_naturality,
    ← Category.assoc,
    Parametrized.vector_atCurve P sB X.variety e he b hb j hj₁ hj₂ f hf v]
  rfl

/-- A finite decomposable expansion of the first actual tensor. -/
theorem leftSection_expansion
    (E : ExternalExpansion (projectiveLineVariety P)
      (identityCurveContact P).sequence.line (sourceBivector P)) :
    leftSection P sB X e he = ∑ i,
      RelativeSquare.productSection (Parametrized.parameter P sB)
        (Parametrized.vector P sB X.variety e he (E.left i))
        (contactVector P sB X e he (E.right i)) ≫
      RelativeSquare.comparison (Parametrized.parameter P sB)
        X.variety.structureMap sB e he (tangentSheaf X.variety.structureMap)
          X.contact.sequence.line.sheaf := by
  rw [leftSection, Parametrized.bivector_expansion P sB E]
  simp only [Preadditive.sum_comp, RelativeSquare.productSection_map]
  rfl

/-- The same expansion with the tangent and contact factors exchanged. -/
theorem rightSection_expansion
    (E : ExternalExpansion (projectiveLineVariety P)
      (identityCurveContact P).sequence.line (sourceBivector P)) :
    rightSection P sB X e he = ∑ i,
      RelativeSquare.productSection (Parametrized.parameter P sB)
        (contactVector P sB X e he (E.left i))
        (Parametrized.vector P sB X.variety e he (E.right i)) ≫
      RelativeSquare.comparison (Parametrized.parameter P sB)
        X.variety.structureMap sB e he X.contact.sequence.line.sheaf
          (tangentSheaf X.variety.structureMap) := by
  rw [rightSection, Parametrized.bivector_expansion P sB E]
  simp only [Preadditive.sum_comp, RelativeSquare.productSection_map]
  rfl

/-- The family tensor restricts to the original left tensor on the
entire source square of every complex fibre. -/
theorem leftSection_atCurve
    (b : ComplexBase ⟶ B) (hb : b ≫ sB = 𝟙 ComplexBase)
    (j : ProjectiveLine ⟶ Parametrized.Source P sB)
    (hj₁ : j ≫ Parametrized.projection P sB = 𝟙 ProjectiveLine)
    (hj₂ : j ≫ Parametrized.parameter P sB = P.structureMap ≫ b)
    (f : RationalCurve P X.variety) (hf : j ≫ e = f.map) :
    pullSection (Parametrized.squareAtSection P sB b j hj₂)
        (leftSection P sB X e he) ≫
      (compositionPullback (Parametrized.squareAtSection P sB b j hj₂)
        (evaluationSquare P sB X e he) (curveSquareMap P f)
        (Parametrized.squareAtSection_evaluation P sB X.variety e he b j hj₂ f hf)
        (movingPairBundleLeft X.variety X.contact)).hom = Curve.leftSection P X f := by
  obtain ⟨E⟩ := externalExpansion_exists (projectiveLineVariety P)
    (identityCurveContact P).sequence.line (sourceBivector P)
  rw [leftSection_expansion P sB X e he E, Curve.leftSection_expansion P X f E,
    SectionTransport.pull_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  exact RelativeSquare.product_atCurve (Parametrized.parameter P sB)
    P X.variety sB e he j f hf (Parametrized.squareAtSection P sB b j hj₂)
    (Parametrized.squareAtSection_left P sB b j hj₂)
    (Parametrized.squareAtSection_right P sB b j hj₂)
    (Parametrized.squareAtSection_evaluation P sB X.variety e he b j hj₂ f hf)
    (Parametrized.vector P sB X.variety e he (E.left i))
    (contactVector P sB X e he (E.right i))
    (E.left i ≫ Curve.differential P X f)
    (E.right i ≫ curveContactVelocity P X.contact f)
    (Parametrized.vector_atCurve P sB X.variety e he b hb j hj₁ hj₂ f hf (E.left i))
    (contactVector_atCurve P sB X e he b hb j hj₁ hj₂ f hf (E.right i))

/-- The corresponding whole-square specialization for the right
tensor, retaining the differential in its second factor. -/
theorem rightSection_atCurve
    (b : ComplexBase ⟶ B) (hb : b ≫ sB = 𝟙 ComplexBase)
    (j : ProjectiveLine ⟶ Parametrized.Source P sB)
    (hj₁ : j ≫ Parametrized.projection P sB = 𝟙 ProjectiveLine)
    (hj₂ : j ≫ Parametrized.parameter P sB = P.structureMap ≫ b)
    (f : RationalCurve P X.variety) (hf : j ≫ e = f.map) :
    pullSection (Parametrized.squareAtSection P sB b j hj₂)
        (rightSection P sB X e he) ≫
      (compositionPullback (Parametrized.squareAtSection P sB b j hj₂)
        (evaluationSquare P sB X e he) (curveSquareMap P f)
        (Parametrized.squareAtSection_evaluation P sB X.variety e he b j hj₂ f hf)
        (movingPairBundleRight X.variety X.contact)).hom = Curve.rightSection P X f := by
  obtain ⟨E⟩ := externalExpansion_exists (projectiveLineVariety P)
    (identityCurveContact P).sequence.line (sourceBivector P)
  rw [rightSection_expansion P sB X e he E, Curve.rightSection_expansion P X f E,
    SectionTransport.pull_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  exact RelativeSquare.product_atCurve (Parametrized.parameter P sB)
    P X.variety sB e he j f hf (Parametrized.squareAtSection P sB b j hj₂)
    (Parametrized.squareAtSection_left P sB b j hj₂)
    (Parametrized.squareAtSection_right P sB b j hj₂)
    (Parametrized.squareAtSection_evaluation P sB X.variety e he b j hj₂ f hf)
    (contactVector P sB X e he (E.left i))
    (Parametrized.vector P sB X.variety e he (E.right i))
    (E.left i ≫ curveContactVelocity P X.contact f)
    (E.right i ≫ Curve.differential P X f)
    (contactVector_atCurve P sB X e he b hb j hj₁ hj₂ f hf (E.left i))
    (Parametrized.vector_atCurve P sB X.variety e he b hb j hj₁ hj₂ f hf (E.right i))

end ParametrizedContact

namespace Reparametrization

variable (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
variable (he : e.hom ≫ P.structureMap = P.structureMap)

theorem mixedPull_product {E F : OModule ProjectiveLine}
    (a : AlgebraicSection E) (b : AlgebraicSection F) :
    mixedPull P e he E F (externalProductSection P.structureMap a b) =
      externalProductSection P.structureMap (pullSection e.hom a) (pullSection e.hom b) := by
  letI := curveExternalComparison_isIso P (curve P e he) E F
  apply (cancel_mono (curveExternalComparison P (curve P e he) E F)).mp
  rw [mixedPull_comparison, curveExternalComparison_onProducts]

theorem mixedPull_sum {E F : OModule ProjectiveLine} {N : ℕ}
    (a : Fin N → AlgebraicSection (externalTensor P.structureMap E F)) :
    mixedPull P e he E F (∑ i, a i) = ∑ i, mixedPull P e he E F (a i) := by
  simp only [mixedPull, SectionTransport.pull_sum, Preadditive.sum_comp]

variable {n : ℕ} (X : ContactFanoManifold n) (f g : RationalCurve P X.variety)
variable (hg : g.map = e.hom ≫ f.map)

include hg in
@[reassoc] theorem square_comp :
    curveSquareMap P (curve P e he) ≫ curveSquareMap P f = curveSquareMap P g := by
  apply pullback.hom_ext
  · rw [Category.assoc, curveSquareMap_first, ← Category.assoc,
      curveSquareMap_first, curveSquareMap_first]
    change (firstProjection P.structureMap ≫ e.hom) ≫ f.map =
      firstProjection P.structureMap ≫ g.map
    rw [Category.assoc, hg]
  · rw [Category.assoc, curveSquareMap_second, ← Category.assoc,
      curveSquareMap_second, curveSquareMap_second]
    change (secondProjection P.structureMap ≫ e.hom) ≫ f.map =
      secondProjection P.structureMap ≫ g.map
    rw [Category.assoc, hg]

/-- Comparison with the target external bundle commutes with an
actual source reparametrization. A finite expansion is used only to
prove canonical tensor coherence; the tensor itself remains fixed. -/
theorem compared_of_expansion {E F : OModule X.variety.scheme}
    (B : AlgebraicSection (externalTensor P.structureMap
      (pullbackModule f.map E) (pullbackModule f.map F)))
    {N : ℕ} (a : Fin N → AlgebraicSection (pullbackModule f.map E))
    (b : Fin N → AlgebraicSection (pullbackModule f.map F))
    (hB : B = ∑ i, externalProductSection P.structureMap (a i) (b i)) :
    pullSection (curveSquareMap P (curve P e he))
        (B ≫ curveExternalComparison P f E F) ≫
      (compositionPullback (curveSquareMap P (curve P e he)) (curveSquareMap P f)
        (curveSquareMap P g) (square_comp P e he X f g hg)
        (externalTensor X.variety.structureMap E F)).hom =
      (mixedPull P e he (pullbackModule f.map E) (pullbackModule f.map F) B ≫
        externalTensorMap P.structureMap
          (compositionPullback e.hom f.map g.map hg.symm E).hom
          (compositionPullback e.hom f.map g.map hg.symm F).hom) ≫
        curveExternalComparison P g E F := by
  rw [hB, mixedPull_sum]
  simp only [Preadditive.sum_comp, SectionTransport.pull_sum, mixedPull_product]
  apply Finset.sum_congr rfl
  intro i hi
  have hp := RelativeSquare.product_atCurve P.structureMap P X.variety
    (𝟙 ComplexBase) f.map (by simpa only [Category.comp_id] using f.overC)
    e.hom g hg.symm (curveSquareMap P (curve P e he))
    (curveSquareMap_first P (curve P e he))
    (curveSquareMap_second P (curve P e he))
    (square_comp P e he X f g hg) (a i) (b i)
    (pullSection e.hom (a i) ≫ (compositionPullback e.hom f.map g.map hg.symm E).hom)
    (pullSection e.hom (b i) ≫ (compositionPullback e.hom f.map g.map hg.symm F).hom)
    rfl rfl
  simpa only [externalProductSection, externalTensorMap, tensorSection_map,
    pullSection_naturality] using hp

/-- Reparametrization invariance in the actual target bundle, including
all the canonical composition and external-product comparisons. -/
theorem leftSection :
    pullSection (curveSquareMap P (curve P e he)) (Curve.leftSection P X f) ≫
      (compositionPullback (curveSquareMap P (curve P e he)) (curveSquareMap P f)
        (curveSquareMap P g) (square_comp P e he X f g hg)
        (movingPairBundleLeft X.variety X.contact)).hom = Curve.leftSection P X g := by
  obtain ⟨E⟩ := externalExpansion_exists (projectiveLineVariety P)
    (identityCurveContact P).sequence.line (sourceBivector P)
  have hB : Curve.leftRaw P X f = ∑ i,
      externalProductSection P.structureMap
        (E.left i ≫ Curve.differential P X f)
        (E.right i ≫ curveContactVelocity P X.contact f) := by
    rw [Curve.leftRaw, E.equation]
    simp only [Preadditive.sum_comp, externalProductSection, externalTensorMap,
      tensorSection_map, pullSection_naturality]
  rw [Curve.leftSection, compared_of_expansion P e he X f g hg
    (Curve.leftRaw P X f) _ _ hB, leftRaw P e he X f g hg]
  rfl

theorem rightSection :
    pullSection (curveSquareMap P (curve P e he)) (Curve.rightSection P X f) ≫
      (compositionPullback (curveSquareMap P (curve P e he)) (curveSquareMap P f)
        (curveSquareMap P g) (square_comp P e he X f g hg)
        (movingPairBundleRight X.variety X.contact)).hom = Curve.rightSection P X g := by
  obtain ⟨E⟩ := externalExpansion_exists (projectiveLineVariety P)
    (identityCurveContact P).sequence.line (sourceBivector P)
  have hB : Curve.rightRaw P X f = ∑ i,
      externalProductSection P.structureMap
        (E.left i ≫ curveContactVelocity P X.contact f)
        (E.right i ≫ Curve.differential P X f) := by
    rw [Curve.rightRaw, E.equation]
    simp only [Preadditive.sum_comp, externalProductSection, externalTensorMap,
      tensorSection_map, pullSection_naturality]
  rw [Curve.rightSection, compared_of_expansion P e he X f g hg
    (Curve.rightRaw P X f) _ _ hB, rightRaw P e he X f g hg]
  rfl

end Reparametrization

namespace OpenSection

/-- A section on the pulled-back module over an open subscheme gives
the actual section of the original sheaf on that open. -/
def value {Y : Scheme} (U : Y.Opens) {E : OModule Y}
    (s : AlgebraicSection (pullbackModule U.ι E)) : SectionsOn E U :=
  E.presheaf.map (eqToHom U.ι_image_top.symm).op
    (sectionValue (s ≫ (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app E))

/-- The inverse construction retains the canonical open pullback. -/
def fromValue {Y : Scheme} (U : Y.Opens) {E : OModule Y}
    (s : SectionsOn E U) : AlgebraicSection (pullbackModule U.ι E) :=
  sectionFromValue (E.presheaf.map (eqToHom U.ι_image_top).op s) ≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app E

theorem value_section {Y : Scheme} (U : Y.Opens) {E : OModule Y}
    (s : SectionsOn E U) : value U (fromValue U s) = s := by
  simp only [value, fromValue, Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
    sectionFromValue_spec, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp, eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

theorem section_value {Y : Scheme} (U : Y.Opens) {E : OModule Y}
    (s : AlgebraicSection (pullbackModule U.ι E)) : fromValue U (value U s) = s := by
  apply (cancel_mono ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app E)).mp
  simp only [fromValue, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  apply (sectionValue_bijective (E.restrict U.ι)).injective
  simp only [sectionFromValue_spec, value, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

theorem value_map {Y : Scheme} (U : Y.Opens) {E F : OModule Y}
    (s : AlgebraicSection (pullbackModule U.ι E)) (v : E ⟶ F) :
    value U (s ≫ (Scheme.Modules.pullback U.ι).map v) = v.app U (value U s) := by
  unfold value
  rw [Category.assoc, (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.naturality,
    ← Category.assoc, sectionValue_comp]
  exact sheafHom_naturality v (eqToHom U.ι_image_top.symm)
    (sectionValue (s ≫ (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app E))

theorem value_pullSection {Y : Scheme} (U : Y.Opens) {E : OModule Y}
    (s : AlgebraicSection E) :
    value U (pullSection U.ι s) =
      E.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (sectionValue s) := by
  rw [← FrameEvaluation.restrictedSection_to_pullSection]
  simp only [value, Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
    FrameEvaluation.restrictedSection_value, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← op_comp]
  rfl

end OpenSection

namespace SmoothFamily

variable {P : ProjectiveLineOverC} {p : ProjectiveLinePoint P}
variable {n : ℕ} {X : ContactFanoManifold n} {g : VeryFreeContactConic P p X}
variable {N : FullConicNeighborhood P p X g}
variable {F : StableMaps.ProjectiveNodalFamily P p X.variety X.contact.sequence.line 2}
variable (Q : StableMaps.FullHomComparison P p X.variety N.homSpace N.neighborhood
  X.contact.sequence.line 2 F)

abbrev evaluation : Q.parametrizedSource ⟶ X.variety.scheme :=
  Q.sourceMap ≫ F.evaluation

theorem evaluation_overC :
    evaluation Q ≫ X.variety.structureMap =
      Parametrized.parameter P Q.coverToC ≫ Q.coverToC := by
  rw [evaluation, Category.assoc, F.overC, ← Category.assoc, Q.sourceMap_parameter]
  simpa only [Category.assoc, StableMaps.FullHomComparison.coverToBase,
    StableMaps.FullHomComparison.coverToC] using
    congrArg (fun k => Parametrized.parameter P Q.coverToC ≫ k) Q.overC

abbrev smoothEvaluation : F.smoothSquareOpen.toScheme ⟶ SelfProduct X.variety.structureMap :=
  F.smoothSquareOpen.ι ≫ F.squareEvaluation

abbrev parametrizedEvaluation : Q.ParametrizedSquare ⟶ SelfProduct X.variety.structureMap :=
  ParametrizedContact.evaluationSquare P Q.coverToC X (evaluation Q) (evaluation_overC Q)

@[reassoc] theorem evaluation_commutes :
    Q.parametrizedSquareToSmooth ≫ smoothEvaluation (F := F) =
      parametrizedEvaluation Q := by
  rw [smoothEvaluation, ← Category.assoc, Q.parametrizedSquareToSmooth_ι]
  apply pullback.hom_ext
  · simp only [parametrizedEvaluation, ParametrizedContact.evaluationSquare,
      Parametrized.evaluationSquare, Category.assoc,
      RelativeSquare.evaluation_left, F.squareEvaluation_first,
      Q.parametrizedSquareToFamily_first_assoc, evaluation]
  · simp only [parametrizedEvaluation, ParametrizedContact.evaluationSquare,
      Parametrized.evaluationSquare, Category.assoc,
      RelativeSquare.evaluation_right, F.squareEvaluation_second,
      Q.parametrizedSquareToFamily_second_assoc, evaluation]

abbrev smoothToC : F.smoothSquareOpen.toScheme ⟶ ComplexBase :=
  F.smoothSquareOpen.ι ≫ F.squareToBase ≫ F.toC

@[reassoc] theorem parametrized_toC :
    Q.parametrizedSquareToSmooth ≫ smoothToC (F := F) =
      Q.parametrizedSquareToCover ≫ Q.coverToC := by
  simp only [smoothToC, ← Category.assoc, Q.parametrizedSquareToSmooth_ι,
    Q.parametrizedSquareToFamily_base]
  simpa only [Category.assoc, StableMaps.FullHomComparison.coverToBase,
    StableMaps.FullHomComparison.coverToC] using
    congrArg (fun k => Q.parametrizedSquareToCover ≫ k) Q.overC

abbrev Point := PointsOver ComplexBase (𝟙 ComplexBase) Q.ParametrizedSquare
  (Q.parametrizedSquareToSmooth ≫ smoothToC (F := F))

def coverPoint (t : Point Q) :
    PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC :=
  ⟨t.val ≫ Q.parametrizedSquareToCover, by
    simpa only [Category.assoc, ← parametrized_toC Q] using t.property⟩

def neighborhoodPoint
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    PointsOver ComplexBase (𝟙 ComplexBase) N.neighborhood.toScheme
      (N.neighborhood.ι ≫ N.homSpace.toC) :=
  ⟨q.val ≫ Q.toHom, by simpa only [Category.assoc] using q.property⟩

abbrev curve
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    RationalCurve P X.variety := N.curveAt (neighborhoodPoint Q q)

@[reassoc] theorem fibre_evaluation
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    Q.complexSourceInclusion q ≫ evaluation Q = (curve Q q).map := by
  change Q.complexSourceMap q ≫ F.evaluation = _
  rw [Q.complexSourceMap_evaluation, curve, N.curveAt_spec]
  rfl

def fibreSquare
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    SelfProduct P.structureMap ⟶ Q.ParametrizedSquare :=
  Parametrized.squareAtSection P Q.coverToC q.val (Q.complexSourceInclusion q)
    (pullback.lift_snd _ _ _)

@[reassoc] theorem fibreSquare_evaluation
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    fibreSquare Q q ≫ parametrizedEvaluation Q = curveSquareMap P (curve Q q) :=
  Parametrized.squareAtSection_evaluation P Q.coverToC X.variety
    (evaluation Q) (evaluation_overC Q) q.val (Q.complexSourceInclusion q)
    (pullback.lift_snd _ _ _) (curve Q q) (fibre_evaluation Q q)

def coordinatePair (t : Point Q) : ComplexBase ⟶ SelfProduct P.structureMap :=
  t.val ≫ Parametrized.sourceSquare P Q.coverToC

@[reassoc] theorem coordinatePair_left (t : Point Q) :
    coordinatePair Q t ≫ firstProjection P.structureMap =
      t.val ≫ RelativeSquare.left Q.parametrizedParameter ≫
        Parametrized.projection P Q.coverToC := by
  simp only [coordinatePair, Parametrized.sourceSquare, Category.assoc,
    RelativeSquare.evaluation_left]

@[reassoc] theorem coordinatePair_right (t : Point Q) :
    coordinatePair Q t ≫ secondProjection P.structureMap =
      t.val ≫ RelativeSquare.right Q.parametrizedParameter ≫
        Parametrized.projection P Q.coverToC := by
  simp only [coordinatePair, Parametrized.sourceSquare, Category.assoc,
    RelativeSquare.evaluation_right]

theorem sourcePoint_factor
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC)
    (a : ComplexBase ⟶ Q.parametrizedSource)
    (ha : a ≫ Q.parametrizedParameter = q.val) :
    (a ≫ Parametrized.projection P Q.coverToC) ≫ Q.complexSourceInclusion q = a := by
  have hz : (a ≫ Parametrized.projection P Q.coverToC) ≫ P.structureMap =
      𝟙 ComplexBase := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha, q.property]
  apply pullback.hom_ext
  · simp only [Category.assoc, StableMaps.FullHomComparison.complexSourceInclusion,
      pullback.lift_fst, Category.comp_id]
  · simp only [StableMaps.FullHomComparison.complexSourceInclusion, Category.assoc,
      pullback.lift_snd]
    rw [← Category.assoc, hz, Category.id_comp, ha]

@[reassoc] theorem point_factorization (t : Point Q) :
    coordinatePair Q t ≫ fibreSquare Q (coverPoint Q t) = t.val := by
  apply pullback.hom_ext
  · simp only [fibreSquare, Category.assoc, Parametrized.squareAtSection_left]
    rw [← Category.assoc, coordinatePair_left]
    exact sourcePoint_factor Q (coverPoint Q t)
      (t.val ≫ RelativeSquare.left Q.parametrizedParameter) rfl
  · simp only [fibreSquare, Category.assoc, Parametrized.squareAtSection_right]
    rw [← Category.assoc, coordinatePair_right]
    apply sourcePoint_factor Q (coverPoint Q t)
      (t.val ≫ RelativeSquare.right Q.parametrizedParameter)
    simpa only [coverPoint, Category.assoc] using
      congrArg (fun k => t.val ≫ k) Q.parametrizedSquare_second_parameter

@[reassoc] theorem coordinatePair_toC (t : Point Q) :
    coordinatePair Q t ≫ firstProjection P.structureMap ≫ P.structureMap =
      𝟙 ComplexBase := by
  rw [coordinatePair_left_assoc]
  simp only [Category.assoc, Parametrized.projection, pullback.condition]
  exact (coverPoint Q t).property

theorem same_base (t₀ t₁ : Point Q)
    (h : t₀.val ≫ Q.parametrizedSquareToSmooth =
      t₁.val ≫ Q.parametrizedSquareToSmooth) :
    (coverPoint Q t₀).val ≫ Q.coverToBase =
      (coverPoint Q t₁).val ≫ Q.coverToBase := by
  have hb := congrArg (fun k => k ≫ F.smoothSquareParameter ≫ F.smoothOpen.ι) h
  simpa only [coverPoint, Category.assoc, Q.parametrizedSquareToSmooth_base,
    StableMaps.FullHomComparison.coverToBase] using hb

theorem complexSourceMap_ext
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC)
    {T : Scheme} (u v : T ⟶ ProjectiveLine)
    (hs : u ≫ Q.complexSourceMap q = v ≫ Q.complexSourceMap q)
    (hc : u ≫ P.structureMap = v ≫ P.structureMap) : u = v := by
  apply (cancel_mono (Q.complexFibreIso q).hom).mp
  apply pullback.hom_ext
  · simpa only [Category.assoc, Q.complexFibreIso_source] using hs
  · simpa only [Category.assoc, Q.complexFibreIso_toC] using hc

@[reassoc] theorem coordinatePair_source_left (t : Point Q) :
    coordinatePair Q t ≫ firstProjection P.structureMap ≫
        Q.complexSourceMap (coverPoint Q t) =
      t.val ≫ RelativeSquare.left Q.parametrizedParameter ≫ Q.sourceMap := by
  rw [StableMaps.FullHomComparison.complexSourceMap, ← Category.assoc,
    ← Category.assoc, coordinatePair_left]
  rw [sourcePoint_factor Q (coverPoint Q t)
    (t.val ≫ RelativeSquare.left Q.parametrizedParameter) rfl]

@[reassoc] theorem coordinatePair_source_right (t : Point Q) :
    coordinatePair Q t ≫ secondProjection P.structureMap ≫
        Q.complexSourceMap (coverPoint Q t) =
      t.val ≫ RelativeSquare.right Q.parametrizedParameter ≫ Q.sourceMap := by
  rw [StableMaps.FullHomComparison.complexSourceMap, ← Category.assoc,
    ← Category.assoc, coordinatePair_right]
  have hp : (t.val ≫ RelativeSquare.right Q.parametrizedParameter) ≫
      Q.parametrizedParameter = (coverPoint Q t).val := by
    simpa only [coverPoint, Category.assoc] using
      congrArg (fun k => t.val ≫ k) Q.parametrizedSquare_second_parameter
  rw [sourcePoint_factor Q (coverPoint Q t)
    (t.val ≫ RelativeSquare.right Q.parametrizedParameter) hp]

theorem transition_curves (t₀ t₁ : Point Q)
    (h : t₀.val ≫ Q.parametrizedSquareToSmooth =
      t₁.val ≫ Q.parametrizedSquareToSmooth) :
    (curve Q (coverPoint Q t₀)).map =
      (Q.complexTransition (coverPoint Q t₀) (coverPoint Q t₁)
        (same_base Q t₀ t₁ h)).hom ≫ (curve Q (coverPoint Q t₁)).map := by
  rw [← fibre_evaluation Q (coverPoint Q t₀),
    ← fibre_evaluation Q (coverPoint Q t₁)]
  change Q.complexSourceMap (coverPoint Q t₀) ≫ F.evaluation =
    _ ≫ Q.complexSourceMap (coverPoint Q t₁) ≫ F.evaluation
  rw [Q.complexTransition_source_assoc]

theorem transition_coordinates (t₀ t₁ : Point Q)
    (h : t₀.val ≫ Q.parametrizedSquareToSmooth =
      t₁.val ≫ Q.parametrizedSquareToSmooth) :
    coordinatePair Q t₀ ≫ curveSquareMap P
      (Reparametrization.curve P
        (Q.complexTransition (coverPoint Q t₀) (coverPoint Q t₁) (same_base Q t₀ t₁ h))
        (Q.complexTransition_overC (coverPoint Q t₀) (coverPoint Q t₁)
          (same_base Q t₀ t₁ h))) = coordinatePair Q t₁ := by
  let e := Q.complexTransition (coverPoint Q t₀) (coverPoint Q t₁) (same_base Q t₀ t₁ h)
  have he : e.hom ≫ P.structureMap = P.structureMap :=
    Q.complexTransition_overC _ _ _
  have hfamily : t₀.val ≫ Q.parametrizedSquareToFamily =
      t₁.val ≫ Q.parametrizedSquareToFamily := by
    simpa only [Category.assoc, Q.parametrizedSquareToSmooth_ι] using
      congrArg (fun k => k ≫ F.smoothSquareOpen.ι) h
  apply pullback.hom_ext
  · simp only [Category.assoc, curveSquareMap_first]
    apply complexSourceMap_ext Q (coverPoint Q t₁)
    · simp only [Category.assoc, Q.complexTransition_source,
        coordinatePair_source_left]
      simpa only [Category.assoc, Q.parametrizedSquareToFamily_first] using
        congrArg (fun k => k ≫ pullback.fst F.parameter F.parameter) hfamily
    · simp only [Category.assoc, he, coordinatePair_toC]
  · simp only [Category.assoc, curveSquareMap_second]
    apply complexSourceMap_ext Q (coverPoint Q t₁)
    · simp only [Category.assoc, Q.complexTransition_source,
        coordinatePair_source_right]
      simpa only [Category.assoc, Q.parametrizedSquareToFamily_second] using
        congrArg (fun k => k ≫ pullback.snd F.parameter F.parameter) hfamily
    · simp only [Category.assoc, he]
      simpa only [← pullback.condition] using
        (coordinatePair_toC Q t₀).trans (coordinatePair_toC Q t₁).symm

abbrev left : AlgebraicSection
    (pullbackModule (parametrizedEvaluation Q) (movingPairBundleLeft X.variety X.contact)) :=
  ParametrizedContact.leftSection P Q.coverToC X (evaluation Q) (evaluation_overC Q)

abbrev right : AlgebraicSection
    (pullbackModule (parametrizedEvaluation Q) (movingPairBundleRight X.variety X.contact)) :=
  ParametrizedContact.rightSection P Q.coverToC X (evaluation Q) (evaluation_overC Q)

theorem fibre_left
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    pullSection (fibreSquare Q q) (left Q) ≫
      (compositionPullback (fibreSquare Q q) (parametrizedEvaluation Q)
        (curveSquareMap P (curve Q q)) (fibreSquare_evaluation Q q)
        (movingPairBundleLeft X.variety X.contact)).hom = Curve.leftSection P X (curve Q q) :=
  ParametrizedContact.leftSection_atCurve P Q.coverToC X (evaluation Q)
    (evaluation_overC Q) q.val q.property (Q.complexSourceInclusion q)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (curve Q q) (fibre_evaluation Q q)

theorem fibre_right
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    pullSection (fibreSquare Q q) (right Q) ≫
      (compositionPullback (fibreSquare Q q) (parametrizedEvaluation Q)
        (curveSquareMap P (curve Q q)) (fibreSquare_evaluation Q q)
        (movingPairBundleRight X.variety X.contact)).hom = Curve.rightSection P X (curve Q q) :=
  ParametrizedContact.rightSection_atCurve P Q.coverToC X (evaluation Q)
    (evaluation_overC Q) q.val q.property (Q.complexSourceInclusion q)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (curve Q q) (fibre_evaluation Q q)

@[reassoc] theorem coordinatePair_evaluation (t : Point Q) :
    coordinatePair Q t ≫ curveSquareMap P (curve Q (coverPoint Q t)) =
      t.val ≫ parametrizedEvaluation Q := by
  rw [← fibreSquare_evaluation Q (coverPoint Q t), ← Category.assoc, point_factorization]

theorem point_left (t : Point Q) (x : ComplexBase ⟶ SelfProduct X.variety.structureMap)
    (hx : t.val ≫ parametrizedEvaluation Q = x)
    (hz : coordinatePair Q t ≫ curveSquareMap P (curve Q (coverPoint Q t)) = x) :
    pullSection t.val (left Q) ≫
      (compositionPullback t.val (parametrizedEvaluation Q) x hx
        (movingPairBundleLeft X.variety X.contact)).hom =
    pullSection (coordinatePair Q t) (Curve.leftSection P X (curve Q (coverPoint Q t))) ≫
      (compositionPullback (coordinatePair Q t)
        (curveSquareMap P (curve Q (coverPoint Q t))) x hz
        (movingPairBundleLeft X.variety X.contact)).hom :=
  SectionTransport.pull_specialization (coordinatePair Q t) (fibreSquare Q (coverPoint Q t))
    (parametrizedEvaluation Q) t.val (curveSquareMap P (curve Q (coverPoint Q t))) x
    (point_factorization Q t) (fibreSquare_evaluation Q (coverPoint Q t)) hz hx
    (left Q) (Curve.leftSection P X (curve Q (coverPoint Q t))) (fibre_left Q (coverPoint Q t))

theorem point_right (t : Point Q) (x : ComplexBase ⟶ SelfProduct X.variety.structureMap)
    (hx : t.val ≫ parametrizedEvaluation Q = x)
    (hz : coordinatePair Q t ≫ curveSquareMap P (curve Q (coverPoint Q t)) = x) :
    pullSection t.val (right Q) ≫
      (compositionPullback t.val (parametrizedEvaluation Q) x hx
        (movingPairBundleRight X.variety X.contact)).hom =
    pullSection (coordinatePair Q t) (Curve.rightSection P X (curve Q (coverPoint Q t))) ≫
      (compositionPullback (coordinatePair Q t)
        (curveSquareMap P (curve Q (coverPoint Q t))) x hz
        (movingPairBundleRight X.variety X.contact)).hom :=
  SectionTransport.pull_specialization (coordinatePair Q t) (fibreSquare Q (coverPoint Q t))
    (parametrizedEvaluation Q) t.val (curveSquareMap P (curve Q (coverPoint Q t))) x
    (point_factorization Q t) (fibreSquare_evaluation Q (coverPoint Q t)) hz hx
    (right Q) (Curve.rightSection P X (curve Q (coverPoint Q t))) (fibre_right Q (coverPoint Q t))

theorem same_evaluation (t₀ t₁ : Point Q)
    (h : t₀.val ≫ Q.parametrizedSquareToSmooth =
      t₁.val ≫ Q.parametrizedSquareToSmooth) :
    t₀.val ≫ parametrizedEvaluation Q = t₁.val ≫ parametrizedEvaluation Q := by
  simpa only [Category.assoc, evaluation_commutes] using
    congrArg (fun k => k ≫ smoothEvaluation (F := F)) h

/-- The two values on an actual double fibre agree after the canonical
identification of their target fibres. -/
theorem left_point_values (t₀ t₁ : Point Q)
    (h : t₀.val ≫ Q.parametrizedSquareToSmooth =
      t₁.val ≫ Q.parametrizedSquareToSmooth) :
    pullSection t₀.val (left Q) ≫
      (compositionPullback t₀.val (parametrizedEvaluation Q)
        (t₁.val ≫ parametrizedEvaluation Q) (same_evaluation Q t₀ t₁ h)
        (movingPairBundleLeft X.variety X.contact)).hom =
    pullSection t₁.val (left Q) ≫
      (compositionPullback t₁.val (parametrizedEvaluation Q)
        (t₁.val ≫ parametrizedEvaluation Q) rfl
        (movingPairBundleLeft X.variety X.contact)).hom := by
  let e := Q.complexTransition (coverPoint Q t₀) (coverPoint Q t₁) (same_base Q t₀ t₁ h)
  have he : e.hom ≫ P.structureMap = P.structureMap := Q.complexTransition_overC _ _ _
  have hz₀ := (coordinatePair_evaluation Q t₀).trans (same_evaluation Q t₀ t₁ h)
  have hz₁ := coordinatePair_evaluation Q t₁
  rw [point_left Q t₀ _ (same_evaluation Q t₀ t₁ h) hz₀,
    point_left Q t₁ _ rfl hz₁]
  exact (SectionTransport.pull_specialization (coordinatePair Q t₀)
    (curveSquareMap P (Reparametrization.curve P e he))
    (curveSquareMap P (curve Q (coverPoint Q t₁))) (coordinatePair Q t₁)
    (curveSquareMap P (curve Q (coverPoint Q t₀))) (t₁.val ≫ parametrizedEvaluation Q)
    (transition_coordinates Q t₀ t₁ h)
    (Reparametrization.square_comp P e he X (curve Q (coverPoint Q t₁))
      (curve Q (coverPoint Q t₀)) (transition_curves Q t₀ t₁ h)) hz₀ hz₁
    (Curve.leftSection P X (curve Q (coverPoint Q t₁)))
    (Curve.leftSection P X (curve Q (coverPoint Q t₀)))
    (Reparametrization.leftSection P e he X (curve Q (coverPoint Q t₁))
      (curve Q (coverPoint Q t₀)) (transition_curves Q t₀ t₁ h))).symm

theorem right_point_values (t₀ t₁ : Point Q)
    (h : t₀.val ≫ Q.parametrizedSquareToSmooth =
      t₁.val ≫ Q.parametrizedSquareToSmooth) :
    pullSection t₀.val (right Q) ≫
      (compositionPullback t₀.val (parametrizedEvaluation Q)
        (t₁.val ≫ parametrizedEvaluation Q) (same_evaluation Q t₀ t₁ h)
        (movingPairBundleRight X.variety X.contact)).hom =
    pullSection t₁.val (right Q) ≫
      (compositionPullback t₁.val (parametrizedEvaluation Q)
        (t₁.val ≫ parametrizedEvaluation Q) rfl
        (movingPairBundleRight X.variety X.contact)).hom := by
  let e := Q.complexTransition (coverPoint Q t₀) (coverPoint Q t₁) (same_base Q t₀ t₁ h)
  have he : e.hom ≫ P.structureMap = P.structureMap := Q.complexTransition_overC _ _ _
  have hz₀ := (coordinatePair_evaluation Q t₀).trans (same_evaluation Q t₀ t₁ h)
  have hz₁ := coordinatePair_evaluation Q t₁
  rw [point_right Q t₀ _ (same_evaluation Q t₀ t₁ h) hz₀,
    point_right Q t₁ _ rfl hz₁]
  exact (SectionTransport.pull_specialization (coordinatePair Q t₀)
    (curveSquareMap P (Reparametrization.curve P e he))
    (curveSquareMap P (curve Q (coverPoint Q t₁))) (coordinatePair Q t₁)
    (curveSquareMap P (curve Q (coverPoint Q t₀))) (t₁.val ≫ parametrizedEvaluation Q)
    (transition_coordinates Q t₀ t₁ h)
    (Reparametrization.square_comp P e he X (curve Q (coverPoint Q t₁))
      (curve Q (coverPoint Q t₀)) (transition_curves Q t₀ t₁ h)) hz₀ hz₁
    (Curve.rightSection P X (curve Q (coverPoint Q t₁)))
    (Curve.rightSection P X (curve Q (coverPoint Q t₀)))
    (Reparametrization.rightSection P e he X (curve Q (coverPoint Q t₁))
      (curve Q (coverPoint Q t₀)) (transition_curves Q t₀ t₁ h))).symm

include Q in
theorem smooth_locallyOfFiniteType : LocallyOfFiniteType (smoothToC (F := F)) := by
  letI : IsProper F.toC := F.baseProper
  letI : IsProper F.squareToBase := F.squareToBase_proper
  dsimp only [smoothToC]
  infer_instance

theorem parametrized_reduced : AlgebraicGeometry.IsReduced Q.ParametrizedSquare := by
  letI : IsIntegral F.Square := F.square_integral
  letI : IsLocallyNoetherian F.Square := F.square_locallyNoetherian
  letI : AlgebraicGeometry.IsReduced F.smoothSquareOpen.toScheme :=
    isReduced_of_isOpenImmersion F.smoothSquareOpen.ι
  letI : IsLocallyNoetherian F.smoothSquareOpen.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian F.smoothSquareOpen.ι
  letI : Smooth Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_smooth
  letI : GeometricallyIntegral Q.parametrizedSquareToSmooth :=
    Q.parametrizedSquareToSmooth_geometricallyIntegral
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
    Q.parametrizedSquareToSmooth

theorem overlap_reduced : AlgebraicGeometry.IsReduced
    (pullback Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth) := by
  letI : LocallyOfFiniteType (smoothToC (F := F)) := smooth_locallyOfFiniteType Q
  letI : IsLocallyNoetherian F.smoothSquareOpen.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (smoothToC (F := F))
  letI : Smooth Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_smooth
  letI : GeometricallyIntegral Q.parametrizedSquareToSmooth :=
    Q.parametrizedSquareToSmooth_geometricallyIntegral
  letI : AlgebraicGeometry.IsReduced Q.ParametrizedSquare := parametrized_reduced Q
  letI : IsLocallyNoetherian Q.ParametrizedSquare :=
    LocallyOfFiniteType.isLocallyNoetherian Q.parametrizedSquareToSmooth
  infer_instance

theorem overlap_locallyOfFiniteType : LocallyOfFiniteType
    (pullback.fst Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth ≫
      Q.parametrizedSquareToSmooth ≫ smoothToC (F := F)) := by
  letI : LocallyOfFiniteType (smoothToC (F := F)) := smooth_locallyOfFiniteType Q
  letI : Smooth Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_smooth
  infer_instance

def leftCover : AlgebraicSection
    (pullbackModule Q.parametrizedSquareToSmooth
      (MovingPair.leftBundle (smoothEvaluation (F := F))).sheaf) :=
  left Q ≫ (compositionPullback Q.parametrizedSquareToSmooth
    (smoothEvaluation (F := F)) (parametrizedEvaluation Q) (evaluation_commutes Q)
    (movingPairBundleLeft X.variety X.contact)).inv

def rightCover : AlgebraicSection
    (pullbackModule Q.parametrizedSquareToSmooth
      (MovingPair.rightBundle (smoothEvaluation (F := F))).sheaf) :=
  right Q ≫ (compositionPullback Q.parametrizedSquareToSmooth
    (smoothEvaluation (F := F)) (parametrizedEvaluation Q) (evaluation_commutes Q)
    (movingPairBundleRight X.variety X.contact)).inv

@[reassoc] theorem leftCover_comparison : leftCover Q ≫
    (compositionPullback Q.parametrizedSquareToSmooth (smoothEvaluation (F := F))
      (parametrizedEvaluation Q) (evaluation_commutes Q)
      (movingPairBundleLeft X.variety X.contact)).hom = left Q := by
  simp only [leftCover, Category.assoc, Iso.inv_hom_id, Category.comp_id]

@[reassoc] theorem rightCover_comparison : rightCover Q ≫
    (compositionPullback Q.parametrizedSquareToSmooth (smoothEvaluation (F := F))
      (parametrizedEvaluation Q) (evaluation_commutes Q)
      (movingPairBundleRight X.variety X.contact)).hom = right Q := by
  simp only [rightCover, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Equality on the actual double overlap, proved from equality at
complex points of that reduced finite-type scheme. -/
theorem leftCover_compatible :
    pullSection (pullback.fst Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        (leftCover Q) ≫
      (pullbackSquareIso
        (pullback.fst Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        Q.parametrizedSquareToSmooth
        (pullback.snd Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        Q.parametrizedSquareToSmooth pullback.condition
        (MovingPair.leftBundle (smoothEvaluation (F := F))).sheaf).hom =
      pullSection (pullback.snd Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        (leftCover Q) := by
  letI := overlap_reduced Q
  letI := overlap_locallyOfFiniteType Q
  apply SectionTransport.compatible_of_point_values Q.parametrizedSquareToSmooth
    (smoothToC (F := F)) (MovingPair.leftBundle (smoothEvaluation (F := F))) (leftCover Q)
  intro q₀ q₁ h
  have hz : (q₁.val ≫ Q.parametrizedSquareToSmooth) ≫ smoothEvaluation (F := F) =
      q₁.val ≫ parametrizedEvaluation Q := by rw [Category.assoc, evaluation_commutes]
  apply (cancel_mono (compositionPullback (q₁.val ≫ Q.parametrizedSquareToSmooth)
    (smoothEvaluation (F := F)) (q₁.val ≫ parametrizedEvaluation Q) hz
    (movingPairBundleLeft X.variety X.contact)).hom).mp
  simp only [Category.assoc]
  rw [SectionTransport.inverse_composition_value q₀.val Q.parametrizedSquareToSmooth
    (smoothEvaluation (F := F)) (parametrizedEvaluation Q) (evaluation_commutes Q)
    (q₁.val ≫ Q.parametrizedSquareToSmooth) h (q₁.val ≫ parametrizedEvaluation Q) hz
    (same_evaluation Q q₀ q₁ h) (left Q)]
  rw [SectionTransport.inverse_composition_value q₁.val Q.parametrizedSquareToSmooth
    (smoothEvaluation (F := F)) (parametrizedEvaluation Q) (evaluation_commutes Q)
    (q₁.val ≫ Q.parametrizedSquareToSmooth) rfl (q₁.val ≫ parametrizedEvaluation Q) hz
    rfl (left Q)]
  exact left_point_values Q q₀ q₁ h

theorem rightCover_compatible :
    pullSection (pullback.fst Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        (rightCover Q) ≫
      (pullbackSquareIso
        (pullback.fst Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        Q.parametrizedSquareToSmooth
        (pullback.snd Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        Q.parametrizedSquareToSmooth pullback.condition
        (MovingPair.rightBundle (smoothEvaluation (F := F))).sheaf).hom =
      pullSection (pullback.snd Q.parametrizedSquareToSmooth Q.parametrizedSquareToSmooth)
        (rightCover Q) := by
  letI := overlap_reduced Q
  letI := overlap_locallyOfFiniteType Q
  apply SectionTransport.compatible_of_point_values Q.parametrizedSquareToSmooth
    (smoothToC (F := F)) (MovingPair.rightBundle (smoothEvaluation (F := F))) (rightCover Q)
  intro q₀ q₁ h
  have hz : (q₁.val ≫ Q.parametrizedSquareToSmooth) ≫ smoothEvaluation (F := F) =
      q₁.val ≫ parametrizedEvaluation Q := by rw [Category.assoc, evaluation_commutes]
  apply (cancel_mono (compositionPullback (q₁.val ≫ Q.parametrizedSquareToSmooth)
    (smoothEvaluation (F := F)) (q₁.val ≫ parametrizedEvaluation Q) hz
    (movingPairBundleRight X.variety X.contact)).hom).mp
  simp only [Category.assoc]
  rw [SectionTransport.inverse_composition_value q₀.val Q.parametrizedSquareToSmooth
    (smoothEvaluation (F := F)) (parametrizedEvaluation Q) (evaluation_commutes Q)
    (q₁.val ≫ Q.parametrizedSquareToSmooth) h (q₁.val ≫ parametrizedEvaluation Q) hz
    (same_evaluation Q q₀ q₁ h) (right Q)]
  rw [SectionTransport.inverse_composition_value q₁.val Q.parametrizedSquareToSmooth
    (smoothEvaluation (F := F)) (parametrizedEvaluation Q) (evaluation_commutes Q)
    (q₁.val ≫ Q.parametrizedSquareToSmooth) rfl (q₁.val ≫ parametrizedEvaluation Q) hz
    rfl (right Q)]
  exact right_point_values Q q₀ q₁ h

theorem smoothLeft_exists : ∃! s : AlgebraicSection
    (MovingPair.leftBundle (smoothEvaluation (F := F))).sheaf,
    pullSection Q.parametrizedSquareToSmooth s = leftCover Q := by
  letI : Smooth Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_smooth
  letI : Surjective Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_surjective
  exact FlatSectionDescent.existsUnique_fppf Q.parametrizedSquareToSmooth
    (MovingPair.leftBundle (smoothEvaluation (F := F))) (leftCover Q) (leftCover_compatible Q)

theorem smoothRight_exists : ∃! s : AlgebraicSection
    (MovingPair.rightBundle (smoothEvaluation (F := F))).sheaf,
    pullSection Q.parametrizedSquareToSmooth s = rightCover Q := by
  letI : Smooth Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_smooth
  letI : Surjective Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_surjective
  exact FlatSectionDescent.existsUnique_fppf Q.parametrizedSquareToSmooth
    (MovingPair.rightBundle (smoothEvaluation (F := F))) (rightCover Q) (rightCover_compatible Q)

/-- The uniquely descended actual left section on the smooth family. -/
def smoothLeft : AlgebraicSection
    (MovingPair.leftBundle (smoothEvaluation (F := F))).sheaf :=
  Classical.choose (smoothLeft_exists Q)

/-- The uniquely descended actual right section on the smooth family. -/
def smoothRight : AlgebraicSection
    (MovingPair.rightBundle (smoothEvaluation (F := F))).sheaf :=
  Classical.choose (smoothRight_exists Q)

theorem smoothLeft_pullback :
    pullSection Q.parametrizedSquareToSmooth (smoothLeft Q) = leftCover Q :=
  (Classical.choose_spec (smoothLeft_exists Q)).1

theorem smoothRight_pullback :
    pullSection Q.parametrizedSquareToSmooth (smoothRight Q) = rightCover Q :=
  (Classical.choose_spec (smoothRight_exists Q)).1

/-- Universal normalization on the actual parametrization cover.
This equality may subsequently be pulled back along arbitrary schemes. -/
theorem smoothLeft_normalization :
    pullSection Q.parametrizedSquareToSmooth (smoothLeft Q) ≫
      (compositionPullback Q.parametrizedSquareToSmooth (smoothEvaluation (F := F))
        (parametrizedEvaluation Q) (evaluation_commutes Q)
        (movingPairBundleLeft X.variety X.contact)).hom = left Q := by
  rw [smoothLeft_pullback, leftCover_comparison]

theorem smoothRight_normalization :
    pullSection Q.parametrizedSquareToSmooth (smoothRight Q) ≫
      (compositionPullback Q.parametrizedSquareToSmooth (smoothEvaluation (F := F))
        (parametrizedEvaluation Q) (evaluation_commutes Q)
        (movingPairBundleRight X.variety X.contact)).hom = right Q := by
  rw [smoothRight_pullback, rightCover_comparison]

theorem smooth_commonContact :
    smoothLeft Q ≫ MovingPair.leftContact (smoothEvaluation (F := F)) =
      smoothRight Q ≫ MovingPair.rightContact (smoothEvaluation (F := F)) := by
  letI : Smooth Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_smooth
  letI : Surjective Q.parametrizedSquareToSmooth := Q.parametrizedSquareToSmooth_surjective
  apply FlatSectionDescent.pullSection_injective_fppf Q.parametrizedSquareToSmooth
    (MovingPair.valueBundle (smoothEvaluation (F := F)))
  apply (cancel_mono (compositionPullback Q.parametrizedSquareToSmooth
    (smoothEvaluation (F := F)) (parametrizedEvaluation Q) (evaluation_commutes Q)
    (externalSquareLine X.variety.structureMap X.contact.sequence.line).sheaf).hom).mp
  rw [pullSection_naturality, pullSection_naturality]
  simp only [Category.assoc]
  rw [Normalization.BundleGluing.compositionPullback_naturality,
    Normalization.BundleGluing.compositionPullback_naturality,
    ← Category.assoc, smoothLeft_normalization,
    ← Category.assoc, smoothRight_normalization]
  exact ParametrizedContact.commonContact P Q.coverToC X (evaluation Q) (evaluation_overC Q)

def restrictedLeft : AlgebraicSection
    (pullbackModule F.smoothSquareOpen.ι (MovingPair.leftBundle F.squareEvaluation).sheaf) :=
  smoothLeft Q ≫ (compositionPullback F.smoothSquareOpen.ι F.squareEvaluation
    (smoothEvaluation (F := F)) rfl (movingPairBundleLeft X.variety X.contact)).inv

def restrictedRight : AlgebraicSection
    (pullbackModule F.smoothSquareOpen.ι (MovingPair.rightBundle F.squareEvaluation).sheaf) :=
  smoothRight Q ≫ (compositionPullback F.smoothSquareOpen.ι F.squareEvaluation
    (smoothEvaluation (F := F)) rfl (movingPairBundleRight X.variety X.contact)).inv

theorem restricted_commonContact :
    restrictedLeft Q ≫ (Scheme.Modules.pullback F.smoothSquareOpen.ι).map
        (MovingPair.leftContact F.squareEvaluation) =
      restrictedRight Q ≫ (Scheme.Modules.pullback F.smoothSquareOpen.ι).map
        (MovingPair.rightContact F.squareEvaluation) := by
  simp only [restrictedLeft, restrictedRight, Category.assoc]
  rw [← Descent.LineValue.composition_inv_naturality,
    ← Descent.LineValue.composition_inv_naturality,
    ← Category.assoc, smooth_commonContact]

/-- The two actual rational sections on the compactified square. Their
domain is exactly the original smooth square open. -/
def rationalPair : MovingPair.RationalVectorPair F.squareEvaluation where
  domain := F.smoothSquareOpen
  dense := F.smoothSquareOpen_dense
  leftSection := OpenSection.value F.smoothSquareOpen (restrictedLeft Q)
  rightSection := OpenSection.value F.smoothSquareOpen (restrictedRight Q)
  common := by
    have h := congrArg (fun a => OpenSection.value F.smoothSquareOpen a)
      (restricted_commonContact Q)
    simpa only [OpenSection.value_map] using h

@[simp] theorem rationalPair_domain : (rationalPair Q).domain = F.smoothSquareOpen := rfl

theorem rationalPair_left_open :
    OpenSection.fromValue F.smoothSquareOpen (rationalPair Q).leftSection = restrictedLeft Q :=
  OpenSection.section_value F.smoothSquareOpen (restrictedLeft Q)

theorem rationalPair_right_open :
    OpenSection.fromValue F.smoothSquareOpen (rationalPair Q).rightSection = restrictedRight Q :=
  OpenSection.section_value F.smoothSquareOpen (restrictedRight Q)

theorem extension_left_smooth (E : (rationalPair Q).Extension) :
    pullSection F.smoothSquareOpen.ι E.leftSection ≫
      (compositionPullback F.smoothSquareOpen.ι F.squareEvaluation
        (smoothEvaluation (F := F)) rfl (movingPairBundleLeft X.variety X.contact)).hom =
      smoothLeft Q := by
  have hv : OpenSection.value F.smoothSquareOpen
      (pullSection F.smoothSquareOpen.ι E.leftSection) =
      OpenSection.value F.smoothSquareOpen (restrictedLeft Q) := by
    rw [OpenSection.value_pullSection]
    exact E.extendsLeft
  have hs := congrArg (fun a => OpenSection.fromValue F.smoothSquareOpen a) hv
  rw [OpenSection.section_value, OpenSection.section_value] at hs
  rw [hs]
  simp only [restrictedLeft, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem extension_right_smooth (E : (rationalPair Q).Extension) :
    pullSection F.smoothSquareOpen.ι E.rightSection ≫
      (compositionPullback F.smoothSquareOpen.ι F.squareEvaluation
        (smoothEvaluation (F := F)) rfl (movingPairBundleRight X.variety X.contact)).hom =
      smoothRight Q := by
  have hv : OpenSection.value F.smoothSquareOpen
      (pullSection F.smoothSquareOpen.ι E.rightSection) =
      OpenSection.value F.smoothSquareOpen (restrictedRight Q) := by
    rw [OpenSection.value_pullSection]
    exact E.extendsRight
  have hs := congrArg (fun a => OpenSection.fromValue F.smoothSquareOpen a) hv
  rw [OpenSection.section_value, OpenSection.section_value] at hs
  rw [hs]
  simp only [restrictedRight, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable (t : PointsOver ComplexBase (𝟙 ComplexBase) N.neighborhood.toScheme
  (N.neighborhood.ι ≫ N.homSpace.toC))

def memberToParametrized : Q.ReducedMemberCover t ⟶ Q.ParametrizedSquare :=
  Q.reducedMemberInclusion t ≫ Q.memberToParametrizedSquare t

def memberToSmooth : Q.ReducedMemberCover t ⟶ F.smoothSquareOpen.toScheme :=
  memberToParametrized Q t ≫ Q.parametrizedSquareToSmooth

def memberToFamily : Q.ReducedMemberCover t ⟶ F.Square :=
  Q.reducedMemberInclusion t ≫ Q.memberToFamilySquare t

abbrev memberEvaluation : Q.ReducedMemberCover t ⟶ SelfProduct X.variety.structureMap :=
  Q.reducedMemberToSquare t ≫ curveSquareMap P (N.curveAt t)

@[reassoc] theorem memberToSmooth_ι :
    memberToSmooth Q t ≫ F.smoothSquareOpen.ι = memberToFamily Q t := by
  simp only [memberToSmooth, memberToParametrized, memberToFamily,
    Category.assoc, Q.parametrizedSquareToSmooth_ι,
    Q.memberToParametrizedSquare_family]

@[reassoc] theorem memberToFamily_evaluation :
    memberToFamily Q t ≫ F.squareEvaluation = memberEvaluation Q t := by
  simp only [memberToFamily, memberEvaluation,
    StableMaps.FullHomComparison.reducedMemberToSquare, Category.assoc,
    Q.member_commutes t (N.curveAt t) (N.curveAt_spec t)]

@[reassoc] theorem memberToSmooth_evaluation :
    memberToSmooth Q t ≫ smoothEvaluation (F := F) = memberEvaluation Q t := by
  rw [smoothEvaluation, ← Category.assoc, memberToSmooth_ι, memberToFamily_evaluation]

@[reassoc] theorem memberToParametrized_evaluation :
    memberToParametrized Q t ≫ parametrizedEvaluation Q = memberEvaluation Q t := by
  rw [← evaluation_commutes, ← Category.assoc]
  exact memberToSmooth_evaluation Q t

@[reassoc] theorem memberToParametrized_parameter :
    memberToParametrized Q t ≫ Q.parametrizedSquareToCover =
      Q.reducedMemberInclusion t ≫ Q.memberToCover t := by
  simp only [memberToParametrized, Category.assoc, Q.memberToParametrizedSquare_base]

@[reassoc] theorem memberToParametrized_toC :
    memberToParametrized Q t ≫ Q.parametrizedSquareToSmooth ≫ smoothToC (F := F) =
      Q.reducedMemberToC t := by
  rw [parametrized_toC, ← Category.assoc, memberToParametrized_parameter]
  rw [Category.assoc, ← Q.member_first_overC t]
  rfl

@[reassoc] theorem memberToParametrized_toHom :
    memberToParametrized Q t ≫ Q.parametrizedSquareToCover ≫ Q.toHom =
      Q.reducedMemberToC t ≫ t.val := by
  rw [← Category.assoc, memberToParametrized_parameter, Category.assoc,
    Q.memberToCover_toHom]
  rfl

@[reassoc] theorem memberToParametrized_coordinates :
    memberToParametrized Q t ≫ Parametrized.sourceSquare P Q.coverToC =
      Q.reducedMemberToSquare t := by
  apply pullback.hom_ext
  · simp only [memberToParametrized, Parametrized.sourceSquare, Category.assoc,
      RelativeSquare.evaluation_left,
      StableMaps.FullHomComparison.memberToParametrizedSquare,
      StableMaps.FullHomComparison.reducedMemberToSquare,
      pullback.lift_fst_assoc, pullback.lift_fst]
  · simp only [memberToParametrized, Parametrized.sourceSquare, Category.assoc,
      RelativeSquare.evaluation_right,
      StableMaps.FullHomComparison.memberToParametrizedSquare,
      StableMaps.FullHomComparison.reducedMemberToSquare,
      pullback.lift_snd_assoc, pullback.lift_fst]

def memberPoint
    (z : PointsOver ComplexBase (𝟙 ComplexBase) (Q.ReducedMemberCover t)
      (Q.reducedMemberToC t)) : Point Q :=
  ⟨z.val ≫ memberToParametrized Q t, by
    rw [Category.assoc, memberToParametrized_toC]
    exact z.property⟩

theorem memberPoint_parameter
    (z : PointsOver ComplexBase (𝟙 ComplexBase) (Q.ReducedMemberCover t)
      (Q.reducedMemberToC t)) :
    neighborhoodPoint Q (coverPoint Q (memberPoint Q t z)) = t := by
  apply Subtype.ext
  change ((z.val ≫ memberToParametrized Q t) ≫ Q.parametrizedSquareToCover) ≫
    Q.toHom = t.val
  simp only [Category.assoc]
  rw [memberToParametrized_toHom, ← Category.assoc, z.property, Category.id_comp]

theorem memberPoint_curve
    (z : PointsOver ComplexBase (𝟙 ComplexBase) (Q.ReducedMemberCover t)
      (Q.reducedMemberToC t)) : curve Q (coverPoint Q (memberPoint Q t z)) = N.curveAt t := by
  rw [curve, memberPoint_parameter]

@[reassoc] theorem memberPoint_coordinates
    (z : PointsOver ComplexBase (𝟙 ComplexBase) (Q.ReducedMemberCover t)
      (Q.reducedMemberToC t)) :
    coordinatePair Q (memberPoint Q t z) = z.val ≫ Q.reducedMemberToSquare t := by
  simp only [coordinatePair, memberPoint, Category.assoc, memberToParametrized_coordinates]

/-- Whole-member normalization after the proper surjective reduction
cover. The source square includes the diagonal and every original point. -/
theorem member_left :
    pullSection (memberToParametrized Q t) (left Q) ≫
      (compositionPullback (memberToParametrized Q t) (parametrizedEvaluation Q)
        (memberEvaluation Q t) (memberToParametrized_evaluation Q t)
        (movingPairBundleLeft X.variety X.contact)).hom =
    pullSection (Q.reducedMemberToSquare t) (Curve.leftSection P X (N.curveAt t)) ≫
      (compositionPullback (Q.reducedMemberToSquare t) (curveSquareMap P (N.curveAt t))
        (memberEvaluation Q t) rfl (movingPairBundleLeft X.variety X.contact)).hom := by
  letI : AlgebraicGeometry.IsReduced (Q.ReducedMemberCover t) :=
    Q.reducedMemberCover_reduced t
  letI : LocallyOfFiniteType (Q.reducedMemberToC t) :=
    Q.reducedMemberToC_locallyOfFiniteType t
  apply ComplexPointSectionDetection.section_eq (Q.reducedMemberToC t)
    (MovingPair.leftBundle (memberEvaluation Q t))
  intro z
  have hx : (memberPoint Q t z).val ≫ parametrizedEvaluation Q =
      z.val ≫ memberEvaluation Q t := by
    simp only [memberPoint, Category.assoc, memberToParametrized_evaluation]
  have hz := (coordinatePair_evaluation Q (memberPoint Q t z)).trans hx
  apply (cancel_mono (compositionPullback z.val (memberEvaluation Q t)
    (z.val ≫ memberEvaluation Q t) rfl (movingPairBundleLeft X.variety X.contact)).hom).mp
  have ha := SectionTransport.pull_specialization z.val (memberToParametrized Q t)
    (parametrizedEvaluation Q) (memberPoint Q t z).val (memberEvaluation Q t)
    (z.val ≫ memberEvaluation Q t) rfl (memberToParametrized_evaluation Q t) rfl hx
    (left Q) _ rfl
  have hb := SectionTransport.pull_specialization z.val (Q.reducedMemberToSquare t)
    (curveSquareMap P (N.curveAt t)) (z.val ≫ Q.reducedMemberToSquare t)
    (memberEvaluation Q t) (z.val ≫ memberEvaluation Q t) rfl rfl rfl
    (Category.assoc _ _ _) (Curve.leftSection P X (N.curveAt t)) _ rfl
  rw [← ha, ← hb]
  have hp := point_left Q (memberPoint Q t z) (z.val ≫ memberEvaluation Q t) hx hz
  simpa only [memberPoint_coordinates, memberPoint_curve] using hp

theorem member_right :
    pullSection (memberToParametrized Q t) (right Q) ≫
      (compositionPullback (memberToParametrized Q t) (parametrizedEvaluation Q)
        (memberEvaluation Q t) (memberToParametrized_evaluation Q t)
        (movingPairBundleRight X.variety X.contact)).hom =
    pullSection (Q.reducedMemberToSquare t) (Curve.rightSection P X (N.curveAt t)) ≫
      (compositionPullback (Q.reducedMemberToSquare t) (curveSquareMap P (N.curveAt t))
        (memberEvaluation Q t) rfl (movingPairBundleRight X.variety X.contact)).hom := by
  letI : AlgebraicGeometry.IsReduced (Q.ReducedMemberCover t) :=
    Q.reducedMemberCover_reduced t
  letI : LocallyOfFiniteType (Q.reducedMemberToC t) :=
    Q.reducedMemberToC_locallyOfFiniteType t
  apply ComplexPointSectionDetection.section_eq (Q.reducedMemberToC t)
    (MovingPair.rightBundle (memberEvaluation Q t))
  intro z
  have hx : (memberPoint Q t z).val ≫ parametrizedEvaluation Q =
      z.val ≫ memberEvaluation Q t := by
    simp only [memberPoint, Category.assoc, memberToParametrized_evaluation]
  have hz := (coordinatePair_evaluation Q (memberPoint Q t z)).trans hx
  apply (cancel_mono (compositionPullback z.val (memberEvaluation Q t)
    (z.val ≫ memberEvaluation Q t) rfl (movingPairBundleRight X.variety X.contact)).hom).mp
  have ha := SectionTransport.pull_specialization z.val (memberToParametrized Q t)
    (parametrizedEvaluation Q) (memberPoint Q t z).val (memberEvaluation Q t)
    (z.val ≫ memberEvaluation Q t) rfl (memberToParametrized_evaluation Q t) rfl hx
    (right Q) _ rfl
  have hb := SectionTransport.pull_specialization z.val (Q.reducedMemberToSquare t)
    (curveSquareMap P (N.curveAt t)) (z.val ≫ Q.reducedMemberToSquare t)
    (memberEvaluation Q t) (z.val ≫ memberEvaluation Q t) rfl rfl rfl
    (Category.assoc _ _ _) (Curve.rightSection P X (N.curveAt t)) _ rfl
  rw [← ha, ← hb]
  have hp := point_right Q (memberPoint Q t z) (z.val ≫ memberEvaluation Q t) hx hz
  simpa only [memberPoint_coordinates, memberPoint_curve] using hp

theorem smoothLeft_member :
    pullSection (memberToSmooth Q t) (smoothLeft Q) ≫
      (compositionPullback (memberToSmooth Q t) (smoothEvaluation (F := F))
        (memberEvaluation Q t) (memberToSmooth_evaluation Q t)
        (movingPairBundleLeft X.variety X.contact)).hom =
    pullSection (Q.reducedMemberToSquare t) (Curve.leftSection P X (N.curveAt t)) ≫
      (compositionPullback (Q.reducedMemberToSquare t) (curveSquareMap P (N.curveAt t))
        (memberEvaluation Q t) rfl (movingPairBundleLeft X.variety X.contact)).hom := by
  rw [SectionTransport.pull_specialization (memberToParametrized Q t)
    Q.parametrizedSquareToSmooth (smoothEvaluation (F := F)) (memberToSmooth Q t)
    (parametrizedEvaluation Q) (memberEvaluation Q t) rfl (evaluation_commutes Q)
    (memberToParametrized_evaluation Q t) (memberToSmooth_evaluation Q t)
    (smoothLeft Q) (left Q) (smoothLeft_normalization Q)]
  exact member_left Q t

theorem smoothRight_member :
    pullSection (memberToSmooth Q t) (smoothRight Q) ≫
      (compositionPullback (memberToSmooth Q t) (smoothEvaluation (F := F))
        (memberEvaluation Q t) (memberToSmooth_evaluation Q t)
        (movingPairBundleRight X.variety X.contact)).hom =
    pullSection (Q.reducedMemberToSquare t) (Curve.rightSection P X (N.curveAt t)) ≫
      (compositionPullback (Q.reducedMemberToSquare t) (curveSquareMap P (N.curveAt t))
        (memberEvaluation Q t) rfl (movingPairBundleRight X.variety X.contact)).hom := by
  rw [SectionTransport.pull_specialization (memberToParametrized Q t)
    Q.parametrizedSquareToSmooth (smoothEvaluation (F := F)) (memberToSmooth Q t)
    (parametrizedEvaluation Q) (memberEvaluation Q t) rfl (evaluation_commutes Q)
    (memberToParametrized_evaluation Q t) (memberToSmooth_evaluation Q t)
    (smoothRight Q) (right Q) (smoothRight_normalization Q)]
  exact member_right Q t

theorem extension_left_member (E : (rationalPair Q).Extension) :
    pullSection (memberToFamily Q t) E.leftSection ≫
      (pullbackSquareIso (memberToFamily Q t) F.squareEvaluation
        (Q.reducedMemberToSquare t) (curveSquareMap P (N.curveAt t))
        (memberToFamily_evaluation Q t)
        (movingPairBundleLeft X.variety X.contact)).hom =
      pullSection (Q.reducedMemberToSquare t) (Curve.leftSection P X (N.curveAt t)) := by
  apply (cancel_mono (compositionPullback (Q.reducedMemberToSquare t)
    (curveSquareMap P (N.curveAt t)) (memberEvaluation Q t) rfl
    (movingPairBundleLeft X.variety X.contact)).hom).mp
  rw [Category.assoc, FlatSectionDescent.squareIso_comp_composition]
  rw [SectionTransport.pull_specialization (memberToSmooth Q t)
    F.smoothSquareOpen.ι F.squareEvaluation (memberToFamily Q t)
    (smoothEvaluation (F := F)) (memberEvaluation Q t) (memberToSmooth_ι Q t) rfl
    (memberToSmooth_evaluation Q t) (memberToFamily_evaluation Q t)
    E.leftSection (smoothLeft Q) (extension_left_smooth Q E)]
  exact smoothLeft_member Q t

theorem extension_right_member (E : (rationalPair Q).Extension) :
    pullSection (memberToFamily Q t) E.rightSection ≫
      (pullbackSquareIso (memberToFamily Q t) F.squareEvaluation
        (Q.reducedMemberToSquare t) (curveSquareMap P (N.curveAt t))
        (memberToFamily_evaluation Q t)
        (movingPairBundleRight X.variety X.contact)).hom =
      pullSection (Q.reducedMemberToSquare t) (Curve.rightSection P X (N.curveAt t)) := by
  apply (cancel_mono (compositionPullback (Q.reducedMemberToSquare t)
    (curveSquareMap P (N.curveAt t)) (memberEvaluation Q t) rfl
    (movingPairBundleRight X.variety X.contact)).hom).mp
  rw [Category.assoc, FlatSectionDescent.squareIso_comp_composition]
  rw [SectionTransport.pull_specialization (memberToSmooth Q t)
    F.smoothSquareOpen.ι F.squareEvaluation (memberToFamily Q t)
    (smoothEvaluation (F := F)) (memberEvaluation Q t) (memberToSmooth_ι Q t) rfl
    (memberToSmooth_evaluation Q t) (memberToFamily_evaluation Q t)
    E.rightSection (smoothRight Q) (extension_right_smooth Q E)]
  exact smoothRight_member Q t

/-- An actual extension yields the exact original covered-curve
comparison. The contact value is the original normalized source tensor. -/
def coveredComparison (E : (rationalPair Q).Extension)
    (hp : IsProper F.squareEvaluation)
    (hd : DenseRange (fun y : F.Square => F.squareEvaluation y)) :
    CoveredCurveComparison P X (E.properPair hp hd F.square_integralScheme) (N.curveAt t) where
  cover := Q.ReducedMemberCover t
  toSquare := Q.reducedMemberToSquare t
  proper := Q.reducedMemberToSquare_proper t
  surjective := Q.reducedMemberToSquare_surjective t
  toSource := memberToFamily Q t
  commutes := memberToFamily_evaluation Q t
  identity := by
    rw [E.properPair_value hp hd F.square_integralScheme, pullSection_naturality]
    simp only [Category.assoc]
    rw [pullbackSquare_naturality, ← Category.assoc, extension_left_member Q t E,
      ← pullSection_naturality, Curve.leftSection_contact]

/-- The original covered moving-pair output follows from extension of
the two rational sections. All full-family comparisons are constructed,
rather than added as a field of an auxiliary hypothesis package. -/
def coveredMovingPair (E : (rationalPair Q).Extension)
    (hd : DenseRange (fun y : F.Square => F.squareEvaluation y)) :
    CoveredMovingPair P p X g where
  properPair := E.properPair F.squareEvaluation_proper hd F.square_integralScheme
  fullFamily := N
  comparison := fun t => coveredComparison Q t E F.squareEvaluation_proper hd

end SmoothFamily

end LeBrunSalamon.Construction.FamilyBivectors

end
