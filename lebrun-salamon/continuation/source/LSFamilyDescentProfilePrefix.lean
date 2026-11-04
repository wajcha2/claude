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
set_option profiler true

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

run_cmd Lean.logInfo "DESCENT_STAGE_COMPLETED SectionTransport"

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

end RelativeSquare

run_cmd Lean.logInfo "DESCENT_STAGE_COMPLETED RelativeSquare"

-- Normalize the existing P1/contact carrier aliases for the same actual maps.
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety identityCurveContact intrinsicTangentBundle

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
  rw [leftSection, leftRaw]
  conv_lhs => rw [E.equation]
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
  rw [rightSection, rightRaw]
  conv_lhs => rw [E.equation]
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
  simp only [Category.assoc]
  erw [← RelativeSquare.comparison_naturality P.structureMap
    X.variety.structureMap (𝟙 ComplexBase) f.map
    (by simpa only [Category.comp_id] using f.overC)
    X.contact.sequence.form (𝟙 X.contact.sequence.line.sheaf)]
  rw [RelativeSquare.boxMap_comp_assoc]
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
  simp only [Category.assoc]
  erw [← RelativeSquare.comparison_naturality P.structureMap
    X.variety.structureMap (𝟙 ComplexBase) f.map
    (by simpa only [Category.comp_id] using f.overC)
    (𝟙 X.contact.sequence.line.sheaf) X.contact.sequence.form]
  rw [RelativeSquare.boxMap_comp_assoc]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

end Curve

run_cmd Lean.logInfo "DESCENT_STAGE_COMPLETED Curve"

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
  have hp (i : Fin E.size) :
      RelativeSquare.productSection (parameter P sB)
        (pullSection (projection P sB) (E.left i))
        (pullSection (projection P sB) (E.right i)) ≫ sourceComparison P sB =
      pullSection (sourceSquare P sB)
        (externalProductSection P.structureMap (E.left i) (E.right i)) :=
    RelativeSquare.comparison_onProducts (parameter P sB) P.structureMap sB
      (projection P sB) (pullback.condition (f := P.structureMap) (g := sB))
      (E.left i) (E.right i)
  have h := congrArg (fun a :
      AlgebraicSection (externalTensor P.structureMap
        (tangentSheaf P.structureMap) (tangentSheaf P.structureMap)) =>
    pullSection (sourceSquare P sB) a) E.equation
  rw [SectionTransport.pull_sum] at h
  apply (cancel_mono (sourceComparison P sB)).mp
  rw [bivector_comparison, Preadditive.sum_comp]
  exact h.trans (Finset.sum_congr rfl (fun i _ => (hp i).symm))

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

run_cmd Lean.logInfo "DESCENT_STAGE_COMPLETED Parametrized"

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
  simp only [Preadditive.sum_comp, RelativeSquare.productSection_map_assoc]
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
  simp only [Preadditive.sum_comp, RelativeSquare.productSection_map_assoc]
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

run_cmd Lean.logInfo "DESCENT_STAGE_COMPLETED ParametrizedContact"

namespace Reparametrization

variable (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
variable (he : e.hom ≫ P.structureMap = P.structureMap)

theorem mixedPull_product {E F : OModule ProjectiveLine}
    (a : AlgebraicSection E) (b : AlgebraicSection F) :
    mixedPull P e he E F (externalProductSection P.structureMap a b) =
      externalProductSection P.structureMap (pullSection e.hom a) (pullSection e.hom b) := by
  letI := curveExternalComparison_isIso P (curve P e he) E F
  apply (cancel_mono (curveExternalComparison P (curve P e he) E F)).mp
  rw [mixedPull_comparison]
  exact (curveExternalComparison_onProducts P (curve P e he) a b).symm

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
    rw [Curve.leftRaw]
    conv_lhs => rw [E.equation]
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
    rw [Curve.rightRaw]
    conv_lhs => rw [E.equation]
    simp only [Preadditive.sum_comp, externalProductSection, externalTensorMap,
      tensorSection_map, pullSection_naturality]
  rw [Curve.rightSection, compared_of_expansion P e he X f g hg
    (Curve.rightRaw P X f) _ _ hB, rightRaw P e he X f g hg]
  rfl

end Reparametrization

run_cmd Lean.logInfo "DESCENT_STAGE_COMPLETED Reparametrization"


end LeBrunSalamon.Construction.FamilyBivectors

end
