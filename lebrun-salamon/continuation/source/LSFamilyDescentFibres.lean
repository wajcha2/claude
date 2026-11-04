import LSFamilyDescentTransport

/-!
# Whole-source fibre specialization of the actual moving-pair tensors.

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
  exact RelativeSquare.sum_products_atCurve (Parametrized.parameter P sB)
    P X.variety sB e he j f hf (Parametrized.squareAtSection P sB b j hj₂)
    (Parametrized.squareAtSection_left P sB b j hj₂)
    (Parametrized.squareAtSection_right P sB b j hj₂)
    (Parametrized.squareAtSection_evaluation P sB X.variety e he b j hj₂ f hf)
    (E := tangentSheaf X.variety.structureMap)
    (F := X.contact.sequence.line.sheaf) (N := E.size)
    (fun i => Parametrized.vector P sB X.variety e he (E.left i))
    (fun i => contactVector P sB X e he (E.right i))
    (fun i => E.left i ≫ Curve.differential P X f)
    (fun i => E.right i ≫ curveContactVelocity P X.contact f)
    (leftSection P sB X e he) (Curve.leftSection P X f)
    (leftSection_expansion P sB X e he E) (Curve.leftSection_expansion P X f E)
    (fun i => Parametrized.vector_atCurve P sB X.variety e he b hb j hj₁ hj₂ f hf
      (E.left i))
    (fun i => contactVector_atCurve P sB X e he b hb j hj₁ hj₂ f hf (E.right i))

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
  exact RelativeSquare.sum_products_atCurve (Parametrized.parameter P sB)
    P X.variety sB e he j f hf (Parametrized.squareAtSection P sB b j hj₂)
    (Parametrized.squareAtSection_left P sB b j hj₂)
    (Parametrized.squareAtSection_right P sB b j hj₂)
    (Parametrized.squareAtSection_evaluation P sB X.variety e he b j hj₂ f hf)
    (E := X.contact.sequence.line.sheaf)
    (F := tangentSheaf X.variety.structureMap) (N := E.size)
    (fun i => contactVector P sB X e he (E.left i))
    (fun i => Parametrized.vector P sB X.variety e he (E.right i))
    (fun i => E.left i ≫ curveContactVelocity P X.contact f)
    (fun i => E.right i ≫ Curve.differential P X f)
    (rightSection P sB X e he) (Curve.rightSection P X f)
    (rightSection_expansion P sB X e he E) (Curve.rightSection_expansion P X f E)
    (fun i => contactVector_atCurve P sB X e he b hb j hj₁ hj₂ f hf (E.left i))
    (fun i => Parametrized.vector_atCurve P sB X.variety e he b hb j hj₁ hj₂ f hf
      (E.right i))

end ParametrizedContact

end LeBrunSalamon.Construction.FamilyBivectors

end
