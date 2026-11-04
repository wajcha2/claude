import RecompileExtensionsPart01
import LSVectorBundlePullback
import Mathlib.Algebra.Category.ModuleCat.Products

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


/- BEGIN UNCOMPILED continuation scalar_sections.lean.txt -/
/-!
Actual complex constants and local coefficients of algebraic sections.

Uncompiled continuation. Insert after the existing Skeleton namespace and
before Refinement. These equations use the original structure morphisms,
open restrictions and point lifts, including their actual unit comparisons.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Core LeBrunSalamon.Skeleton

namespace LeBrunSalamon.ScalarSections

/-- The complex constants on every actual open form the specified ring map. -/
def constantsOn {X : Scheme} (s : X ⟶ ComplexBase) (U : X.Opens) :
    ℂ →+* RingSections X U where
  toFun := complexConstant s U
  map_zero' := by simp [complexConstant]
  map_one' := by simp [complexConstant]
  map_add' a b := by simp [complexConstant]
  map_mul' a b := by simp [complexConstant]

/-- Constants are compatible with restriction in the original structure sheaf. -/
theorem complexConstant_restrict {X : Scheme} (s : X ⟶ ComplexBase)
    {U V : X.Opens} (i : V ⟶ U) (c : ℂ) :
    X.presheaf.map i.op (complexConstant s U c) = complexConstant s V c := by
  unfold complexConstant
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp] <;> rfl

/-- The top-section comparison for an open subscheme is the actual
restriction of global functions, including the equality of open images. -/
theorem topIso_inv_restrict {X : Scheme} (U : X.Opens) (a : RingSections X ⊤) :
    U.topIso.inv (X.presheaf.map (homOfLE le_top).op a) = U.ι.appTop a := by
  change (X.presheaf.map (homOfLE le_top).op ≫ U.topIso.inv) a = U.ι.appTop a
  simp only [Scheme.Opens.topIso_inv, ← Functor.map_comp, Scheme.Opens.ι_appTop] <;> rfl

/-- Evaluation through an actual point over C fixes every complex constant.
No coordinate choice or algebra structure on an abstract fiber is assumed. -/
theorem evaluate_complexConstant {X : Scheme} (s : X ⟶ ComplexBase)
    (U : X.Opens) (q : ComplexBase ⟶ U.toScheme)
    (hq : q ≫ U.ι ≫ s = 𝟙 ComplexBase) (c : ℂ) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        (q.appTop (U.topIso.inv (complexConstant s U c))) = c := by
  unfold complexConstant
  rw [topIso_inv_restrict]
  calc
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        (q.appTop (U.ι.appTop (s.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)))) =
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
          ((q ≫ U.ι ≫ s).appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) := by
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] <;> rfl
    _ = c := by
      rw [hq]
      exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of ℂ)) c

/-- Evaluating an O-linear section at 1 on an open is restriction of its
global value. This uses naturality of the original section morphism. -/
theorem section_app_one {X : Scheme} {E : OModule X}
    (a : AlgebraicSection E) (U : X.Opens) :
    Scheme.Modules.Hom.app a U (1 : RingSections X U) =
      E.presheaf.map (homOfLE le_top).op (sectionValue a) := by
  have h : E.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (Scheme.Modules.Hom.app a ⊤ (1 : RingSections X ⊤)) =
      Scheme.Modules.Hom.app a U (X.presheaf.map (homOfLE le_top).op (1 : RingSections X ⊤)) :=
    sheafHom_naturality a (homOfLE le_top) (1 : RingSections X ⊤)
  have hone : X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
      (1 : RingSections X ⊤) = (1 : RingSections X U) := map_one _
  rw [hone] at h
  exact h.symm

/-- The existing coefficient of an actual section is additive, without any
claim that the frame extends to a global trivialization. -/
def coefficientAddHom {X : Scheme} {L : LineBundle X} (F : AffineLineFrame L) :
    AlgebraicSection L.sheaf →+ RingSections X F.openSet where
  toFun := F.localCoefficient
  map_zero' := by
    change F.coefficient 0 = 0
    exact map_zero F.coefficient
  map_add' a b := by
    change F.coefficient (Scheme.Modules.Hom.app a F.openSet (1 : RingSections X F.openSet) + Scheme.Modules.Hom.app b F.openSet (1 : RingSections X F.openSet)) = _
    exact map_add F.coefficient _ _

end LeBrunSalamon.ScalarSections



end
/- END UNCOMPILED continuation scalar_sections.lean.txt -/

/-!
# Refinement -- boundary arithmetic, covered moving pairs, and diagonal stages

This namespace refines the largest remaining manuscript cut. `ProperPair` is a SCHEME-level specialization
of des:descent, not a definition of algebraic space. To use the manuscript's coarse space, a proper scheme
cover must be constructed and its full-family comparison pulled back; no lift of the family is assumed.
The scheme-cover bridge is justified classically by Chow's lemma (Stacks 088U), but that comparison has
NOT yet been formalized here. The new input packages have no admitted constructor. Their assembly uses
only explicit inputs. `by sorry` declarations below are obligations, not evidence.
-/
namespace LeBrunSalamon.Refinement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseTen
open LeBrunSalamon.PhaseTwentyOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFive LeBrunSalamon.Core LeBrunSalamon.Skeleton

/-! ## 1. Canonical pullback comparisons, required before transporting formulas -/

/-- Two paths in a commutative square induce this particular pullback
isomorphism, using mathlib's pullback composition and equality transport. -/
def pullbackSquareIso {T Y W Z : Scheme}
    (a : T ⟶ Y) (b : Y ⟶ Z) (c : T ⟶ W) (d : W ⟶ Z)
    (h : a ≫ b = c ≫ d) (E : OModule Z) :
    pullbackModule a (pullbackModule b E) ≅ pullbackModule c (pullbackModule d E) :=
  (Scheme.Modules.pullbackComp a b).app E ≪≫
    eqToIso (congrArg (fun f : T ⟶ Z => pullbackModule f E) h) ≪≫
      ((Scheme.Modules.pullbackComp c d).app E).symm


set_option backward.isDefEq.respectTransparency false in
theorem pullbackSquareIso_onSections {T Y W Z : Scheme}
    (a : T ⟶ Y) (b : Y ⟶ Z) (c : T ⟶ W) (d : W ⟶ Z)
    (h : a ≫ b = c ≫ d) {E : OModule Z} (s : AlgebraicSection E) :
    pullSection a (pullSection b s) ≫ (pullbackSquareIso a b c d h E).hom =
      pullSection c (pullSection d s) := by
  have he {f g : T ⟶ Z} (e : f = g) :
      pullSection f s ≫ eqToHom (congrArg (fun k : T ⟶ Z => pullbackModule k E) e) =
        pullSection g s := by
    subst g
    simp
  simp only [pullbackSquareIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
    Iso.app_hom, Iso.app_inv]
  rw [← Category.assoc, ← Category.assoc,
    CanonicalPullbackSectionProof.pullSection_comp, he h]
  rw [← CanonicalPullbackSectionProof.pullSection_comp c d s]
  simp


def curveSquareMap (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X) :
    SelfProduct P.structureMap ⟶ SelfProduct X.structureMap :=
  pullback.lift (firstProjection P.structureMap ≫ f.map)
    (secondProjection P.structureMap ≫ f.map) (by
      simpa only [Category.assoc, f.overC] using
        (pullback.condition (f := P.structureMap) (g := P.structureMap)))

theorem curveSquareMap_first (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X) :
    curveSquareMap P f ≫ firstProjection X.structureMap =
      firstProjection P.structureMap ≫ f.map := by
  exact pullback.lift_fst _ _ _

theorem curveSquareMap_second (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X) :
    curveSquareMap P f ≫ secondProjection X.structureMap =
      secondProjection P.structureMap ≫ f.map := by
  exact pullback.lift_snd _ _ _

/-- External-product base change with both projection comparisons fixed. -/
def curveExternalComparison (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X) (E F : OModule X.scheme) :
    externalTensor P.structureMap (pullbackModule f.map E) (pullbackModule f.map F) ⟶
      pullbackModule (curveSquareMap P f) (externalTensor X.structureMap E F) :=
  tensorMap
    (pullbackSquareIso (firstProjection P.structureMap) f.map
      (curveSquareMap P f) (firstProjection X.structureMap)
      (curveSquareMap_first P f).symm E).hom
    (pullbackSquareIso (secondProjection P.structureMap) f.map
      (curveSquareMap P f) (secondProjection X.structureMap)
      (curveSquareMap_second P f).symm F).hom ≫
  tensorPullbackComparison (curveSquareMap P f)
    (pullbackModule (firstProjection X.structureMap) E)
    (pullbackModule (secondProjection X.structureMap) F)

theorem curveExternalComparison_isIso (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X) (E F : OModule X.scheme) :
    IsIso (curveExternalComparison P f E F) := by
  let e := pullbackSquareIso (firstProjection P.structureMap) f.map
    (curveSquareMap P f) (firstProjection X.structureMap)
    (curveSquareMap_first P f).symm E
  let g := pullbackSquareIso (secondProjection P.structureMap) f.map
    (curveSquareMap P f) (secondProjection X.structureMap)
    (curveSquareMap_second P f).symm F
  letI := tensorPullbackComparison_isIso (curveSquareMap P f)
    (pullbackModule (firstProjection X.structureMap) E)
    (pullbackModule (secondProjection X.structureMap) F)
  change IsIso ((tensorIso e g).hom ≫
    tensorPullbackComparison (curveSquareMap P f)
      (pullbackModule (firstProjection X.structureMap) E)
      (pullbackModule (secondProjection X.structureMap) F))
  infer_instance


set_option backward.isDefEq.respectTransparency false in
theorem curveExternalComparison_onProducts (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X)
    {E F : OModule X.scheme} (a : AlgebraicSection E) (b : AlgebraicSection F) :
    externalProductSection P.structureMap (pullSection f.map a) (pullSection f.map b) ≫
      curveExternalComparison P f E F =
        pullSection (curveSquareMap P f) (externalProductSection X.structureMap a b) := by
  unfold externalProductSection curveExternalComparison
  rw [← Category.assoc, tensorSection_map,
    pullbackSquareIso_onSections, pullbackSquareIso_onSections,
    tensorPullbackComparison_onSections]


/-- Intrinsic source value, in the precise target of pullback along f x f. -/
def sourceContactValue (P : ProjectiveLineOverC) {n : ℕ}
    {X : SmoothProperComplexVariety (2*n+1)} (C : IntrinsicContactStructure X)
    (f : RationalCurve P X) : AlgebraicSection
      (pullbackModule (curveSquareMap P f)
        (externalSquareLine X.structureMap C.sequence.line).sheaf) :=
  sourceBivector P ≫ externalTensorMap P.structureMap
    (curveContactVelocity P C f) (curveContactVelocity P C f) ≫
      curveExternalComparison P f C.sequence.line.sheaf C.sequence.line.sheaf

set_option backward.isDefEq.respectTransparency false in
/-- Upgrades the finite-expansion formulation to a canonical sheaf equality. -/
theorem curveKernelIdentity_iff (P : ProjectiveLineOverC) {n : ℕ}
    {X : SmoothProperComplexVariety (2*n+1)} (C : IntrinsicContactStructure X)
    (f : RationalCurve P X) (B : ExternalSquareSections X C.sequence.line) :
    CurveKernelIdentity P C f B ↔
      pullSection (curveSquareMap P f) B = sourceContactValue P C f := by
  classical
  let q := curveExternalComparison P f C.sequence.line.sheaf C.sequence.line.sheaf
  have hsum (E : ExternalExpansion X C.sequence.line B) :
      (∑ i, externalProductSection P.structureMap
        (pullSection f.map (E.left i)) (pullSection f.map (E.right i))) ≫ q =
      pullSection (curveSquareMap P f) B := by
    dsimp only [q]
    rw [Preadditive.sum_comp]
    simp_rw [curveExternalComparison_onProducts]
    have h := congrArg
      (fun s : ExternalSquareSections X C.sequence.line =>
        pullSection (curveSquareMap P f) s) E.equation
    simpa only [pullSection, restrictSection, Functor.map_sum,
      Preadditive.comp_sum] using h.symm
  constructor
  · rintro ⟨E, hE⟩
    rw [← hsum E, hE]
    simp only [sourceContactValue, q, Category.assoc]
  · intro h
    obtain ⟨E⟩ := externalExpansion_exists X C.sequence.line B
    refine ⟨E, ?_⟩
    letI : IsIso q := curveExternalComparison_isIso P f
      C.sequence.line.sheaf C.sequence.line.sheaf
    apply (cancel_mono q).mp
    calc
      _ = pullSection (curveSquareMap P f) B := hsum E
      _ = sourceContactValue P C f := h
      _ = (sourceBivector P ≫ externalTensorMap P.structureMap
          (curveContactVelocity P C f) (curveContactVelocity P C f)) ≫ q := by
        simp only [sourceContactValue, q, Category.assoc]

section CurveExchangeProofSection

set_option backward.isDefEq.respectTransparency false

namespace CurveExchangeProof

/-- Exchange acts on a finite expansion by interchanging its actual
global factors; the section itself is transformed by the chosen normalized
external exchange map. -/
def exchangedExpansion {d : ℕ} {X : SmoothProperComplexVariety d}
    {L : LineBundle X.scheme} {B : ExternalSquareSections X L}
    (E : ExternalExpansion X L B) :
    ExternalExpansion X L
      ((chosenExternalExchange X.structureMap L).identification.swapSection B) where
  size := E.size
  left := E.right
  right := E.left
  equation := by
    let τ := chosenExternalExchange X.structureMap L
    let σ := ExchangeAlgebraProof.swapSectionAddHom τ.identification
    change σ B = ∑ i, externalProductSection X.structureMap (E.right i) (E.left i)
    have hsum := map_sum σ
      (fun i : Fin E.size =>
        externalProductSection X.structureMap (E.left i) (E.right i)) Finset.univ
    have hexch :
        (∑ i, σ (externalProductSection X.structureMap (E.left i) (E.right i))) =
          ∑ i, externalProductSection X.structureMap (E.right i) (E.left i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact τ.onProducts (E.left i) (E.right i)
    exact (congrArg σ E.equation).trans (hsum.trans hexch)

theorem externalTensorMap_product {Y : Scheme} (s : Y ⟶ ComplexBase)
    (L M : LineBundle Y) (q : L.sheaf ⟶ M.sheaf)
    (a b : AlgebraicSection L.sheaf) :
    externalProductSection s a b ≫ externalTensorMap s q q =
      externalProductSection s (a ≫ q) (b ≫ q) := by
  simp only [externalProductSection, externalTensorMap, tensorSection_map,
    ExternalExchangeCoherenceProof.pullSection_map]

/-- Naturality of external exchange for a line-bundle morphism, proved
on a genuine finite tensor expansion and the normalized pure products. -/
theorem exchange_map {d : ℕ} (X : SmoothProperComplexVariety d)
    (L M : LineBundle X.scheme) (q : L.sheaf ⟶ M.sheaf)
    (B : ExternalSquareSections X L) :
    (chosenExternalExchange X.structureMap M).identification.swapSection
        (B ≫ externalTensorMap X.structureMap q q) =
      (chosenExternalExchange X.structureMap L).identification.swapSection B ≫
        externalTensorMap X.structureMap q q := by
  obtain ⟨E⟩ := externalExpansion_exists X L B
  let σL := ExchangeAlgebraProof.swapSectionAddHom
    (chosenExternalExchange X.structureMap L).identification
  let σM := ExchangeAlgebraProof.swapSectionAddHom
    (chosenExternalExchange X.structureMap M).identification
  change σM (B ≫ externalTensorMap X.structureMap q q) =
    σL B ≫ externalTensorMap X.structureMap q q
  rw [E.equation, Preadditive.sum_comp, map_sum, map_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  change (chosenExternalExchange X.structureMap M).identification.swapSection
      (externalProductSection X.structureMap (E.left i) (E.right i) ≫
        externalTensorMap X.structureMap q q) =
    (chosenExternalExchange X.structureMap L).identification.swapSection
      (externalProductSection X.structureMap (E.left i) (E.right i)) ≫
        externalTensorMap X.structureMap q q
  rw [externalTensorMap_product,
    (chosenExternalExchange X.structureMap M).onProducts,
    (chosenExternalExchange X.structureMap L).onProducts,
    externalTensorMap_product]

theorem map_symmetric {d : ℕ} (X : SmoothProperComplexVariety d)
    (L M : LineBundle X.scheme) (q : L.sheaf ⟶ M.sheaf)
    (B : ExternalSquareSections X L)
    (hB : IsSymmetricExternalSection X.structureMap L B) :
    IsSymmetricExternalSection X.structureMap M
      (B ≫ externalTensorMap X.structureMap q q) := by
  change (chosenExternalExchange X.structureMap L).identification.swapSection B = B at hB
  change (chosenExternalExchange X.structureMap M).identification.swapSection
    (B ≫ externalTensorMap X.structureMap q q) = B ≫ externalTensorMap X.structureMap q q
  rw [exchange_map, hB]

/-- The source contact expression inherits the source bivector's symmetry
through the actual contact-velocity morphism in both tensor factors. -/
theorem sourceFormula_symmetric (P : ProjectiveLineOverC) {n : ℕ}
    {X : SmoothProperComplexVariety (2*n+1)} (C : IntrinsicContactStructure X)
    (f : RationalCurve P X) :
    IsSymmetricExternalSection P.structureMap (pullbackBundle f.map C.sequence.line)
      (sourceBivector P ≫ externalTensorMap P.structureMap
        (curveContactVelocity P C f) (curveContactVelocity P C f)) := by
  exact map_symmetric (projectiveLineVariety P)
    (identityCurveContact P).sequence.line (pullbackBundle f.map C.sequence.line)
    (curveContactVelocity P C f) (sourceBivector P)
    (Classical.choose_spec (sourceBivector_existsUnique P)).1.1

theorem curveKernelIdentity_exchange (P : ProjectiveLineOverC) {n : ℕ}
    {X : SmoothProperComplexVariety (2*n+1)} (C : IntrinsicContactStructure X)
    (f : RationalCurve P X) (B : ExternalSquareSections X C.sequence.line)
    (h : CurveKernelIdentity P C f B) :
    CurveKernelIdentity P C f
      ((chosenExternalExchange X.structureMap C.sequence.line).identification.swapSection B) := by
  obtain ⟨E, hE⟩ := h
  refine ⟨exchangedExpansion E, ?_⟩
  let M := pullbackBundle f.map C.sequence.line
  let σ := ExchangeAlgebraProof.swapSectionAddHom
    (chosenExternalExchange P.structureMap M).identification
  have he := congrArg σ hE
  rw [map_sum] at he
  have hprod (i : Fin E.size) :
      σ (externalProductSection P.structureMap
        (pullSection f.map (E.left i)) (pullSection f.map (E.right i))) =
      externalProductSection P.structureMap
        (pullSection f.map (E.right i)) (pullSection f.map (E.left i)) :=
    (chosenExternalExchange P.structureMap M).onProducts _ _
  simp_rw [hprod] at he
  exact he.trans (sourceFormula_symmetric P C f)

end CurveExchangeProof

end CurveExchangeProofSection



/-! ## 2. Scheme-cover formulation of ext:moving-pair and des:descent -/

/-- Properness and dominance are inherited from the intrinsic two-lift data. Integral source is NEW and
essential for the finite-image argument. No source normality, connected fibres, or f_*O=O is assumed. -/
structure ProperPair {n : ℕ} (X : ContactFanoManifold n) where
  pair : IntrinsicMovingPair X
  irreducible : IrreducibleSpace pair.data.source
  reduced : ∀ U : pair.data.source.Opens,
    IsReduced (RingSections pair.data.source U)

/-- Converts the old p*O-valued convention to an ordinary section on Y. -/
def ProperPair.value {n : ℕ} {X : ContactFanoManifold n} (D : ProperPair X) :
    AlgebraicSection (pullbackModule D.pair.data.projection
      (externalSquareLine X.variety.structureMap X.contact.sequence.line).sheaf) :=
  (unitPullbackIso D.pair.data.projection).inv ≫ D.pair.data.value

def ProperPair.DescendsTo {n : ℕ} {X : ContactFanoManifold n} (D : ProperPair X)
    (B : ExternalSquareSections X.variety X.contact.sequence.line) : Prop :=
  pullSection D.pair.data.projection B = D.value

theorem ProperPair.descendsTo_iff_legacy {n : ℕ} {X : ContactFanoManifold n}
    (D : ProperPair X) (B : ExternalSquareSections X.variety X.contact.sequence.line) :
    D.DescendsTo B ↔ restrictSection D.pair.data.projection B = D.pair.data.value := by
  change ((unitPullbackIso D.pair.data.projection).inv ≫
      restrictSection D.pair.data.projection B =
    (unitPullbackIso D.pair.data.projection).inv ≫ D.pair.data.value) ↔ _
  exact cancel_epi (unitPullbackIso D.pair.data.projection).inv


theorem ProperPair.descent_unique {n : ℕ} {X : ContactFanoManifold n}
    (D : ProperPair X) {B C : ExternalSquareSections X.variety X.contact.sequence.line}
    (hB : D.DescendsTo B) (hC : D.DescendsTo C) : B = C := by
  exact intrinsicMovingPair_descent_unique X D.pair B C
    ((ProperPair.descendsTo_iff_legacy D B).mp hB) ((ProperPair.descendsTo_iff_legacy D C).mp hC)

set_option maxHeartbeats 800000 in
/-- A proper surjective comparison OVER THE WHOLE P1 x P1. This includes
coincident source points. No section of the cover and no direct lift to Y is
required. The equality is an equality of sheaf sections, not of labels. -/
structure CoveredCurveComparison (P : ProjectiveLineOverC) {n : ℕ}
    (X : ContactFanoManifold n) (D : ProperPair X) (f : RationalCurve P X.variety) where
  cover : Scheme
  toSquare : cover ⟶ SelfProduct P.structureMap
  proper : IsProper toSquare
  surjective : Function.Surjective (fun z : cover => toSquare z)
  toSource : cover ⟶ D.pair.data.source
  commutes : toSource ≫ D.pair.data.projection = toSquare ≫ curveSquareMap P f
  identity : pullSection toSource D.value ≫
      (pullbackSquareIso toSource D.pair.data.projection toSquare (curveSquareMap P f)
        commutes (externalSquareLine X.variety.structureMap X.contact.sequence.line).sheaf).hom =
    pullSection toSquare (sourceContactValue P X.contact f)

/-- OUTPUT of extension/coarse-space passage and a JUSTIFIED scheme-cover
comparison. No kernel on X x X or descent conclusion is a field here. -/
structure CoveredMovingPair (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X) where
  properPair : ProperPair X
  fullFamily : FullConicNeighborhood P p X g
  comparison : ∀ t, CoveredCurveComparison P X properPair (fullFamily.curveAt t)

/-- Pullback of sections along the comparison cover is injective since
P1 x P1 is reduced and its target bundle is locally free. A proper surjection
is NOT asserted to be an effective descent morphism for arbitrary sections. -/
theorem coveredComparison_recovers_identity (P : ProjectiveLineOverC) {n : ℕ}
    (X : ContactFanoManifold n) (D : ProperPair X) (f : RationalCurve P X.variety)
    (Q : CoveredCurveComparison P X D f)
    (B : ExternalSquareSections X.variety X.contact.sequence.line) (hB : D.DescendsTo B) :
    CurveKernelIdentity P X.contact f B := by
  apply (curveKernelIdentity_iff P X.contact f B).2
  letI : Smooth P.structureMap := smoothProperComplexVariety_smooth (projectiveLineVariety P)
  letI : Smooth (firstProjection P.structureMap ≫ P.structureMap) := inferInstance
  letI : AlgebraicGeometry.IsReduced (SelfProduct P.structureMap) :=
    LeBrunSalamon.SchemeStandardInputs.smooth_complex_reduced
      (firstProjection P.structureMap ≫ P.structureMap)
  apply dominant_pullSection_injective Q.toSquare Q.surjective.denseRange
    (fun U => inferInstance)
    (pullbackBundle (curveSquareMap P f)
      (externalSquareLine X.variety.structureMap X.contact.sequence.line))
  change pullSection D.pair.data.projection B = D.value at hB
  calc
    pullSection Q.toSquare (pullSection (curveSquareMap P f) B) =
        pullSection Q.toSource (pullSection D.pair.data.projection B) ≫
          (pullbackSquareIso Q.toSource D.pair.data.projection Q.toSquare
            (curveSquareMap P f) Q.commutes
            (externalSquareLine X.variety.structureMap X.contact.sequence.line).sheaf).hom :=
      (pullbackSquareIso_onSections Q.toSource D.pair.data.projection Q.toSquare
        (curveSquareMap P f) Q.commutes B).symm
    _ = pullSection Q.toSquare (sourceContactValue P X.contact f) := by
      rw [hB]
      exact Q.identity


section ComplexPointSectionDetectionSection

set_option backward.isDefEq.respectTransparency false

namespace ComplexPointSectionDetection

/-- Complex points detect a regular function on a reduced scheme
locally of finite type over C. This uses the actual maps of sections at
the closed points supplied by Mathlib's algebraically-closed-field API. -/
theorem function_zero {Y : Scheme} (s : Y ⟶ ComplexBase)
    [LocallyOfFiniteType s] [AlgebraicGeometry.IsReduced Y]
    (a : RingSections Y ⊤)
    (ha : ∀ q : PointsOver ComplexBase (𝟙 ComplexBase) Y s,
      q.val.appTop a = 0) : a = 0 := by
  letI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace s
  apply AlgebraicGeometry.eq_zero_of_basicOpen_eq_bot a
  apply TopologicalSpace.Opens.ext
  apply Set.eq_empty_of_forall_notMem
  intro y hy
  have hd : Dense (closedPoints Y) := by
    rw [dense_iff_closure_eq, closure_closedPoints]
  obtain ⟨z, hz, hclosed⟩ := hd.inter_open_nonempty
    (Y.basicOpen a : Set Y) (Y.basicOpen a).isOpen ⟨y, hy⟩
  let q : PointsOver ComplexBase (𝟙 ComplexBase) Y s :=
    ⟨pointOfClosedPoint s z hclosed, pointOfClosedPoint_comp s z hclosed⟩
  have hp : q.val ⁻¹ᵁ Y.basicOpen a = ⊥ := by
    rw [Scheme.preimage_basicOpen_top, ha q]
    simp
  have hz' : q.val (IsLocalRing.closedPoint ℂ) ∈ Y.basicOpen a := by
    change q.val (IsLocalRing.closedPoint ℂ) ∈ (Y.basicOpen a : Set Y)
    simpa only [q, pointOfClosedPoint_apply] using hz
  have hmem : IsLocalRing.closedPoint ℂ ∈ q.val ⁻¹ᵁ Y.basicOpen a := hz'
  rw [hp] at hmem
  exact hmem

theorem unit_zero {Y : Scheme} (s : Y ⟶ ComplexBase)
    [LocallyOfFiniteType s] [AlgebraicGeometry.IsReduced Y]
    (a : AlgebraicSection (structureModule Y))
    (ha : ∀ q : PointsOver ComplexBase (𝟙 ComplexBase) Y s,
      (Scheme.Modules.pullback q.val).map a = 0) : a = 0 := by
  apply (sectionValue_bijective (structureModule Y)).1
  rw [sectionValue_zero]
  apply function_zero s
  intro q
  let adj := Scheme.Modules.pullbackPushforwardAdjunction q.val
  have hu : adj.homEquiv (structureModule Y) (structureModule ComplexBase)
      (unitPullbackMap q.val) = structurePushforwardMap q.val :=
    unitPullbackMap_adjoint q.val
  have hcomp : a ≫ structurePushforwardMap q.val = 0 := by
    have hn := adj.homEquiv_naturality_left a (unitPullbackMap q.val)
    rw [hu, ha q, zero_comp, adj.homAddEquiv_zero] at hn
    exact hn.symm
  have hvalue := congrArg
    (fun k : structureModule Y ⟶
        (Scheme.Modules.pushforward q.val).obj (structureModule ComplexBase) =>
      k.app ⊤ (1 : RingSections Y ⊤)) hcomp
  change q.val.appTop (sectionValue a) = 0 at hvalue
  exact hvalue

theorem free_zero {Y : Scheme} (s : Y ⟶ ComplexBase)
    [LocallyOfFiniteType s] [AlgebraicGeometry.IsReduced Y]
    {E : OModule Y} {r : ℕ}
    (e : SheafOfModules.free (R := Y.ringCatSheaf) (Fin r) ≅ E)
    (a : AlgebraicSection E)
    (ha : ∀ q : PointsOver ComplexBase (𝟙 ComplexBase) Y s,
      (Scheme.Modules.pullback q.val).map a = 0) : a = 0 := by
  let P : Fin r → OModule Y := fun _ => structureModule Y
  letI : HasBiproduct P := HasBiproduct.of_hasCoproduct P
  let eP : SheafOfModules.free (R := Y.ringCatSheaf) (Fin r) ≅ ∏ᶜ P :=
    (biproductIso P).symm
  apply (cancel_mono e.inv).1
  apply (cancel_mono eP.hom).1
  simp only [zero_comp]
  apply Pi.hom_ext
  intro i
  rw [zero_comp]
  apply unit_zero s
  intro q
  simp only [Functor.map_comp, ha q, zero_comp]

/-- Local free coordinates reduce section detection to regular
functions. Restriction to each open and then each complex point uses the
actual pullback composition comparison, including its unit maps. -/
theorem locallyFree_zero {Y : Scheme} (s : Y ⟶ ComplexBase)
    [LocallyOfFiniteType s] [AlgebraicGeometry.IsReduced Y]
    {E : OModule Y} {r : ℕ} (hE : IsLocallyFreeOfRank E r)
    (a : AlgebraicSection E)
    (ha : ∀ q : PointsOver ComplexBase (𝟙 ComplexBase) Y s,
      (Scheme.Modules.pullback q.val).map a = 0) : a = 0 := by
  obtain ⟨q, hq, hr⟩ := hE
  letI := hq
  have hopen : ∀ i : q.I,
      (Scheme.Modules.pullback (Scheme.Opens.ι (X := Y) (q.X i))).map a = 0 := by
    intro i
    let U : Y.Opens := q.X i
    have hlocal : pullSection U.ι a = 0 := by
      apply free_zero (U.ι ≫ s)
        (DominantSectionInjectivityProof.localFreePullbackIso q hr i)
      intro z
      let zY : PointsOver ComplexBase (𝟙 ComplexBase) Y s :=
        ⟨z.val ≫ U.ι, by simpa only [Category.assoc] using z.property⟩
      have hcomp : (Scheme.Modules.pullback (z.val ≫ U.ι)).map a = 0 := ha zY
      have hiter :=
        (LeBrunSalamon.PhaseFourteen.SliceRestrictionProof.pullback_comp_zero_iff
          z.val U.ι a).mp hcomp
      change (Scheme.Modules.pullback z.val).map
        ((unitPullbackIso U.ι).inv ≫ (Scheme.Modules.pullback U.ι).map a) = 0
      rw [Functor.map_comp, hiter, comp_zero]
    have hunit := unitPullbackMap_pullSection U.ι a
    rw [hlocal, comp_zero] at hunit
    exact hunit.symm
  apply (sectionValue_bijective E).1
  rw [sectionValue_zero]
  let S : TopCat.Sheaf AddCommGrpCat Y :=
    (SheafOfModules.toSheaf Y.ringCatSheaf).obj E
  have hcover : iSup q.X = ⊤ := (_root_.Opens.coversTop_iff Y q.X).mp q.coversTop
  apply TopCat.Sheaf.eq_of_locally_eq' S q.X ⊤
    (fun i => (q.X i).leTop) (by rw [hcover])
  intro i
  have ho := DominantSectionInjectivityProof.over_zero_of_pullback_zero
    (q.X i) a (hopen i)
  have hvalue := congrArg
    (fun k : (structureModule Y).over (q.X i) ⟶ E.over (q.X i) =>
      k.val.app (Opposite.op (Over.mk (𝟙 (q.X i)))) (1 : RingSections Y (q.X i))) ho
  change (Scheme.Modules.Hom.app a (q.X i)) (1 : RingSections Y (q.X i)) = 0 at hvalue
  change E.presheaf.map (homOfLE le_top).op (sectionValue a) =
    E.presheaf.map (homOfLE le_top).op 0
  rw [sectionValue, sheafHom_naturality]
  change (Scheme.Modules.Hom.app a (q.X i))
      (Y.presheaf.map (homOfLE le_top).op (1 : RingSections Y ⊤)) =
    E.presheaf.map (homOfLE le_top).op 0
  rw [map_one, map_zero]
  exact hvalue

theorem section_eq {Y : Scheme} (s : Y ⟶ ComplexBase)
    [LocallyOfFiniteType s] [AlgebraicGeometry.IsReduced Y]
    {r : ℕ} (E : AlgebraicVectorBundle Y r) (a b : AlgebraicSection E.sheaf)
    (h : ∀ q : PointsOver ComplexBase (𝟙 ComplexBase) Y s,
      pullSection q.val a = pullSection q.val b) : a = b := by
  apply sub_eq_zero.mp
  apply locallyFree_zero s E.locallyFree (a - b)
  intro q
  have hq := congrArg (fun t => unitPullbackMap q.val ≫ t) (h q)
  rw [unitPullbackMap_pullSection, unitPullbackMap_pullSection] at hq
  rw [Functor.map_sub, hq, sub_self]

end ComplexPointSectionDetection

end ComplexPointSectionDetectionSection

namespace HomTwoPointEvaluation

/-- The structure map on the actual ordered pair of source points. -/
abbrev squareStructure (P : ProjectiveLineOverC) :
    SelfProduct P.structureMap ⟶ ComplexBase :=
  firstProjection P.structureMap ≫ P.structureMap

/-- The source is the product of the source square with the specified
open of the representing Hom scheme. -/
abbrev Source (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H : HomSpacePresentation P X)
    (U : H.parameter.Opens) : Scheme :=
  pullback (squareStructure P) (U.ι ≫ H.toC)

abbrev structureMap (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H : HomSpacePresentation P X)
    (U : H.parameter.Opens) : Source P H U ⟶ ComplexBase :=
  pullback.snd (squareStructure P) (U.ι ≫ H.toC) ≫ U.ι ≫ H.toC

/-- The first point and the unchanged parameter in the original
universal evaluation family. -/
def leftSource (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H : HomSpacePresentation P X)
    (U : H.parameter.Opens) :
    Source P H U ⟶ RationalSourceOver P H.parameter H.toC :=
  pullback.lift
    (pullback.fst (squareStructure P) (U.ι ≫ H.toC) ≫
      firstProjection P.structureMap)
    (pullback.snd (squareStructure P) (U.ι ≫ H.toC) ≫ U.ι) (by
      simpa only [squareStructure, Category.assoc] using
        (pullback.condition (f := squareStructure P) (g := U.ι ≫ H.toC)))

/-- The second point and the same parameter in the universal family. -/
def rightSource (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H : HomSpacePresentation P X)
    (U : H.parameter.Opens) :
    Source P H U ⟶ RationalSourceOver P H.parameter H.toC :=
  pullback.lift
    (pullback.fst (squareStructure P) (U.ι ≫ H.toC) ≫
      secondProjection P.structureMap)
    (pullback.snd (squareStructure P) (U.ι ≫ H.toC) ≫ U.ι) (by
      calc
        _ = pullback.fst (squareStructure P) (U.ι ≫ H.toC) ≫
            squareStructure P := by
          simpa only [squareStructure, Category.assoc] using
            congrArg (fun k => pullback.fst (squareStructure P) (U.ι ≫ H.toC) ≫ k)
              (pullback.condition (f := P.structureMap) (g := P.structureMap)).symm
        _ = _ := by
          simpa only [Category.assoc] using
            (pullback.condition (f := squareStructure P) (g := U.ι ≫ H.toC)))

/-- The actual universal two-point evaluation, with both factors
computed by the given representing family's evaluation morphism. -/
def evaluation (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H : HomSpacePresentation P X)
    (U : H.parameter.Opens) : Source P H U ⟶ SelfProduct X.structureMap :=
  pullback.lift (leftSource P H U ≫ H.evaluation)
    (rightSource P H U ≫ H.evaluation) (by
      simp only [leftSource, rightSource, Category.assoc, H.overC,
        pullback.lift_fst_assoc]
      simpa only [Category.assoc] using
        congrArg (fun k => pullback.fst (squareStructure P) (U.ι ≫ H.toC) ≫ k)
          (pullback.condition (f := P.structureMap) (g := P.structureMap)))

theorem evaluation_first (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H : HomSpacePresentation P X)
    (U : H.parameter.Opens) :
    evaluation P H U ≫ firstProjection X.structureMap =
      leftSource P H U ≫ H.evaluation :=
  pullback.lift_fst _ _ _

theorem evaluation_second (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H : HomSpacePresentation P X)
    (U : H.parameter.Opens) :
    evaluation P H U ≫ secondProjection X.structureMap =
      rightSource P H U ≫ H.evaluation :=
  pullback.lift_snd _ _ _

def parameterPoint (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H : HomSpacePresentation P X)
    (U : H.parameter.Opens)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ H.toC)) :
    PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC :=
  ⟨t.val ≫ U.ι, by simpa only [Category.assoc] using t.property⟩

/-- Inclusion of the whole source square over the chosen complex
parameter, including coincident source points. -/
def fiberInclusion (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H : HomSpacePresentation P X)
    (U : H.parameter.Opens)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ H.toC)) :
    SelfProduct P.structureMap ⟶ Source P H U :=
  pullback.lift (𝟙 _) (squareStructure P ≫ t.val) (by
    simp only [Category.id_comp, Category.assoc, t.property, Category.comp_id])

theorem fiberInclusion_left_evaluation (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H : HomSpacePresentation P X)
    (U : H.parameter.Opens)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ H.toC)) :
    fiberInclusion P H U t ≫ leftSource P H U ≫ H.evaluation =
      firstProjection P.structureMap ≫ H.mapAt P (parameterPoint P H U t) := by
  let k : ProjectiveLine ⟶ RationalSourceOver P H.parameter H.toC :=
    pullback.lift (𝟙 _) (P.structureMap ≫ (parameterPoint P H U t).val) (by
      simp only [Category.id_comp, Category.assoc,
        (parameterPoint P H U t).property, Category.comp_id])
  have hk : fiberInclusion P H U t ≫ leftSource P H U =
      firstProjection P.structureMap ≫ k := by
    apply pullback.hom_ext
    · simp only [fiberInclusion, leftSource, k, Category.assoc,
        pullback.lift_fst_assoc, pullback.lift_fst,
        Category.id_comp, Category.comp_id]
    · simp only [fiberInclusion, leftSource, k, parameterPoint,
        squareStructure, Category.assoc, pullback.lift_snd_assoc,
        pullback.lift_snd]
  simpa only [k, HomSpacePresentation.mapAt, Category.assoc] using
    congrArg (fun m => m ≫ H.evaluation) hk

theorem fiberInclusion_right_evaluation (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H : HomSpacePresentation P X)
    (U : H.parameter.Opens)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ H.toC)) :
    fiberInclusion P H U t ≫ rightSource P H U ≫ H.evaluation =
      secondProjection P.structureMap ≫ H.mapAt P (parameterPoint P H U t) := by
  let k : ProjectiveLine ⟶ RationalSourceOver P H.parameter H.toC :=
    pullback.lift (𝟙 _) (P.structureMap ≫ (parameterPoint P H U t).val) (by
      simp only [Category.id_comp, Category.assoc,
        (parameterPoint P H U t).property, Category.comp_id])
  have hk : fiberInclusion P H U t ≫ rightSource P H U =
      secondProjection P.structureMap ≫ k := by
    apply pullback.hom_ext
    · simp only [fiberInclusion, rightSource, k, Category.assoc,
        pullback.lift_fst_assoc, pullback.lift_fst,
        Category.id_comp, Category.comp_id]
    · simp only [fiberInclusion, rightSource, k, parameterPoint,
        squareStructure, Category.assoc, pullback.lift_snd_assoc,
        pullback.lift_snd]
      simpa only [Category.assoc] using
        congrArg (fun m => m ≫ t.val ≫ U.ι)
          (pullback.condition (f := P.structureMap) (g := P.structureMap))
  simpa only [k, HomSpacePresentation.mapAt, Category.assoc] using
    congrArg (fun m => m ≫ H.evaluation) hk

/-- On every actual parameter fibre, universal two-point evaluation is
the original curve-square morphism, with both projection equations fixed. -/
theorem fiberInclusion_evaluation (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H : HomSpacePresentation P X)
    (U : H.parameter.Opens)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ H.toC))
    (f : RationalCurve P X) (hf : f.map = H.mapAt P (parameterPoint P H U t)) :
    fiberInclusion P H U t ≫ evaluation P H U = curveSquareMap P f := by
  apply pullback.hom_ext
  · calc
      (fiberInclusion P H U t ≫ evaluation P H U) ≫ firstProjection X.structureMap =
          fiberInclusion P H U t ≫ leftSource P H U ≫ H.evaluation := by
            rw [Category.assoc, evaluation_first]
      _ = firstProjection P.structureMap ≫ H.mapAt P (parameterPoint P H U t) :=
        fiberInclusion_left_evaluation P H U t
      _ = curveSquareMap P f ≫ firstProjection X.structureMap := by
        rw [← hf, curveSquareMap_first]
  · calc
      (fiberInclusion P H U t ≫ evaluation P H U) ≫ secondProjection X.structureMap =
          fiberInclusion P H U t ≫ rightSource P H U ≫ H.evaluation := by
            rw [Category.assoc, evaluation_second]
      _ = secondProjection P.structureMap ≫ H.mapAt P (parameterPoint P H U t) :=
        fiberInclusion_right_evaluation P H U t
      _ = curveSquareMap P f ≫ secondProjection X.structureMap := by
        rw [← hf, curveSquareMap_second]

def pointParameter (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H : HomSpacePresentation P X)
    (U : H.parameter.Opens)
    (q : PointsOver ComplexBase (𝟙 ComplexBase) (Source P H U) (structureMap P H U)) :
    PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ H.toC) :=
  ⟨q.val ≫ pullback.snd (squareStructure P) (U.ι ≫ H.toC), by
    simpa only [structureMap, Category.assoc] using q.property⟩

/-- Every complex point of the total source lies on its actual
parameter fibre. This is a categorical pullback identity, not an
assumption about geometric fibres. -/
theorem point_factorization (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H : HomSpacePresentation P X)
    (U : H.parameter.Opens)
    (q : PointsOver ComplexBase (𝟙 ComplexBase) (Source P H U) (structureMap P H U)) :
    (q.val ≫ pullback.fst (squareStructure P) (U.ι ≫ H.toC)) ≫
      fiberInclusion P H U (pointParameter P H U q) = q.val := by
  have hb : (q.val ≫ pullback.fst (squareStructure P) (U.ι ≫ H.toC)) ≫
      squareStructure P = 𝟙 ComplexBase := by
    calc
      _ = q.val ≫ structureMap P H U := by
        rw [Category.assoc, pullback.condition]
      _ = _ := q.property
  apply pullback.hom_ext
  · simp only [fiberInclusion, Category.assoc, pullback.lift_fst_assoc,
      pullback.lift_fst, Category.comp_id]
  · simp only [fiberInclusion, Category.assoc, pullback.lift_snd_assoc,
      pullback.lift_snd]
    simpa only [squareStructure, pointParameter, Category.assoc, Category.id_comp] using
      congrArg (fun k : ComplexBase ⟶ ComplexBase =>
        k ≫ (pointParameter P H U q).val) hb

theorem source_smooth (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H : HomSpacePresentation P X)
    (U : H.parameter.Opens) (hU : Smooth (U.ι ≫ H.toC)) :
    Smooth (structureMap P H U) := by
  letI : Smooth P.structureMap := smoothProperComplexVariety_smooth (projectiveLineVariety P)
  letI : Smooth (squareStructure P) := inferInstance
  letI : Smooth (U.ι ≫ H.toC) := hU
  change Smooth (pullback.snd (squareStructure P) (U.ι ≫ H.toC) ≫ (U.ι ≫ H.toC))
  infer_instance

end HomTwoPointEvaluation

open LeBrunSalamon.PhaseSeven in
/-- Kollár, Rational Curves on Algebraic Varieties II.3.5; explicit
two-point version in Gounelas, Free Curves on Varieties,
Documenta Mathematica 21 (2016), Proposition 4.7, p.299.
The source and map are the actual P1-square times the Hom open and
the given universal evaluation, not a contact or section detector. -/
theorem _root_.LeBrunSalamon.StandardInputs.homOpen_twoPointEvaluation_dominant
    (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) (H : HomSpacePresentation P X)
    (U : H.parameter.Opens) (hU : Smooth (U.ι ≫ H.toC))
    (t : PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ H.toC))
    (f : RationalCurve P X)
    (hf : f.map = H.mapAt P
      ⟨t.val ≫ U.ι, by simpa only [Category.assoc] using t.property⟩)
    (hfree : IsVeryFreeRationalCurve P X (intrinsicTangentBundle X) f) :
    DenseRange (Refinement.HomTwoPointEvaluation.evaluation P H U).base := by
  sorry

/-- The actual full Hom family detects sections of any finite-rank
bundle on the target square, through its universal two-point evaluation. -/
theorem fullFamily_detects_bundle_section (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X)
    (H : FullConicNeighborhood P p X g) {r : ℕ}
    (L : AlgebraicVectorBundle (SelfProduct X.variety.structureMap) r)
    (B C : AlgebraicSection L.sheaf)
    (h : ∀ t, pullSection (curveSquareMap P (H.curveAt t)) B =
      pullSection (curveSquareMap P (H.curveAt t)) C) : B = C := by
  let Z := HomTwoPointEvaluation.Source P H.homSpace H.neighborhood
  let s : Z ⟶ ComplexBase :=
    HomTwoPointEvaluation.structureMap P H.homSpace H.neighborhood
  let e : Z ⟶ SelfProduct X.variety.structureMap :=
    HomTwoPointEvaluation.evaluation P H.homSpace H.neighborhood
  letI : Smooth s := HomTwoPointEvaluation.source_smooth P H.homSpace H.neighborhood H.smooth
  letI : AlgebraicGeometry.IsReduced Z :=
    LeBrunSalamon.SchemeStandardInputs.smooth_complex_reduced s
  letI : Smooth (firstProjection X.variety.structureMap ≫ X.variety.structureMap) :=
    inferInstance
  letI : AlgebraicGeometry.IsReduced (SelfProduct X.variety.structureMap) :=
    LeBrunSalamon.SchemeStandardInputs.smooth_complex_reduced
      (firstProjection X.variety.structureMap ≫ X.variety.structureMap)
  have he : DenseRange e.base :=
    LeBrunSalamon.StandardInputs.homOpen_twoPointEvaluation_dominant P X.variety
      H.homSpace H.neighborhood H.smooth H.marked (H.curveAt H.marked)
      (H.curveAt_spec H.marked) (H.veryFree H.marked)
  apply dominant_pullSection_injective e he (fun U => inferInstance) L
  apply ComplexPointSectionDetection.section_eq s (pullbackBundle e L)
  intro q
  let t := HomTwoPointEvaluation.pointParameter P H.homSpace H.neighborhood q
  let z : ComplexBase ⟶ SelfProduct P.structureMap :=
    q.val ≫ pullback.fst (HomTwoPointEvaluation.squareStructure P)
      (H.neighborhood.ι ≫ H.homSpace.toC)
  have hF : HomTwoPointEvaluation.fiberInclusion P H.homSpace H.neighborhood t ≫ e =
      curveSquareMap P (H.curveAt t) :=
    HomTwoPointEvaluation.fiberInclusion_evaluation P H.homSpace H.neighborhood t
      (H.curveAt t) (H.curveAt_spec t)
  have hq : z ≫ HomTwoPointEvaluation.fiberInclusion P H.homSpace H.neighborhood t = q.val :=
    HomTwoPointEvaluation.point_factorization P H.homSpace H.neighborhood q
  have hsquare : z ≫ curveSquareMap P (H.curveAt t) = q.val ≫ e := by
    rw [← hF, ← Category.assoc, hq]
  calc
    pullSection q.val (pullSection e B) =
        pullSection z (pullSection (curveSquareMap P (H.curveAt t)) B) ≫
          (pullbackSquareIso z (curveSquareMap P (H.curveAt t)) q.val e hsquare L.sheaf).hom :=
      (pullbackSquareIso_onSections z (curveSquareMap P (H.curveAt t)) q.val e hsquare B).symm
    _ = pullSection z (pullSection (curveSquareMap P (H.curveAt t)) C) ≫
          (pullbackSquareIso z (curveSquareMap P (H.curveAt t)) q.val e hsquare L.sheaf).hom := by
      rw [h t]
    _ = pullSection q.val (pullSection e C) :=
      pullbackSquareIso_onSections z (curveSquareMap P (H.curveAt t)) q.val e hsquare C


/-- Very-freeness and FULLNESS of the open Hom family imply that its
moving-pair evaluation is dominant. Thus its curve-square tests detect a
section on X x X. This is false for an arbitrary single chosen curve. -/
theorem fullFamily_detects_section (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X)
    (H : FullConicNeighborhood P p X g)
    (B C : ExternalSquareSections X.variety X.contact.sequence.line)
    (h : ∀ t, pullSection (curveSquareMap P (H.curveAt t)) B =
      pullSection (curveSquareMap P (H.curveAt t)) C) : B = C := by
  exact fullFamily_detects_bundle_section P p X g H
    (externalSquareLine X.variety.structureMap X.contact.sequence.line) B C h

/-- Symmetry may be recovered from the symmetric source formula on the full family. This avoids demanding
that a chosen scheme cover lift the coarse-space involution. Source: ext:bivector and des:family. -/
theorem fullFamilyIdentity_symmetric (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X)
    (H : FullConicNeighborhood P p X g)
    (B : ExternalSquareSections X.variety X.contact.sequence.line)
    (h : ∀ t, CurveKernelIdentity P X.contact (H.curveAt t) B) :
    IsSymmetricExternalSection X.variety.structureMap X.contact.sequence.line B := by
  change (chosenExternalExchange X.variety.structureMap X.contact.sequence.line).identification.swapSection
    B = B
  apply fullFamily_detects_section P p X g H
  intro t
  have he := CurveExchangeProof.curveKernelIdentity_exchange P X.contact (H.curveAt t) B (h t)
  exact ((curveKernelIdentity_iff P X.contact (H.curveAt t) _).mp he).trans
    ((curveKernelIdentity_iff P X.contact (H.curveAt t) B).mp (h t)).symm

/-- Independent proper-source choices produce the same kernel when tested
on the SAME full neighborhood; no global uniqueness of normalized kernels
is asserted. Higher-order terms need not be fixed by the quadratic symbol. -/
theorem fullFamilyKernel_unique (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X)
    (H : FullConicNeighborhood P p X g)
    (B C : ExternalSquareSections X.variety X.contact.sequence.line)
    (hB : ∀ t, CurveKernelIdentity P X.contact (H.curveAt t) B)
    (hC : ∀ t, CurveKernelIdentity P X.contact (H.curveAt t) C) : B = C := by
  apply fullFamily_detects_section P p X g H B C
  intro t
  exact ((curveKernelIdentity_iff P X.contact (H.curveAt t) B).mp (hB t)).trans
    (((curveKernelIdentity_iff P X.contact (H.curveAt t) C).mp (hC t)).symm)

/-- These four proof slots replace one opaque MovingPairAndDescent slot.
No constructor is admitted. The last two slots are classical comparison
lemmas; the first two carry the manuscript's construction and descent. -/
structure MovingPairInputs (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) : Prop where
  construction : ∀ (n : ℕ) (X : ContactFanoManifold n), HasPrimitiveContactPicard X.contact →
    ∀ g : VeryFreeContactConic P p X, Nonempty (CoveredMovingPair P p X g)
  descent : ∀ (n : ℕ) (X : ContactFanoManifold n), HasPrimitiveContactPicard X.contact →
    ∀ D : ProperPair X, ∃! B, D.DescendsTo B
  recoverIdentity : ∀ (n : ℕ) (X : ContactFanoManifold n) (D : ProperPair X)
    (f : RationalCurve P X.variety) (Q : CoveredCurveComparison P X D f)
    (B : ExternalSquareSections X.variety X.contact.sequence.line),
    D.DescendsTo B → CurveKernelIdentity P X.contact f B
  recoverSymmetry : ∀ (n : ℕ) (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X)
    (H : FullConicNeighborhood P p X g)
    (B : ExternalSquareSections X.variety X.contact.sequence.line),
    (∀ t, CurveKernelIdentity P X.contact (H.curveAt t) B) →
    IsSymmetricExternalSection X.variety.structureMap X.contact.sequence.line B

/-- Actual forward assembly. It calls no admitted contact-descent theorem:
all four assertions are supplied as explicit inputs. -/
theorem MovingPairInputs.assemble (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (H : MovingPairInputs P p) : MovingPairAndDescent P p := by
  intro n X hp g
  obtain ⟨D⟩ := H.construction n X hp g
  obtain ⟨B, hB, _⟩ := H.descent n X hp D.properPair
  have hIdentity : ∀ t, CurveKernelIdentity P X.contact (D.fullFamily.curveAt t) B := by
    intro t
    exact H.recoverIdentity n X D.properPair (D.fullFamily.curveAt t) (D.comparison t) B hB
  exact ⟨⟨D.fullFamily, B, H.recoverSymmetry n X g D.fullFamily B hIdentity, hIdentity⟩⟩

/-! ## 3. Three ordered diagonal obligations; acceleration cannot be dropped early -/

abbrev FamilyKernel (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X) :=
  FullFamilyKernel P p X g

def FamilyKernel.HasZeroValue (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} {X : ContactFanoManifold n} {g : VeryFreeContactConic P p X}
    (D : FamilyKernel P p X g) : Prop :=
  VanishesToOrderAlongDiagonal X.variety.structureMap
    (externalSquareLine X.variety.structureMap X.contact.sequence.line).sheaf D.kernel 1

def FamilyKernel.HasZeroFirstSymbol (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} {X : ContactFanoManifold n} {g : VeryFreeContactConic P p X}
    (D : FamilyKernel P p X g) : Prop :=
  VanishesQuadraticallyAlongDiagonal X.variety.structureMap
    (externalSquareLine X.variety.structureMap X.contact.sequence.line).sheaf D.kernel

namespace FullFamilyDiagonalProof

@[simp] theorem pullSection_zero {Y Z : Scheme} (f : Y ⟶ Z) {E : OModule Z} :
    pullSection f (0 : AlgebraicSection E) = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    change (unitPullbackIso f).inv ≫
      (Scheme.Modules.pullback f).map (0 : structureModule Z ⟶ E) = 0
    exact (congrArg
      (fun b : pullbackModule f (structureModule Z) ⟶ pullbackModule f E =>
        (unitPullbackIso f).inv ≫ b)
      ((Scheme.Modules.pullback f).map_zero (structureModule Z) E)).trans
        (HasZeroMorphisms.comp_zero (unitPullbackIso f).inv (pullbackModule f E))

theorem pullSection_zero_iff {Y Z : Scheme} (f : Y ⟶ Z)
    {E : OModule Z} (a : AlgebraicSection E) :
    pullSection f a = 0 ↔ (Scheme.Modules.pullback f).map a = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    constructor
    · intro h
      exact (unitPullbackMap_pullSection f a).symm.trans
        ((congrArg (fun b : AlgebraicSection (pullbackModule f E) =>
          unitPullbackMap f ≫ b) h).trans
            (HasZeroMorphisms.comp_zero (unitPullbackMap f) (pullbackModule f E)))
    · intro h
      change (unitPullbackIso f).inv ≫ (Scheme.Modules.pullback f).map a = 0
      exact (congrArg
        (fun b : pullbackModule f (structureModule Z) ⟶ pullbackModule f E =>
          (unitPullbackIso f).inv ≫ b) h).trans
            (HasZeroMorphisms.comp_zero (unitPullbackIso f).inv (pullbackModule f E))

theorem pullSection_comp_zero_iff {T Y Z : Scheme} (f : T ⟶ Y) (g : Y ⟶ Z)
    {E : OModule Z} (a : AlgebraicSection E) :
    pullSection f (pullSection g a) = 0 ↔ pullSection (f ≫ g) a = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    let e := (Scheme.Modules.pullbackComp f g).hom.app E
    have he : pullSection f (pullSection g a) ≫ e = pullSection (f ≫ g) a :=
      CanonicalPullbackSectionProof.pullSection_comp f g a
    constructor
    · intro h
      exact he.symm.trans
        ((congrArg
          (fun b : AlgebraicSection (pullbackModule f (pullbackModule g E)) => b ≫ e)
          h).trans (HasZeroMorphisms.zero_comp (structureModule T) e))
    · intro h
      apply (cancel_mono e).mp
      exact (he.trans h).trans (HasZeroMorphisms.zero_comp (structureModule T) e).symm

/-- The actual diagonal factors through its second infinitesimal
neighborhood, so quadratic vanishing gives zero on the diagonal itself. -/
theorem diagonal_zero_of_orderTwo {Y : Scheme} (s : Y ⟶ ComplexBase)
    [IsSeparated s] {E : OModule (SelfProduct s)} (a : AlgebraicSection E)
    (ha : VanishesQuadraticallyAlongDiagonal s E a) :
    pullSection (diagonal s) a = 0 := by
  have hker : (diagonalPowerInclusion s 2).ker ≤ (diagonal s).ker := by
    change ((diagonalIdeal s) ^ 2).subschemeι.ker ≤ diagonalIdeal s
    rw [Scheme.IdealSheafData.ker_subschemeι]
    intro U
    change (diagonalIdeal s).ideal U ^ 2 ≤ (diagonalIdeal s).ideal U
    exact Ideal.pow_le_self (by decide)
  let j := IsClosedImmersion.lift (diagonalPowerInclusion s 2) (diagonal s) hker
  have hj : j ≫ diagonalPowerInclusion s 2 = diagonal s :=
    IsClosedImmersion.lift_fac _ _ hker
  apply (pullSection_zero_iff _ _).2
  rw [← hj]
  apply (LeBrunSalamon.PhaseFourteen.SliceRestrictionProof.pullback_comp_zero_iff
    j (diagonalPowerInclusion s 2) a).2
  have hmap : (Scheme.Modules.pullback (diagonalPowerInclusion s 2)).map a = 0 := ha
  rw [hmap, Functor.map_zero]

/-- The first-power subscheme is the actual closed diagonal. This
direction uses its closed-immersion universal property with equal ideals. -/
theorem orderOne_of_diagonal_zero {Y : Scheme} (s : Y ⟶ ComplexBase)
    [IsSeparated s] {E : OModule (SelfProduct s)} (a : AlgebraicSection E)
    (ha : pullSection (diagonal s) a = 0) :
    VanishesToOrderAlongDiagonal s E a 1 := by
  have hker : (diagonal s).ker ≤ (diagonalPowerInclusion s 1).ker := by
    change diagonalIdeal s ≤ ((diagonalIdeal s) ^ 1).subschemeι.ker
    rw [Scheme.IdealSheafData.ker_subschemeι, pow_one]
  let j := IsClosedImmersion.lift (diagonal s) (diagonalPowerInclusion s 1) hker
  have hj : j ≫ diagonal s = diagonalPowerInclusion s 1 :=
    IsClosedImmersion.lift_fac _ _ hker
  change (Scheme.Modules.pullback (diagonalPowerInclusion s 1)).map a = 0
  rw [← hj]
  apply (LeBrunSalamon.PhaseFourteen.SliceRestrictionProof.pullback_comp_zero_iff
    j (diagonal s) a).2
  rw [(pullSection_zero_iff _ _).1 ha, Functor.map_zero]

theorem curveSquare_diagonal (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X) :
    diagonal P.structureMap ≫ curveSquareMap P f = f.map ≫ diagonal X.structureMap := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, curveSquareMap_first, curveSquareMap_second,
      pullback.diagonal_fst, pullback.diagonal_snd,
      pullback.diagonal_fst_assoc, pullback.diagonal_snd_assoc,
      Category.id_comp, Category.comp_id]

theorem sourceContactValue_diagonal_zero (P : ProjectiveLineOverC) {n : ℕ}
    {X : SmoothProperComplexVariety (2*n+1)} (C : IntrinsicContactStructure X)
    (f : RationalCurve P X) :
    pullSection (diagonal P.structureMap) (sourceContactValue P C f) = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    have hs := diagonal_zero_of_orderTwo P.structureMap (sourceBivector P)
      (Classical.choose_spec (sourceBivector_existsUnique P)).1.2.1
    let e := externalTensorMap P.structureMap
      (curveContactVelocity P C f) (curveContactVelocity P C f) ≫
        curveExternalComparison P f C.sequence.line.sheaf C.sequence.line.sheaf
    change pullSection (diagonal P.structureMap) (sourceBivector P ≫ e) = 0
    have hn := pullSection_naturality (diagonal P.structureMap) (sourceBivector P) e
    have hz := congrArg
      (fun b : AlgebraicSection (pullbackModule (diagonal P.structureMap)
          (externalSquareLine P.structureMap (identityCurveContact P).sequence.line).sheaf) =>
        b ≫ (Scheme.Modules.pullback (diagonal P.structureMap)).map e) hs
    exact hn.trans (hz.trans
      (HasZeroMorphisms.zero_comp (structureModule ProjectiveLine)
        ((Scheme.Modules.pullback (diagonal P.structureMap)).map e)))

theorem curve_diagonal_zero (P : ProjectiveLineOverC) {n : ℕ}
    {X : SmoothProperComplexVariety (2*n+1)} (C : IntrinsicContactStructure X)
    (f : RationalCurve P X) (B : ExternalSquareSections X C.sequence.line)
    (h : CurveKernelIdentity P C f B) :
    pullSection f.map (pullSection (diagonal X.structureMap) B) = 0 := by
  have hf := (curveKernelIdentity_iff P C f B).1 h
  have hz : pullSection (diagonal P.structureMap)
      (pullSection (curveSquareMap P f) B) = 0 := by
    rw [hf]
    exact sourceContactValue_diagonal_zero P C f
  have hc := (pullSection_comp_zero_iff (diagonal P.structureMap) (curveSquareMap P f) B).1 hz
  rw [curveSquare_diagonal] at hc
  exact (pullSection_comp_zero_iff f.map (diagonal X.structureMap) B).2 hc

/-- The same full family detects bundle sections on X: pull back to
the first projection, whose diagonal section makes it surjective, then
use the already proved detection theorem on the target square. -/
theorem detects_base_section (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X)
    (H : FullConicNeighborhood P p X g) {r : ℕ}
    (E : AlgebraicVectorBundle X.variety.scheme r) (a b : AlgebraicSection E.sheaf)
    (h : ∀ t, pullSection (H.curveAt t).map a = pullSection (H.curveAt t).map b) : a = b := by
  have hsurj : Function.Surjective (firstProjection X.variety.structureMap) := by
    intro x
    refine ⟨diagonal X.variety.structureMap x, ?_⟩
    exact congrArg (fun k : X.variety.scheme ⟶ X.variety.scheme => k x)
      (pullback.diagonal_fst X.variety.structureMap)
  letI : AlgebraicGeometry.IsReduced X.variety.scheme :=
    LeBrunSalamon.SchemeStandardInputs.smooth_complex_reduced X.variety.structureMap
  apply dominant_pullSection_injective (firstProjection X.variety.structureMap)
    hsurj.denseRange (fun U => inferInstance) E
  apply fullFamily_detects_bundle_section P p X g H
    (pullbackBundle (firstProjection X.variety.structureMap) E)
  intro t
  let e := pullbackSquareIso (curveSquareMap P (H.curveAt t))
    (firstProjection X.variety.structureMap) (firstProjection P.structureMap)
    (H.curveAt t).map (curveSquareMap_first P (H.curveAt t)) E.sheaf
  apply (cancel_mono e.hom).mp
  change pullSection (curveSquareMap P (H.curveAt t))
      (pullSection (firstProjection X.variety.structureMap) a) ≫ e.hom =
    pullSection (curveSquareMap P (H.curveAt t))
      (pullSection (firstProjection X.variety.structureMap) b) ≫ e.hom
  dsimp only [e]
  rw [pullbackSquareIso_onSections, pullbackSquareIso_onSections, h t]

end FullFamilyDiagonalProof

namespace SymmetricDiagonalProof

open scoped TensorProduct
open Core.ExternalTensorCoordinates

/-- Differentiating multiplication separates the first and second
tensor slots. The derivation is the universal Kähler derivation. -/
theorem differential_multiply {A : Type} [CommRing A] [Algebra ℂ A]
    (t : A ⊗[ℂ] A) :
    KaehlerDifferential.D ℂ A (Algebra.TensorProduct.lmul' ℂ t) =
      (KaehlerDifferential.D ℂ A).tensorProductTo t +
        (KaehlerDifferential.D ℂ A).tensorProductTo (TensorProduct.comm ℂ A A t) := by
  refine TensorProduct.inductionOn t ?_ ?_
  · intro a b
    simp only [Algebra.TensorProduct.lmul'_apply_tmul, TensorProduct.comm_tmul,
      Derivation.tensorProductTo_tmul, Derivation.leibniz]
  · intro a b ha hb
    simp only [map_add, ha, hb]
    abel

/-- A symmetric tensor in the diagonal ideal has zero conormal class
over C, hence belongs to the square of that ideal. -/
theorem symmetric_mem_square {A : Type} [CommRing A] [Algebra ℂ A]
    (t : A ⊗[ℂ] A) (ht : t ∈ KaehlerDifferential.ideal ℂ A)
    (hs : TensorProduct.comm ℂ A A t = t) :
    t ∈ (KaehlerDifferential.ideal ℂ A) ^ 2 := by
  have hm : Algebra.TensorProduct.lmul' ℂ t = 0 := ht
  have hd := differential_multiply t
  rw [hm, map_zero, hs] at hd
  have htwo : (2 : ℂ) • (KaehlerDifferential.D ℂ A).tensorProductTo t = 0 := by
    simpa only [two_smul] using hd.symm
  have hz : (KaehlerDifferential.D ℂ A).tensorProductTo t = 0 :=
    (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  apply ((KaehlerDifferential.ideal ℂ A).toCotangent_eq_zero ⟨t, ht⟩).mp
  rw [← KaehlerDifferential.D_tensorProductTo]
  exact hz

/-- Both coefficient families are exchanged inside the same actual
section when the section is symmetric. -/
def exchangedSameExpansion {d : ℕ} {X : SmoothProperComplexVariety d}
    {L : LineBundle X.scheme} {B : ExternalSquareSections X L}
    (E : ExternalExpansion X L B)
    (hB : IsSymmetricExternalSection X.structureMap L B) :
    ExternalExpansion X L B where
  size := E.size
  left := E.right
  right := E.left
  equation := by
    set_option backward.isDefEq.respectTransparency false in
      exact hB.symm.trans (CurveExchangeProof.exchangedExpansion E).equation

theorem coefficientTensor_symmetric {d : ℕ} {X : SmoothProperComplexVariety d}
    {L : LineBundle X.scheme} {B : ExternalSquareSections X L}
    (E : ExternalExpansion X L B)
    (hB : IsSymmetricExternalSection X.structureMap L B) (F : AffineLineFrame L) :
    TensorProduct.comm ℂ (Coefficients X.structureMap F.openSet)
        (Coefficients X.structureMap F.openSet)
        (coefficientTensorMap X.structureMap L F E.tensor) =
      coefficientTensorMap X.structureMap L F E.tensor := by
  let E' := exchangedSameExpansion E hB
  have ht := congrArg (coefficientTensorMap X.structureMap L F) (E.tensor_independent E')
  have hs : TensorProduct.comm ℂ (Coefficients X.structureMap F.openSet)
        (Coefficients X.structureMap F.openSet)
        (coefficientTensorMap X.structureMap L F E.tensor) =
      coefficientTensorMap X.structureMap L F E'.tensor := by
    rw [E.coefficientTensorMap_tensor, E'.coefficientTensorMap_tensor, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rfl
  exact hs.trans ht.symm

/-- Symmetry kills the first normal symbol once the diagonal value is
zero. The proof uses the canonical affine quotient coefficient and the
universal conormal quotient, without testing selected tangent vectors. -/
theorem orderTwo_of_orderOne {d : ℕ} (X : SmoothProperComplexVariety d)
    (L : LineBundle X.scheme) (B : ExternalSquareSections X L)
    (hB : IsSymmetricExternalSection X.structureMap L B)
    (h0 : VanishesToOrderAlongDiagonal X.structureMap
      (externalSquareLine X.structureMap L).sheaf B 1) :
    VanishesQuadraticallyAlongDiagonal X.structureMap
      (externalSquareLine X.structureMap L).sheaf B := by
  set_option backward.isDefEq.respectTransparency false in
    obtain ⟨E⟩ := externalExpansion_exists X L B
    have hE : sectionFromValue
        (globalTensorMap X.structureMap L.sheaf L.sheaf E.tensor) = B := by
      rw [E.tensor_image]
      exact sectionFromValue_sectionValue B
    change VanishesToOrderAlongDiagonal X.structureMap
      (externalSquareLine X.structureMap L).sheaf B 2
    rw [← hE]
    apply (diagonalRestriction_iff_quotientCoefficients X.structureMap L E.tensor 2).2
    intro F
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hm : coefficientTensorMap X.structureMap L F E.tensor ∈
        KaehlerDifferential.ideal ℂ (Coefficients X.structureMap F.openSet) := by
      have h := E.coefficientTensor_mem_of_order 1 h0 F
      rw [pow_one] at h
      exact h
    exact symmetric_mem_square _ hm (coefficientTensor_symmetric E hB F)

end SymmetricDiagonalProof

/-- SOURCE jet:curve-expansion, constant term followed by continuation. -/
theorem fullFamily_diagonalValue (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X)
    (D : FamilyKernel P p X g) : FamilyKernel.HasZeroValue P p D := by
  have hz : pullSection (diagonal X.variety.structureMap) D.kernel = 0 := by
    apply FullFamilyDiagonalProof.detects_base_section P p X g D.family
      (pullbackBundle (diagonal X.variety.structureMap)
        (externalSquareLine X.variety.structureMap X.contact.sequence.line))
    intro t
    set_option backward.isDefEq.respectTransparency false in
      exact (FullFamilyDiagonalProof.curve_diagonal_zero P X.contact
        (D.family.curveAt t) D.kernel (D.fullIdentity t)).trans
          (FullFamilyDiagonalProof.pullSection_zero (D.family.curveAt t).map
            (E := pullbackModule (diagonal X.variety.structureMap)
              (externalSquareLine X.variety.structureMap X.contact.sequence.line).sheaf)).symm
  exact FullFamilyDiagonalProof.orderOne_of_diagonal_zero X.variety.structureMap D.kernel hz

/-- SOURCE jet:diagonal. Once the diagonal value vanishes, symmetry
annihilates the first normal symbol over C. -/
theorem fullFamily_firstSymbol (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X)
    (D : FamilyKernel P p X g) (h0 : FamilyKernel.HasZeroValue P p D) :
    FamilyKernel.HasZeroFirstSymbol P p D := by
  exact SymmetricDiagonalProof.orderTwo_of_orderOne X.variety
    X.contact.sequence.line D.kernel D.symmetry h0


structure DiagonalInputs (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) : Prop where
  value : ∀ (n : ℕ) (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X)
    (D : FamilyKernel P p X g), FamilyKernel.HasZeroValue P p D
  firstSymbol : ∀ (n : ℕ) (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X)
    (D : FamilyKernel P p X g), FamilyKernel.HasZeroValue P p D →
      FamilyKernel.HasZeroFirstSymbol P p D
  secondSymbol : ∀ (n : ℕ) (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X)
    (D : FamilyKernel P p X g), FamilyKernel.HasZeroFirstSymbol P p D →
      HasNormalizedContactSymbol X.contact D.kernel

theorem DiagonalInputs.assemble (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (H : DiagonalInputs P p) : FamilyToDiagonal P p := by
  intro n X g D
  have h1 := H.firstSymbol n X g D (H.value n X g D)
  exact ⟨⟨D.kernel, D.symmetry, h1, H.secondSymbol n X g D h1⟩, rfl⟩

/-! ## 4. Actual formal node and elementary pole-cancellation lemmas -/

namespace Boundary
section FormalNode
variable (R : Type*) [CommRing R]

abbrev FormalSeries := MvPowerSeries (Fin 2) R

def relationIdeal (a : R) : Ideal (FormalSeries R) :=
  Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C a}

/-- The completed-node MODEL; identifying it with a geometric completed
local ring requires the split-node theorem (Stacks 0CBX) and a complete DVR base. -/
abbrev FormalNode (a : R) := FormalSeries R ⧸ relationIdeal R a

def base (a : R) : R →+* FormalNode R a :=
  (Ideal.Quotient.mk (relationIdeal R a)).comp MvPowerSeries.C

def u (a : R) : FormalNode R a :=
  Ideal.Quotient.mk (relationIdeal R a) (MvPowerSeries.X 0)

def v (a : R) : FormalNode R a :=
  Ideal.Quotient.mk (relationIdeal R a) (MvPowerSeries.X 1)

def branchIdeal (a : R) : Ideal (FormalNode R a) := Ideal.span {u R a, v R a}

theorem relation (a : R) : u R a * v R a = base R a a := by
  apply sub_eq_zero.mp
  have h : Ideal.Quotient.mk (relationIdeal R a)
      (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C a) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp)
  simpa only [u, v, base, RingHom.comp_apply, map_sub, map_mul] using h


/-- Exact quotient statement behind ext:ideal-intersection. The image of
EVERY base element is fixed, so this is not an arbitrary ring equivalence. -/
theorem quotientByBranches (a : R) :
    ∃ e : (FormalNode R a ⧸ branchIdeal R a) ≃+* (R ⧸ Ideal.span {a}),
      ∀ r : R, e (Ideal.Quotient.mk (branchIdeal R a) (base R a r)) =
        Ideal.Quotient.mk (Ideal.span {a}) r := by
  classical
  let seriesQuotientMap : FormalSeries R →+* (FormalNode R a ⧸ branchIdeal R a) :=
    (Ideal.Quotient.mk (branchIdeal R a)).comp (Ideal.Quotient.mk (relationIdeal R a))
  let β : R →+* (FormalNode R a ⧸ branchIdeal R a) := seriesQuotientMap.comp MvPowerSeries.C
  have hX (i : Fin 2) : seriesQuotientMap (MvPowerSeries.X i) = 0 := by
    fin_cases i
    · change Ideal.Quotient.mk (branchIdeal R a) (u R a) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    · change Ideal.Quotient.mk (branchIdeal R a) (v R a) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hβa : β a = 0 := by
    change Ideal.Quotient.mk (branchIdeal R a) (base R a a) = 0
    rw [← relation R a, map_mul]
    change seriesQuotientMap (MvPowerSeries.X 0) * seriesQuotientMap (MvPowerSeries.X 1) = 0
    erw [hX, hX]
    exact @MulZeroClass.mul_zero (FormalNode R a ⧸ branchIdeal R a)
      inferInstance 0
  have hβ : Ideal.span ({a} : Set R) ≤ RingHom.ker β := by
    apply Ideal.span_le.mpr
    intro r hr
    have hr' : r = a := Set.mem_singleton_iff.mp hr
    subst r
    exact RingHom.mem_ker.mpr hβa
  let backward : (R ⧸ Ideal.span {a}) →+* (FormalNode R a ⧸ branchIdeal R a) :=
    Ideal.Quotient.lift (Ideal.span {a}) β
      (fun r hr => RingHom.mem_ker.mp (hβ hr))
  let ρ : FormalSeries R →+* (R ⧸ Ideal.span {a}) :=
    (Ideal.Quotient.mk (Ideal.span {a})).comp MvPowerSeries.constantCoeff
  have haq : Ideal.Quotient.mk (Ideal.span ({a} : Set R)) a = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hrel : relationIdeal R a ≤ RingHom.ker ρ := by
    apply Ideal.span_le.mpr
    intro p hp
    have hp' : p = MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C a :=
      Set.mem_singleton_iff.mp hp
    subst p
    apply RingHom.mem_ker.mpr
    simp [ρ, haq]
  let ρ₁ : FormalNode R a →+* (R ⧸ Ideal.span {a}) :=
    Ideal.Quotient.lift (relationIdeal R a) ρ
      (fun p hp => RingHom.mem_ker.mp (hrel hp))
  have hbranch : branchIdeal R a ≤ RingHom.ker ρ₁ := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> simp [ρ₁, ρ, u, v]
  let forward : (FormalNode R a ⧸ branchIdeal R a) →+* (R ⧸ Ideal.span {a}) :=
    Ideal.Quotient.lift (branchIdeal R a) ρ₁
      (fun z hz => RingHom.mem_ker.mp (hbranch hz))
  have hconst (p : FormalSeries R) : seriesQuotientMap p = β (MvPowerSeries.constantCoeff p) := by
    let p₀ : FormalSeries R := fun d =>
      if d 0 = 0 then MvPowerSeries.coeff d p else 0
    have hp₀ (d : Fin 2 →₀ ℕ) : MvPowerSeries.coeff d p₀ =
        if d 0 = 0 then MvPowerSeries.coeff d p else 0 := rfl
    have hd₀ : (MvPowerSeries.X 0 : FormalSeries R) ∣ p - p₀ := by
      apply MvPowerSeries.X_dvd_iff.mpr
      intro d hd
      rw [map_sub, hp₀, if_pos hd, sub_self]
    have hd₁ : (MvPowerSeries.X 1 : FormalSeries R) ∣
        p₀ - MvPowerSeries.C (MvPowerSeries.constantCoeff p) := by
      apply MvPowerSeries.X_dvd_iff.mpr
      intro d hd
      rw [map_sub, hp₀, MvPowerSeries.coeff_C]
      by_cases h₀ : d 0 = 0
      · have hz : d = 0 := by
          apply Finsupp.ext
          intro i
          fin_cases i
          · exact h₀
          · exact hd
        subst d
        simp only [Finsupp.zero_apply, if_pos rfl,
          MvPowerSeries.coeff_zero_eq_constantCoeff_apply, sub_self]
      · have hz : d ≠ 0 := by
          intro hz
          apply h₀
          simp only [hz, Finsupp.zero_apply]
        rw [if_neg h₀, if_neg hz, sub_self]
    obtain ⟨g, hg⟩ := hd₀
    obtain ⟨h, hh⟩ := hd₁
    have hp : p = MvPowerSeries.C (MvPowerSeries.constantCoeff p) +
        MvPowerSeries.X 0 * g + MvPowerSeries.X 1 * h := by
      linear_combination hg + hh
    calc
      seriesQuotientMap p = seriesQuotientMap (MvPowerSeries.C (MvPowerSeries.constantCoeff p) +
          MvPowerSeries.X 0 * g + MvPowerSeries.X 1 * h) := congrArg seriesQuotientMap hp
      _ = β (MvPowerSeries.constantCoeff p) := by
        erw [map_add, map_add, map_mul, map_mul, hX, hX]
        have hg0 : (0 : FormalNode R a ⧸ branchIdeal R a) * seriesQuotientMap g = 0 :=
          @MulZeroClass.zero_mul (FormalNode R a ⧸ branchIdeal R a)
            inferInstance (seriesQuotientMap g)
        have hh0 : (0 : FormalNode R a ⧸ branchIdeal R a) * seriesQuotientMap h = 0 :=
          @MulZeroClass.zero_mul (FormalNode R a ⧸ branchIdeal R a)
            inferInstance (seriesQuotientMap h)
        rw [hg0, hh0]
        change β (MvPowerSeries.constantCoeff p) + 0 + 0 = β (MvPowerSeries.constantCoeff p)
        exact (_root_.add_zero (β (MvPowerSeries.constantCoeff p) + 0)).trans
          (_root_.add_zero (β (MvPowerSeries.constantCoeff p)))
  have hleft : Function.LeftInverse backward forward := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    change β (MvPowerSeries.constantCoeff p) = seriesQuotientMap p
    exact (hconst p).symm
  have hright : Function.RightInverse backward forward := by
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.Quotient.mk (Ideal.span {a})
        (MvPowerSeries.constantCoeff (MvPowerSeries.C r)) =
      Ideal.Quotient.mk (Ideal.span {a}) r
    rw [MvPowerSeries.constantCoeff_C]
  let e := RingEquiv.ofBijective forward ⟨hleft.injective, hright.surjective⟩
  refine ⟨e, ?_⟩
  intro r
  change Ideal.Quotient.mk (Ideal.span {a})
      (MvPowerSeries.constantCoeff (MvPowerSeries.C r)) =
    Ideal.Quotient.mk (Ideal.span {a}) r
  rw [MvPowerSeries.constantCoeff_C]


theorem base_mem_branchIdeal_iff (a r : R) :
    base R a r ∈ branchIdeal R a ↔ r ∈ Ideal.span {a} := by
  obtain ⟨e, he⟩ := quotientByBranches R a
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← he r, Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply e.injective
    rw [map_zero, he r]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h


/-- Multiplication by the unit describing a local generator cannot
change the branch-ideal membership. No division by u or v is used. -/
theorem unitCoefficient_forces_parameter_divisibility (a h : R)
    (c : (FormalNode R a)ˣ) (hh : base R a h * c.val ∈ branchIdeal R a) :
    a ∣ h := by
  apply Ideal.mem_span_singleton.mp
  apply (base_mem_branchIdeal_iff R a h).mp
  exact ((branchIdeal R a).mul_unit_mem_iff_mem c.isUnit).mp hh


/-- The dualizing relation respects v du + u dv = 0. This scalar
identity is NOT a construction of the dualizing sheaf. -/
theorem dualizing_relation (a : R) :
    v R a * u R a + u R a * (-v R a) = 0 := by ring

end FormalNode
section Poles
variable (R K : Type*) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

def RegularScalar (z : K) : Prop := ∃ a : R, algebraMap R K a = z

/-- Cleared-denominator bound; over a DVR with uniformizer pi this is
ord(z)>=-r, including z=0. The definition itself is ordinary ring algebra. -/
def PoleAtMost (pi : R) (r : ℕ) (z : K) : Prop :=
  RegularScalar R K ((algebraMap R K pi)^r * z)

def VanishesAtLeast (pi : R) (r : ℕ) (z : K) : Prop :=
  ∃ a : R, z = (algebraMap R K pi)^r * algebraMap R K a

theorem regular_mul {z w : K} (hz : RegularScalar R K z) (hw : RegularScalar R K w) :
    RegularScalar R K (z*w) := by
  obtain ⟨a, rfl⟩ := hz
  obtain ⟨b, rfl⟩ := hw
  exact ⟨a*b, map_mul (algebraMap R K) a b⟩

theorem regular_add {z w : K} (hz : RegularScalar R K z) (hw : RegularScalar R K w) :
    RegularScalar R K (z+w) := by
  obtain ⟨a, rfl⟩ := hz
  obtain ⟨b, rfl⟩ := hw
  exact ⟨a+b, map_add (algebraMap R K) a b⟩

theorem pole_mono (pi : R) {r s : ℕ} (hrs : r ≤ s) {z : K}
    (h : PoleAtMost R K pi r z) : PoleAtMost R K pi s z := by
  obtain ⟨a, ha⟩ := h
  refine ⟨pi ^ (s-r) * a, ?_⟩
  rw [map_mul, map_pow, ha, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hrs]

theorem pole_cancel (pi : R) (r : ℕ) {z c : K}
    (hz : PoleAtMost R K pi r z) (hc : VanishesAtLeast R K pi r c) :
    RegularScalar R K (z*c) := by
  obtain ⟨a, ha⟩ := hz
  obtain ⟨b, hb⟩ := hc
  refine ⟨a*b, ?_⟩
  rw [map_mul, ha, hb]
  ring

theorem vanish_regular (pi : R) (r : ℕ) {z : K}
    (hz : VanishesAtLeast R K pi r z) : RegularScalar R K z := by
  obtain ⟨a, ha⟩ := hz
  refine ⟨pi ^ r * a, ?_⟩
  rw [map_mul, map_pow]
  exact ha.symm

end Poles

set_option backward.isDefEq.respectTransparency false in
inductive Component where
  | first | second
  deriving DecidableEq, Repr, Fintype

/-- SOURCE ext:pole-table: same-component products have no pole. A
second contraction is needed for the second/second component. -/
def poleBudget (r : ℕ) (a b : Component) : ℕ := if a = b then 0 else r

theorem poleBudget_le (r : ℕ) (a b : Component) : poleBudget r a b ≤ r := by
  unfold poleBudget
  split <;> omega

theorem poleBudget_swap (r : ℕ) (a b : Component) :
    poleBudget r a b = poleBudget r b a := by
  cases a <;> cases b <;> simp [poleBudget]

/-- Coefficientwise cancellation for BOTH vector lifts. Geometric valuation bounds and the order-r contact
vanishing are explicit inputs. This lemma does not assert those bounds for an arbitrary family. -/
theorem twoVectorLifts_regular
    (R K : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (pi : R) (r : ℕ) (a b : Component) (z d1 d2 c1 c2 : K)
    (hz : PoleAtMost R K pi (poleBudget r a b) z)
    (hd1 : RegularScalar R K d1) (hd2 : RegularScalar R K d2)
    (hc1 : VanishesAtLeast R K pi r c1) (hc2 : VanishesAtLeast R K pi r c2) :
    RegularScalar R K (z*d1*c2) ∧ RegularScalar R K (z*c1*d2) := by
  have hz' : PoleAtMost R K pi r z := pole_mono R K pi (poleBudget_le r a b) hz
  constructor
  · simpa only [mul_assoc, mul_left_comm, mul_comm] using
      regular_mul R K (pole_cancel R K pi r hz' hc2) hd1
  · exact regular_mul R K (pole_cancel R K pi r hz' hc1) hd2

/-- SOURCE ext:extended-vectors: on a normal noetherian affine chart,
regularity at all height-one primes detects actual regular functions.
The numerator/denominator condition is the literal localization test. Stacks Project, Tag 031T. -/
def RegularAtPrime (R K : Type*) [CommRing R] [Field K] [Algebra R K]
    (p : Ideal R) (z : K) : Prop :=
  ∃ a b : R, b ∉ p ∧ z * algebraMap R K b = algebraMap R K a

theorem LeBrunSalamon.PublishedInputs.Step3f.regular_of_heightOne
    (R K : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] (z : K)
    (hz : ∀ p : Ideal R, p.IsPrime → p.height = 1 → RegularAtPrime R K p z) :
    RegularScalar R K z := by
  sorry

/-- Project-facing alias of the height-one intersection theorem, Stacks Tag 031T. -/
theorem regular_of_heightOne
    (R K : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] (z : K)
    (hz : ∀ p : Ideal R, p.IsPrime → p.height = 1 → RegularAtPrime R K p z) :
    RegularScalar R K z := by
  exact LeBrunSalamon.PublishedInputs.Step3f.regular_of_heightOne R K z hz

/-- Trivialize the LOCALLY FREE TARGET, not the relative tangent sheaf
at the node. This is the vector-valued form used in boundary extension. -/
theorem vector_regular_of_heightOne
    (R K : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] (r : ℕ) (z : Fin r → K)
    (hz : ∀ p : Ideal R, p.IsPrime → p.height = 1 → ∀ i, RegularAtPrime R K p (z i)) :
    ∃ v : Fin r → R, ∀ i, algebraMap R K (v i) = z i := by
  classical
  have h (i : Fin r) : RegularScalar R K (z i) :=
    regular_of_heightOne R K (z i) (fun p hp hheight => hz p hp hheight i)
  exact ⟨fun i => Classical.choose (h i), fun i => Classical.choose_spec (h i)⟩

end Boundary

/-!
## Symmetric jets, refined to local functions and actual global contractions

SOURCE: jets.tex, jet:local-calculation and the proof of jet:criterion, at Project.manuscriptCommit. This
module refines one previously monolithic input. For ANY finite expansion B=sum a_i boxtimes b_i, use the
coefficient vector of (a_i) in a local line frame. Independence of the b_i is NOT required. Its value and
derivative are evaluated using genuine point derivations. Contracting the coefficient vector produces the
actual global section sum lambda(e_i)*a_i.

Local coordinates on jets are normalized on ALL local functions, not merely on the as-yet-unknown image of
H^0(L). No global jet-surjectivity assumption is allowed in these definitions. A frame of L does not
globally split its jet bundle. The existence and comparison lemmas below remain explicit proof
obligations.
-/
namespace Jets

open LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseSeventeen
open LeBrunSalamon.PhaseNineteen LeBrunSalamon.PhaseTwentyTwo

/-- A line frame on an actual affine neighborhood of a specified complex point. -/
structure PointFrame {d : ℕ} (X : SmoothProperComplexVariety d)
    (L : LineBundle X.scheme) (x : ComplexPoint X) where
  frame : AffineLineFrame L
  pointLift : ComplexBase ⟶ frame.openSet.toScheme
  overPoint : pointLift ≫ frame.openSet.ι = x.map

theorem pointFrame_exists {d : ℕ} (X : SmoothProperComplexVariety d)
    (L : LineBundle X.scheme) (x : ComplexPoint X) : Nonempty (PointFrame X L x) := by
  let z : ComplexBase := IsLocalRing.closedPoint ℂ
  obtain ⟨F, hF⟩ := affineLineFrames_cover L (x.map z)
  have hr : Set.range x.map ⊆ Set.range F.openSet.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    change x.map w ∈ F.openSet
    rw [Subsingleton.elim w z]
    exact hF
  exact ⟨⟨F, IsOpenImmersion.lift F.openSet.ι x.map hr,
    IsOpenImmersion.lift_fac _ _ _⟩⟩


namespace PointFrame
variable {d : ℕ} {X : SmoothProperComplexVariety d} {L : LineBundle X.scheme}
  {x : ComplexPoint X} (F : PointFrame X L x)

/-- A type alias retaining the chosen C-structure, not a new abstract ring. -/
def ChartRing : Type _ := RingSections X.scheme F.frame.openSet
instance chartCommRing : CommRing F.ChartRing :=
  inferInstanceAs (CommRing (RingSections X.scheme F.frame.openSet))

/-- The actual scalar map; its four ring-law proof fields are supplied in the uncompiled continuation. -/
def constants : ℂ →+* F.ChartRing :=
  ScalarSections.constantsOn X.structureMap F.frame.openSet
instance chartAlgebra : Algebra ℂ F.ChartRing := F.constants.toAlgebra

/-- Evaluate through the genuine point of the affine open. -/
def evaluation : F.ChartRing →ₐ[ℂ] ℂ where
  toRingHom := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp
    (F.pointLift.appTop.hom.comp F.frame.openSet.topIso.inv.hom)
  commutes' := by
    intro c
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (F.pointLift.appTop (F.frame.openSet.topIso.inv
        (complexConstant X.structureMap F.frame.openSet c))) = c
    exact ScalarSections.evaluate_complexConstant X.structureMap F.frame.openSet F.pointLift
      (by rw [← Category.assoc, F.overPoint, x.overC]) c

def coefficient (a : AlgebraicSection L.sheaf) : F.ChartRing :=
  F.frame.localCoefficient a

/-- Der_C(O(U), C_x), as a SUBMODULE so its linear structure is canonical. -/
def pointDerivations : Submodule ℂ (F.ChartRing →ₗ[ℂ] ℂ) where
  carrier := {D : F.ChartRing →ₗ[ℂ] ℂ | ∀ a b : F.ChartRing, D (a*b) = F.evaluation a * D b + F.evaluation b * D a}
  zero_mem' := by intro a b; simp
  add_mem' := by
    intro D E hD hE a b
    simp only [LinearMap.add_apply, hD a b, hE a b]
    ring
  smul_mem' := by
    intro c D hD a b
    simp only [LinearMap.smul_apply, smul_eq_mul, hD a b]
    ring
abbrev Tangent := ↥F.pointDerivations

/-- df at x, evaluated on all point derivations, not global vector fields. -/
def differential (a : F.ChartRing) : F.Tangent →ₗ[ℂ] ℂ where
  toFun D := D.val a
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def localJet (a : F.ChartRing) : TrivializedFirstJet F.Tangent :=
  (F.evaluation a, F.differential a)

namespace PointDerivationFiniteProof

/-- The actual complex scalar map on an affine chart is of finite type. -/
theorem constantsOn_finiteType {Y : Scheme} (s : Y ⟶ ComplexBase)
    [LocallyOfFiniteType s] (U : Y.Opens) (hU : IsAffineOpen U) :
    (ScalarSections.constantsOn s U).FiniteType := by
  have hf : (s.appLE ⊤ U (by simp)).hom.FiniteType :=
    s.finiteType_appLE (isAffineOpen_top ComplexBase) hU (by simp)
  have hg : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective
  change ((s.appLE ⊤ U (by simp)).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom).FiniteType
  exact hf.comp hg

/-- Values on finitely many actual algebra generators determine every point derivation. -/
theorem pointDerivations_finite {A : Type*} [CommRing A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] (p : A →ₐ[ℂ] ℂ)
    (S : Submodule ℂ (A →ₗ[ℂ] ℂ))
    (hS : ∀ D : S, ∀ a b : A, D.val (a * b) = p a * D.val b + p b * D.val a) :
    FiniteDimensional ℂ S := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType ℂ A).out
  let values : S →ₗ[ℂ] (s → ℂ) :=
    { toFun := fun D i => D.val i.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hconstant (D : S) (c : ℂ) : D.val (algebraMap ℂ A c) = 0 := by
    have hone := hS D 1 1
    have hz : D.val (1 : A) = 0 := by
      simp only [one_mul, map_one] at hone
      linear_combination -hone
    simpa only [Algebra.smul_def, mul_one, smul_eq_mul, hz, mul_zero] using
      D.val.map_smul c (1 : A)
  apply FiniteDimensional.of_injective values
  intro D E h
  apply Subtype.ext
  apply LinearMap.ext
  intro a
  have ha : a ∈ Algebra.adjoin ℂ (s : Set A) := by rw [hs]; trivial
  induction ha using Algebra.adjoin_induction with
  | mem a ha => exact congrFun h ⟨a, ha⟩
  | algebraMap c => rw [hconstant, hconstant]
  | add a b ha hb ia ib => rw [map_add, map_add, ia, ib]
  | mul a b ha hb ia ib => rw [hS D, hS E, ia, ib]

end PointDerivationFiniteProof

theorem tangent_finite : FiniteDimensional ℂ F.Tangent := by
  letI : Algebra.FiniteType ℂ F.ChartRing := by
    apply RingHom.finiteType_algebraMap.mp
    exact PointDerivationFiniteProof.constantsOn_finiteType X.structureMap
      F.frame.openSet F.frame.isAffine
  exact PointDerivationFiniteProof.pointDerivations_finite F.evaluation
    F.pointDerivations (fun D => D.property)

attribute [instance] tangent_finite



theorem localJet_equal_iff (a b : F.ChartRing) : F.localJet a = F.localJet b ↔
    a-b ∈ (RingHom.ker F.evaluation.toRingHom)^2 := by
  change (F.evaluation a, F.differential a) = (F.evaluation b, F.differential b) ↔ _
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨hv, hd⟩
    apply (LeBrunSalamon.PhaseThirtyOne.allPointDerivations_detect_firstJet
      F.evaluation a b).mpr
    refine ⟨hv, ?_⟩
    intro D
    exact LinearMap.congr_fun hd (⟨D.val, D.property⟩ : F.Tangent)
  · intro h
    obtain ⟨hv, hd⟩ :=
      (LeBrunSalamon.PhaseThirtyOne.allPointDerivations_detect_firstJet
        F.evaluation a b).mp h
    refine ⟨hv, ?_⟩
    apply LinearMap.ext
    intro D
    exact hd ⟨D.val, D.property⟩


/-- The chosen lift identifies the inverse image of the actual frame open with all of Spec C. -/
theorem point_preimage_frame : x.map ⁻¹ᵁ F.frame.openSet = ⊤ := by
  apply top_unique
  intro z hz
  change x.map z ∈ F.frame.openSet
  have h := congrArg (fun g : ComplexBase ⟶ X.scheme => g z) F.overPoint
  simp only [Scheme.Hom.comp_apply] at h
  rw [← h]
  exact (F.pointLift z).property

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient evaluation and the original point's affine ring map have exactly the same kernel. -/
theorem evaluation_kernel :
    RingHom.ker F.evaluation.toRingHom =
      RingHom.ker (x.map.app F.frame.openSet).hom := by
  let hTop : (⊤ : ComplexBase.Opens) ≤ x.map ⁻¹ᵁ F.frame.openSet := by
    rw [F.point_preimage_frame]
  have hi : F.frame.openSet.topIso.inv =
      F.frame.openSet.ι.appLE F.frame.openSet ⊤ (by simp) := by
    simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE]
    rfl
  have hcomp : F.frame.openSet.topIso.inv ≫ F.pointLift.appTop =
      x.map.appLE F.frame.openSet ⊤ hTop := by
    rw [hi, Scheme.Hom.appTop, F.pointLift.app_eq_appLE,
      Scheme.Hom.appLE_comp_appLE]
    have appLE_congr {f g : ComplexBase ⟶ X.scheme} (hfg : f = g)
        (hf : (⊤ : ComplexBase.Opens) ≤ f ⁻¹ᵁ F.frame.openSet)
        (hg : (⊤ : ComplexBase.Opens) ≤ g ⁻¹ᵁ F.frame.openSet) :
        f.appLE F.frame.openSet ⊤ hf = g.appLE F.frame.openSet ⊤ hg := by
      subst g
      rfl
    exact appLE_congr F.overPoint
      (by simpa only [F.overPoint] using hTop) hTop
  let r : Γ(ComplexBase, x.map ⁻¹ᵁ F.frame.openSet) ⟶ Γ(ComplexBase, ⊤) :=
    ComplexBase.presheaf.map (homOfLE hTop).op
  haveI : IsIso r := by
    have hh : (homOfLE hTop).op =
        eqToHom (congrArg Opposite.op F.point_preimage_frame) := Subsingleton.elim _ _
    dsimp only [r]
    rw [hh]
    infer_instance
  let e : RingSections ComplexBase (x.map ⁻¹ᵁ F.frame.openSet) ≃+* ℂ :=
    ((asIso r).trans (Scheme.ΓSpecIso (CommRingCat.of ℂ))).commRingCatIsoToRingEquiv
  have he : F.evaluation.toRingHom =
      e.toRingHom.comp (x.map.app F.frame.openSet).hom := by
    ext a
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        (F.pointLift.appTop (F.frame.openSet.topIso.inv a)) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        (r ((x.map.app F.frame.openSet) a))
    exact congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom z)
      (congrArg (fun q : Γ(X.scheme, F.frame.openSet) ⟶ Γ(ComplexBase, ⊤) => q a) hcomp)
  rw [he, RingHom.ker_equiv_comp]

/-- The actual order-two thickening has the square of this frame's evaluation kernel. -/
theorem fatPoint_chart_kernel :
    RingHom.ker ((pointPowerInclusion x 2).app F.frame.openSet).hom =
      (RingHom.ker F.evaluation.toRingHom) ^ 2 := by
  rw [F.evaluation_kernel]
  exact IntrinsicJetAffineQuotientProof.pointPower_kernel_on_affine x
    F.frame.openSet F.frame.isAffine 2

/-- A normalized scalar coordinate ring equivalence for the actual fat-point chart. -/
def fatPointChartEquiv :
    (F.ChartRing ⧸ (RingHom.ker F.evaluation.toRingHom) ^ 2) ≃+*
      RingSections (pointPowerSubscheme x 2)
        ((pointPowerInclusion x 2) ⁻¹ᵁ F.frame.openSet) :=
  (Ideal.quotEquivOfEq F.fatPoint_chart_kernel.symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := ((pointPowerInclusion x 2).app F.frame.openSet).hom)
      (IntrinsicJetAffineQuotientProof.pointPower_affine_restriction_surjective x
        F.frame.openSet F.frame.isAffine 2))

set_option backward.isDefEq.respectTransparency false in
/-- The scalar coordinate comparison fixes every ambient function, rather than only global sections. -/
theorem fatPointChartEquiv_mk (a : F.ChartRing) :
    F.fatPointChartEquiv
        (Ideal.Quotient.mk ((RingHom.ker F.evaluation.toRingHom) ^ 2) a) =
      ((pointPowerInclusion x 2).app F.frame.openSet).hom a := by
  rfl

/-- Equality of local first jets is equality of the two actual restricted scalar functions. -/
theorem localJet_equal_iff_fatPoint (a b : F.ChartRing) :
    F.localJet a = F.localJet b ↔
      ((pointPowerInclusion x 2).app F.frame.openSet).hom a =
        ((pointPowerInclusion x 2).app F.frame.openSet).hom b := by
  rw [F.localJet_equal_iff, F.evaluation_kernel]
  exact (IntrinsicJetAffineQuotientProof.pointPower_restriction_eq_iff x
    F.frame.openSet F.frame.isAffine 2 a b).symm

theorem localJet_surjective : Function.Surjective F.localJet := by
  classical
  let dmap : F.ChartRing →ₗ[ℂ] (F.Tangent →ₗ[ℂ] ℂ) :=
    { toFun := F.differential
      map_add' := by
        intro a b
        apply LinearMap.ext
        intro D
        exact D.val.map_add a b
      map_smul' := by
        intro c a
        apply LinearMap.ext
        intro D
        exact D.val.map_smul c a }
  have hspan : Submodule.span ℂ (Set.range dmap) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro D hD
    by_contra hnone
    apply hD
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    by_contra ha
    exact hnone ⟨dmap a, ⟨a, rfl⟩, ha⟩
  have hsurj : Function.Surjective dmap := by
    apply LinearMap.range_eq_top.mp
    apply le_antisymm le_top
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  have hconst (c : ℂ) : F.differential (algebraMap ℂ F.ChartRing c) = 0 := by
    apply LinearMap.ext
    intro D
    have h₁ := D.property (1 : F.ChartRing) 1
    have hz : D.val (1 : F.ChartRing) = 0 := by
      simp only [one_mul, map_one] at h₁
      linear_combination -h₁
    change D.val (algebraMap ℂ F.ChartRing c) = 0
    simpa only [Algebra.smul_def, mul_one, smul_eq_mul, hz, mul_zero] using
      D.val.map_smul c (1 : F.ChartRing)
  rintro ⟨z, dz⟩
  obtain ⟨a, ha⟩ := hsurj dz
  refine ⟨a + algebraMap ℂ F.ChartRing (z - F.evaluation a), ?_⟩
  apply Prod.ext
  · change F.evaluation (a + algebraMap ℂ F.ChartRing (z - F.evaluation a)) = z
    rw [map_add, AlgHom.commutes, Algebra.algebraMap_self_apply]
    ring
  · change dmap (a + algebraMap ℂ F.ChartRing (z - F.evaluation a)) = dz
    rw [map_add]
    change F.differential a + F.differential (algebraMap ℂ F.ChartRing
      (z - F.evaluation a)) = dz
    rw [hconst, add_zero]
    exact ha


section EvaluateVectorProofSection

set_option backward.isDefEq.respectTransparency false

namespace EvaluateVectorProof

/-- The relative differential kills the actual complex constants on every open. -/
theorem relativeDerivation_constant {Y : Scheme} (sY : Y ⟶ ComplexBase)
    {E : OModule Y} (D : RelativeSheafDerivation sY E)
    (U : Y.Opens) (c : ℂ) : D.apply U (complexConstant sY U c) = 0 := by
  have hk := D.killsBase ⊤ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)
  change D.apply ⊤ (sY.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) = 0 at hk
  have hn := D.naturality (homOfLE (show U ≤ ⊤ from le_top))
    (sY.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))
  rw [hk, map_zero] at hn
  exact hn.symm

/-- A local intrinsic tangent section annihilates the actual complex constants. -/
theorem action_constant {Y : Scheme} (sY : Y ⟶ ComplexBase) (U : Y.Opens)
    (v : SectionsOn (tangentSheaf sY) U) (c : ℂ) :
    tangentActs sY U v (complexConstant sY U c) = 0 := by
  change (tangentCotangentPair sY).apply U v
    ((cotangentPresentation sY).differential.apply U (complexConstant sY U c)) = 0
  rw [relativeDerivation_constant]
  exact ((tangentCotangentPair sY).apply U v).map_zero

/-- An intrinsic tangent section acts on every subopen of its domain. -/
def localAction {Y : Scheme} (s : Y ⟶ ComplexBase) (U : Y.Opens)
    (v : SectionsOn (tangentSheaf s) U) :
    LocalDerivationProof.LocalDerivation s (structureModule Y) U where
  apply W a := tangentActs s W.left (TangentBracketProof.restrictField s U v W) a
  zero W := TangentActionProof.zero_function s W.left _
  add W a b := TangentActionProof.add_function s W.left _ a b
  leibniz W a b := TangentActionProof.leibniz s W.left _ a b
  naturality := by
    intro V W i a
    change Y.presheaf.map i.left.op
        (tangentActs s W.left (TangentBracketProof.restrictField s U v W) a) = _
    rw [TangentActionProof.naturality, TangentBracketProof.restrictField_naturality]
  killsBase := by
    intro V a W i
    exact TangentBracketProof.killsRestrictedBase s V W.left i _ a

theorem localAction_top {Y : Scheme} (s : Y ⟶ ComplexBase) (U : Y.Opens)
    (v : SectionsOn (tangentSheaf s) U) (a : RingSections Y U) :
    (localAction s U v).apply (Over.mk (𝟙 U)) a = tangentActs s U v a := by
  change tangentActs s U ((tangentSheaf s).presheaf.map (𝟙 U).op v) a = _
  simp

/-- On an affine open, testing all of its regular functions already tests
the entire local derivation, so it determines the intrinsic vector. -/
theorem affine_tangent_action_faithful {Y : Scheme} (s : Y ⟶ ComplexBase)
    (U : Y.Opens) (hU : IsAffineOpen U)
    (v w : SectionsOn (tangentSheaf s) U)
    (h : ∀ a, tangentActs s U v a = tangentActs s U w a) : v = w := by
  have he : localAction s U v = localAction s U w :=
    LeBrunSalamon.StandardInputs.affine_localDerivation_ext s U hU
      (localAction s U v) (localAction s U w)
      (fun a => (localAction_top s U v a).trans ((h a).trans (localAction_top s U w a).symm))
  apply tangentActs_faithful s U
  intro V i a
  exact congrArg (fun δ : LocalDerivationProof.LocalDerivation s (structureModule Y) U =>
    δ.apply (Over.mk i) a) he

/-- The affine sheaf-derivation correspondence and the already constructed
cotangent universal property give an intrinsic tangent section with exactly
the specified action on the affine coordinate ring. -/
theorem affine_tangent_action_exists {Y : Scheme} (s : Y ⟶ ComplexBase)
    (U : Y.Opens) (hU : IsAffineOpen U)
    (D : RingSections Y U → RingSections Y U)
    (h0 : D 0 = 0)
    (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = a * D b + b * D a)
    (hc : ∀ c : ℂ, D (complexConstant s U c) = 0) :
    ∃ v : SectionsOn (tangentSheaf s) U, ∀ a, tangentActs s U v a = D a := by
  obtain ⟨δ, hδ⟩ := LeBrunSalamon.StandardInputs.affine_localDerivation_exists
    s U hU D h0 hadd hmul hc
  obtain ⟨φ, hφ⟩ := LocalDerivationProof.realize (cotangentPresentation s)
    (structureModule Y) U δ
  obtain ⟨v, hv⟩ := TangentBracketProof.localFunctional_surjective s U φ
  refine ⟨v, ?_⟩
  intro a
  have hlocal :
      (TangentBracketProof.localFunctional s U v).val.app (Opposite.op (Over.mk (𝟙 U)))
          ((cotangentPresentation s).differential.apply U a) =
        tangentActs s U ((tangentSheaf s).presheaf.map (𝟙 U).op v) a :=
    TangentBracketProof.localFunctional_apply s U v (Over.mk (𝟙 U)) a
  have hid : (tangentSheaf s).presheaf.map (𝟙 U).op v = v := by simp
  rw [hid, hv] at hlocal
  exact hlocal.symm.trans ((hφ (Over.mk (𝟙 U)) a).trans (hδ a))

/-- The algebra structure used by a point frame is the actual smooth
structure morphism on its affine open, composed with the canonical
identification of the global functions of `Spec ℂ` with `ℂ`. -/
theorem chartRing_smooth : Algebra.Smooth ℂ F.ChartRing := by
  have hf : (X.structureMap.appLE ⊤ F.frame.openSet (by simp)).hom.Smooth :=
    X.structureMap.smooth_appLE (isAffineOpen_top ComplexBase) F.frame.isAffine (by simp)
  have hg : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom.Smooth :=
    RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.symm.bijective
  apply RingHom.smooth_algebraMap.mp
  change ((X.structureMap.appLE ⊤ F.frame.openSet (by simp)).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom).Smooth
  exact hg.comp hf

end EvaluateVectorProof

end EvaluateVectorProofSection

set_option backward.isDefEq.respectTransparency false in

/-- Evaluation of an intrinsic tangent section as a point derivation. -/
def evaluateVector (v : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) :
    F.Tangent :=
  ⟨{ toFun := fun a => F.evaluation (tangentActs X.structureMap F.frame.openSet v a)
     map_add' := by
       intro a b
       rw [tangentActs_add_function]
       exact F.evaluation.map_add _ _
     map_smul' := by
       intro c a
       change F.evaluation (tangentActs X.structureMap F.frame.openSet v
           (complexConstant X.structureMap F.frame.openSet c *
             (show RingSections X.scheme F.frame.openSet from a))) =
         c * F.evaluation (tangentActs X.structureMap F.frame.openSet v a)
       rw [LeBrunSalamon.PhaseTwentyFive.TangentActionProof.leibniz,
         EvaluateVectorProof.action_constant,
         mul_zero, add_zero]
       have hm : F.evaluation
           (complexConstant X.structureMap F.frame.openSet c *
             tangentActs X.structureMap F.frame.openSet v a) =
           F.evaluation (complexConstant X.structureMap F.frame.openSet c) *
             F.evaluation (tangentActs X.structureMap F.frame.openSet v a) :=
         F.evaluation.map_mul
           (show F.ChartRing from complexConstant X.structureMap F.frame.openSet c)
           (show F.ChartRing from tangentActs X.structureMap F.frame.openSet v a)
       have hc : F.evaluation (complexConstant X.structureMap F.frame.openSet c) = c :=
         F.evaluation.commutes c
       exact hm.trans (congrArg (fun z : ℂ =>
         z * F.evaluation (tangentActs X.structureMap F.frame.openSet v a)) hc) }, by
     intro a b
     change F.evaluation (tangentActs X.structureMap F.frame.openSet v (a * b)) =
       F.evaluation a * F.evaluation (tangentActs X.structureMap F.frame.openSet v b) +
         F.evaluation b * F.evaluation (tangentActs X.structureMap F.frame.openSet v a)
     rw [LeBrunSalamon.PhaseTwentyFive.TangentActionProof.leibniz]
     let D : F.ChartRing → F.ChartRing := fun a =>
       show F.ChartRing from tangentActs X.structureMap F.frame.openSet v a
     have hs : F.evaluation (a * D b + b * D a) =
         F.evaluation (a * D b) + F.evaluation (b * D a) :=
       F.evaluation.map_add (a * D b) (b * D a)
     exact hs.trans (congrArg₂ (fun r s : ℂ => r + s)
       (F.evaluation.map_mul a (D b))
       (F.evaluation.map_mul b (D a)))⟩

section AffineVectorScalars

/-- The chart alias acts by the original structure-sheaf action on the
intrinsic tangent sections. This local instance changes no scalar action. -/
local instance chartTangentModule :
    Module F.ChartRing (SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) :=
  inferInstanceAs (Module (RingSections X.scheme F.frame.openSet)
    (SectionsOn (tangentSheaf X.structureMap) F.frame.openSet))

theorem evaluateVector_surjective : Function.Surjective F.evaluateVector := by
  letI : Algebra.Smooth ℂ F.ChartRing := EvaluateVectorProof.chartRing_smooth F
  intro D
  obtain ⟨V, hV⟩ := LeBrunSalamon.PhaseThirtyOne.regularVectorFields_lift_pointDerivations
    F.evaluation (⟨D.val, D.property⟩ : AffineTangentAt F.ChartRing F.evaluation)
  have hmul (a b : F.ChartRing) : V (a * b) = a * V b + b * V a := by
    simpa only [smul_eq_mul] using V.leibniz a b
  obtain ⟨v, hv⟩ := EvaluateVectorProof.affine_tangent_action_exists X.structureMap
    F.frame.openSet F.frame.isAffine (fun a => V a) (map_zero V)
    (fun a b => map_add V a b)
    (fun a b => hmul a b)
    (fun c => V.map_algebraMap c)
  refine ⟨v, ?_⟩
  apply Subtype.ext
  apply LinearMap.ext
  intro a
  change F.evaluation (tangentActs X.structureMap F.frame.openSet v a) = D.val a
  have ha : (show F.ChartRing from
      tangentActs X.structureMap F.frame.openSet v a) = V a := hv a
  exact (congrArg F.evaluation ha).trans (hV a)

theorem evaluateVector_sub
    (u v : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) :
    F.evaluateVector (u - v) = F.evaluateVector u - F.evaluateVector v := by
  apply Subtype.ext
  apply LinearMap.ext
  intro a
  change F.evaluation (tangentActs X.structureMap F.frame.openSet (u - v) a) =
    F.evaluation (tangentActs X.structureMap F.frame.openSet u a) -
      F.evaluation (tangentActs X.structureMap F.frame.openSet v a)
  have ha : (show F.ChartRing from
      tangentActs X.structureMap F.frame.openSet (u - v) a) =
      (show F.ChartRing from tangentActs X.structureMap F.frame.openSet u a) -
        (show F.ChartRing from tangentActs X.structureMap F.frame.openSet v a) :=
    TangentActionProof.sub_field X.structureMap F.frame.openSet u v a
  exact (congrArg F.evaluation ha).trans
    (F.evaluation.map_sub
      (show F.ChartRing from tangentActs X.structureMap F.frame.openSet u a)
      (show F.ChartRing from tangentActs X.structureMap F.frame.openSet v a))

theorem evaluateVector_smul (a : F.ChartRing)
    (v : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) :
    F.evaluateVector (a • v) = F.evaluation a • F.evaluateVector v := by
  apply Subtype.ext
  apply LinearMap.ext
  intro b
  change F.evaluation (tangentActs X.structureMap F.frame.openSet (a • v) b) =
    F.evaluation a * F.evaluation (tangentActs X.structureMap F.frame.openSet v b)
  have ha : (show F.ChartRing from
      tangentActs X.structureMap F.frame.openSet (a • v) b) =
      a * (show F.ChartRing from tangentActs X.structureMap F.frame.openSet v b) :=
    TangentActionProof.smul_field X.structureMap F.frame.openSet v a b
  exact (congrArg F.evaluation ha).trans
    (F.evaluation.map_mul a
      (show F.ChartRing from tangentActs X.structureMap F.frame.openSet v b))

section AffineVectorComparison

set_option backward.isDefEq.respectTransparency false

/-- The intrinsic vector's action on the affine coordinate ring, keeping
the actual complex algebra structure of the frame. -/
def affineVectorMap :
    SectionsOn (tangentSheaf X.structureMap) F.frame.openSet →ₗ[F.ChartRing]
      AffineVectorFields F.ChartRing where
  toFun v :=
    { toLinearMap :=
        { toFun := tangentActs X.structureMap F.frame.openSet v
          map_add' := TangentActionProof.add_function X.structureMap F.frame.openSet v
          map_smul' := by
            intro c a
            change RingSections X.scheme F.frame.openSet at a
            change tangentActs X.structureMap F.frame.openSet v
                (complexConstant X.structureMap F.frame.openSet c * a) =
              complexConstant X.structureMap F.frame.openSet c *
                tangentActs X.structureMap F.frame.openSet v a
            rw [TangentActionProof.leibniz, EvaluateVectorProof.action_constant,
              mul_zero, add_zero] }
      map_one_eq_zero' := by
        have h1 : complexConstant X.structureMap F.frame.openSet 1 =
            (1 : RingSections X.scheme F.frame.openSet) := F.constants.map_one
        exact (congrArg (tangentActs X.structureMap F.frame.openSet v) h1).symm.trans
          (EvaluateVectorProof.action_constant X.structureMap F.frame.openSet v 1)
      leibniz' := TangentActionProof.leibniz X.structureMap F.frame.openSet v }
  map_add' u v := by
    apply Derivation.ext
    intro a
    exact TangentActionProof.add_field X.structureMap F.frame.openSet u v a
  map_smul' a v := by
    apply Derivation.ext
    intro b
    exact TangentActionProof.smul_field X.structureMap F.frame.openSet v a b

theorem affineVectorMap_bijective : Function.Bijective F.affineVectorMap := by
  constructor
  · intro u v h
    apply EvaluateVectorProof.affine_tangent_action_faithful X.structureMap
      F.frame.openSet F.frame.isAffine u v
    intro a
    exact congrArg (fun D : AffineVectorFields F.ChartRing => D a) h
  · intro D
    have hmul (a b : F.ChartRing) : D (a * b) = a * D b + b * D a := by
      simpa only [smul_eq_mul] using D.leibniz a b
    obtain ⟨v, hv⟩ := EvaluateVectorProof.affine_tangent_action_exists X.structureMap
      F.frame.openSet F.frame.isAffine (fun a => D a) (map_zero D)
      (fun a b => map_add D a b)
      (fun a b => hmul a b)
      (fun c => D.map_algebraMap c)
    refine ⟨v, ?_⟩
    apply Derivation.ext
    exact hv

/-- The canonical affine tangent/derivation comparison, with no choice of
coordinates or abstract vector-space identification. -/
def affineVectorEquiv :
    SectionsOn (tangentSheaf X.structureMap) F.frame.openSet ≃ₗ[F.ChartRing]
      AffineVectorFields F.ChartRing :=
  LinearEquiv.ofBijective F.affineVectorMap F.affineVectorMap_bijective

theorem affineVectorEquiv_apply
    (v : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) (a : F.ChartRing) :
    F.affineVectorEquiv v a = tangentActs X.structureMap F.frame.openSet v a := rfl

theorem affineVectorEquiv_bracket
    (u v : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) :
    F.affineVectorEquiv (tangentBracket X.structureMap F.frame.openSet u v) =
      ⁅F.affineVectorEquiv u, F.affineVectorEquiv v⁆ := by
  apply Derivation.ext
  intro a
  exact tangentBracket_spec X.structureMap F.frame.openSet u v a

/-- Evaluation of regular affine derivations as the same point-derivation
space used by `evaluateVector`. -/
def evaluateAffineVector : AffineVectorFields F.ChartRing →ₗ[ℂ] F.Tangent where
  toFun V :=
    ⟨F.evaluation.toLinearMap.comp V.toLinearMap, by
      intro a b
      change F.evaluation (V (a * b)) =
        F.evaluation a * F.evaluation (V b) + F.evaluation b * F.evaluation (V a)
      rw [Derivation.leibniz]
      simp only [smul_eq_mul, map_add, map_mul]⟩
  map_add' V W := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    exact F.evaluation.map_add (V a) (W a)
  map_smul' c V := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    exact F.evaluation.toLinearMap.map_smul c (V a)

theorem evaluateAffineVector_intrinsic
    (v : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) :
    F.evaluateAffineVector (F.affineVectorEquiv v) = F.evaluateVector v := by
  apply Subtype.ext
  apply LinearMap.ext
  intro a
  rfl

theorem evaluateAffineVector_surjective : Function.Surjective F.evaluateAffineVector := by
  intro D
  obtain ⟨v, hv⟩ := F.evaluateVector_surjective D
  exact ⟨F.affineVectorEquiv v, (F.evaluateAffineVector_intrinsic v).trans hv⟩

/-- Evaluate a regular covector on a regular vector and then at the chosen
point; the restriction of scalars is the given complex structure. -/
def evaluatedCovector (α : AffineOneForm F.ChartRing) :
    AffineVectorFields F.ChartRing →ₗ[ℂ] ℂ :=
  F.evaluation.toLinearMap.comp (α.restrictScalars ℂ)

theorem evaluatedCovector_ker (α : AffineOneForm F.ChartRing) :
    LinearMap.ker F.evaluateAffineVector ≤ LinearMap.ker (F.evaluatedCovector α) := by
  letI : Algebra.Smooth ℂ F.ChartRing := EvaluateVectorProof.chartRing_smooth F
  intro V hV
  change F.evaluation (α V) = 0
  apply LeBrunSalamon.PhaseThirteen.AffineVelocityProof.point_zero_covector F.evaluation V
  intro a
  exact congrArg (fun D : F.Tangent => D.val a)
    (show F.evaluateAffineVector V = 0 from hV)

/-- Finite projectivity of the actual affine cotangent module makes every
regular covector descend to the point-derivation quotient. -/
def covectorAtPoint (α : AffineOneForm F.ChartRing) : F.Tangent →ₗ[ℂ] ℂ :=
  (F.evaluateAffineVector.liftOfSurjective F.evaluateAffineVector_surjective)
    ⟨F.evaluatedCovector α, F.evaluatedCovector_ker α⟩

theorem covectorAtPoint_evaluate (α : AffineOneForm F.ChartRing)
    (V : AffineVectorFields F.ChartRing) :
    F.covectorAtPoint α (F.evaluateAffineVector V) = F.evaluation (α V) := by
  exact LinearMap.equivOfSurjective_apply F.evaluateAffineVector_surjective
    (F.evaluatedCovector_ker α)

/-- Pointwise evaluation of an arbitrary regular bilinear form. -/
def evaluatedBilinear
    (b : AffineVectorFields F.ChartRing →ₗ[F.ChartRing] AffineOneForm F.ChartRing) :
    AffineVectorFields F.ChartRing →ₗ[ℂ] (AffineVectorFields F.ChartRing →ₗ[ℂ] ℂ) where
  toFun V := F.evaluatedCovector (b V)
  map_add' V W := by
    apply LinearMap.ext
    intro Z
    change F.evaluation (b (V + W) Z) = F.evaluation (b V Z) + F.evaluation (b W Z)
    rw [map_add, LinearMap.add_apply, map_add]
  map_smul' c V := by
    apply LinearMap.ext
    intro W
    change F.evaluation (b ((algebraMap ℂ F.ChartRing c) • V) W) =
      c * F.evaluation (b V W)
    rw [b.map_smul]
    change F.evaluation (algebraMap ℂ F.ChartRing c * b V W) =
      c * F.evaluation (b V W)
    rw [map_mul, F.evaluation.commutes, Algebra.algebraMap_self_apply]

theorem evaluatedBilinear_kers
    (b : AffineVectorFields F.ChartRing →ₗ[F.ChartRing] AffineOneForm F.ChartRing) :
    LinearMap.ker F.evaluateAffineVector ≤ LinearMap.ker (F.evaluatedBilinear b) ∧
      LinearMap.ker F.evaluateAffineVector ≤ LinearMap.ker (F.evaluatedBilinear b).flip := by
  letI : Algebra.Smooth ℂ F.ChartRing := EvaluateVectorProof.chartRing_smooth F
  constructor
  · intro V hV
    apply LinearMap.ext
    intro W
    change F.evaluation (b V W) = 0
    apply LeBrunSalamon.PhaseThirteen.AffineVelocityProof.point_zero_covector
      F.evaluation V (α := b.flip W)
    intro a
    exact congrArg (fun D : F.Tangent => D.val a)
      (show F.evaluateAffineVector V = 0 from hV)
  · intro W hW
    apply LinearMap.ext
    intro V
    exact F.evaluatedCovector_ker (b V) hW

/-- Descend both arguments through the actual point-evaluation map. The
kernel conditions are derived from finite projective duality. -/
def bilinearAtPoint
    (b : AffineVectorFields F.ChartRing →ₗ[F.ChartRing] AffineOneForm F.ChartRing) :
    F.Tangent →ₗ[ℂ] (F.Tangent →ₗ[ℂ] ℂ) :=
  let q := F.evaluateAffineVector.quotKerEquivOfSurjective F.evaluateAffineVector_surjective
  ((F.evaluatedBilinear b).liftQ₂ (LinearMap.ker F.evaluateAffineVector)
    (LinearMap.ker F.evaluateAffineVector) (F.evaluatedBilinear_kers b).1
    (F.evaluatedBilinear_kers b).2).compl₁₂ q.symm.toLinearMap q.symm.toLinearMap

theorem bilinearAtPoint_evaluate
    (b : AffineVectorFields F.ChartRing →ₗ[F.ChartRing] AffineOneForm F.ChartRing)
    (V W : AffineVectorFields F.ChartRing) :
    F.bilinearAtPoint b (F.evaluateAffineVector V) (F.evaluateAffineVector W) =
      F.evaluation (b V W) := by
  simp only [bilinearAtPoint, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, LinearMap.liftQ₂_mk] <;> rfl

end AffineVectorComparison

end AffineVectorScalars

/-- The first fat point is contained in every open neighborhood of its support. -/
theorem fatPoint_in_frame :
    (pointPowerInclusion x 2) ⁻¹ᵁ F.frame.openSet = ⊤ := by
  apply FatPointOpenFactorizationProof.pointPower_preimage_eq_top x 2 (by decide)
  have h : Set.range x.map ⊆ Set.range F.frame.openSet.ι := by
    rintro _ ⟨z, rfl⟩
    refine ⟨F.pointLift z, ?_⟩
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun f : ComplexBase ⟶ X.scheme => f z) F.overPoint
  simpa only [Scheme.Opens.range_ι] using h


/-- The intrinsic first-jet fibre; its source is the actual pullback of O_X. -/
abbrev JetFiber (_F : PointFrame X L x) :=
  (pullbackModule (pointPowerInclusion x 2) (structureModule X.scheme) ⟶
    pullbackModule (pointPowerInclusion x 2) L.sheaf)

/-- Restrict a LOCAL coefficient times the frame to the first fat point.
This explicit formula prevents normalization only on global sections, which
would be circular while proving that global sections generate all first jets. -/
def restrictLocal (a : F.ChartRing) : F.JetFiber :=
  let i := pointPowerInclusion x 2
  let s := pullLocalSection i L.sheaf F.frame.openSet (F.frame.coefficient.symm a)
  unitPullbackMap i ≫ sectionFromValue
    (show SectionsOn (pullbackModule i L.sheaf) ⊤ from F.fatPoint_in_frame ▸ s)

section LocalFrameJetProofSection

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LocalFrameJetProof

open Opposite

/-- The actual affine global-section equivalence reflects isomorphisms of
quasi-coherent module sheaves on a spectrum. -/
theorem spec_isIso_of_appTop_bijective {R : CommRingCat}
    {E G : OModule (Spec R)} [E.IsQuasicoherent] [G.IsQuasicoherent]
    (p : E ⟶ G) (hp : Function.Bijective (p.app ⊤)) : IsIso p := by
  let Q := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let E' : Q.FullSubcategory := ⟨E, inferInstance⟩
  let G' : Q.FullSubcategory := ⟨G, inferInstance⟩
  let p' : E' ⟶ G' := ObjectProperty.homMk p
  haveI : IsIso ((tildeEquiv (R := R)).inverse.map p') := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact hp
  haveI : IsIso p' := isIso_of_reflects_iso p' (tildeEquiv (R := R)).inverse
  change IsIso (Q.ι.map p')
  infer_instance

/-- Reflection on an arbitrary affine scheme uses its actual canonical
spectrum chart, including the canonical restriction comparisons. -/
theorem affine_isIso_of_appTop_bijective {Y : Scheme} [IsAffine Y]
    {E G : OModule Y} [E.IsQuasicoherent] [G.IsQuasicoherent]
    (p : E ⟶ G) (hp : Function.Bijective (p.app ⊤)) : IsIso p := by
  let e := Y.isoSpec
  let A := Scheme.Modules.restrictFunctor e.inv
  let B := Scheme.Modules.restrictFunctor e.hom
  let q := A.map p
  have hq : Function.Bijective (q.app ⊤) := by
    change Function.Bijective (p.app (e.inv ''ᵁ ⊤))
    have htop : e.inv ''ᵁ ⊤ = ⊤ :=
      (Scheme.Hom.image_top_eq_opensRange e.inv).trans
        (Scheme.Hom.opensRange_of_isIso e.inv)
    erw [htop]
    exact hp
  letI : IsIso q := spec_isIso_of_appTop_bijective q hq
  let c : A ⋙ B ≅ 𝟭 (OModule Y) :=
    (Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫
      Scheme.Modules.restrictFunctorId
  have heq : p = c.inv.app E ≫ B.map q ≫ c.hom.app G := by
    have h := c.hom.naturality p
    simpa only [q, Functor.id_obj, Functor.id_map, Functor.comp_map,
      ← Category.assoc, Iso.inv_hom_id_app,
      Category.id_comp] using congrArg (fun a => c.inv.app E ≫ a) h.symm
  rw [heq]
  infer_instance

private theorem over_eq_terminal {Y : Scheme} {U : Y.Opens}
    (W : Over U) (h : W.left = U) : W = Over.mk (𝟙 U) := by
  obtain ⟨V, i, rfl⟩ := Over.mk_surjective W
  change V = U at h
  subst V
  exact congrArg (fun i : U ⟶ U => Over.mk i) (Subsingleton.elim _ _)

/-- A morphism on an affine over-site is invertible whenever its actual
section map on the entire open is bijective. -/
theorem affine_over_isIso_of_bijective {Y : Scheme} {E G : OModule Y}
    [E.IsQuasicoherent] [G.IsQuasicoherent] (U : Y.Opens) (hU : IsAffineOpen U)
    (p : E.over U ⟶ G.over U)
    (hp : Function.Bijective (p.val.app (op (Over.mk (𝟙 U))))) : IsIso p := by
  let A := (Scheme.Modules.overEquiv U).functor
  letI : IsAffine U.toScheme := hU
  letI : (A.obj (E.over U)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.overFunctorEquiv U).app E).symm inferInstance
  letI : (A.obj (G.over U)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.overFunctorEquiv U).app G).symm inferInstance
  have htop : U.overEquivalence.inverse.obj ⊤ = Over.mk (𝟙 U) := by
    apply over_eq_terminal
    change U.ι ''ᵁ ⊤ = U
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have hAp : Function.Bijective ((A.map p).app ⊤) := by
    change Function.Bijective (p.val.app (op (U.overEquivalence.inverse.obj ⊤)))
    rw [htop]
    exact hp
  letI : IsIso (A.map p) := affine_isIso_of_appTop_bijective (A.map p) hAp
  exact isIso_of_reflects_iso p A

/-- The local unit morphism determined by the supplied coefficient frame.
It is constructed from that frame's value at one, without choosing a new frame. -/
def frameMap {Y : Scheme} {M : LineBundle Y} (H : AffineLineFrame M) :
    (structureModule Y).over H.openSet ⟶ M.sheaf.over H.openSet :=
  (ExtensionGluing.UnitOnOpen.unitOverHomEquiv M.sheaf H.openSet).symm
    (H.coefficient.symm 1)

theorem frameMap_apply {Y : Scheme} {M : LineBundle Y}
    (H : AffineLineFrame M) (a : RingSections Y H.openSet) :
    (frameMap H).val.app (op (Over.mk (𝟙 H.openSet))) a = H.coefficient.symm a := by
  have h1 : (frameMap H).val.app (op (Over.mk (𝟙 H.openSet)))
      (1 : RingSections Y H.openSet) =
      H.coefficient.symm 1 :=
    (ExtensionGluing.UnitOnOpen.unitOverHomEquiv M.sheaf H.openSet).apply_symm_apply _
  calc
    _ = a • (frameMap H).val.app (op (Over.mk (𝟙 H.openSet)))
        (1 : RingSections Y H.openSet) := by
      simpa only [smul_eq_mul, mul_one] using
        ((frameMap H).val.app (op (Over.mk (𝟙 H.openSet)))).hom.map_smul a
          (1 : RingSections Y H.openSet)
    _ = H.coefficient.symm a := by
      rw [h1, ← H.coefficient.symm.map_smul]
      simp only [smul_eq_mul, mul_one]

theorem frameMap_isIso {Y : Scheme} {M : LineBundle Y}
    (H : AffineLineFrame M) : IsIso (frameMap H) := by
  letI : (structureModule Y).IsQuasicoherent :=
    LocalExtensionSplitting.quasicoherent_of_locallyFreeRank (structureModule_rank Y)
  letI : M.sheaf.IsQuasicoherent :=
    LocalExtensionSplitting.quasicoherent_of_locallyFreeRank M.locallyFree
  apply affine_over_isIso_of_bijective H.openSet H.isAffine
  constructor
  · intro a b hab
    exact H.coefficient.symm.injective
      ((frameMap_apply H a).symm.trans (hab.trans (frameMap_apply H b)))
  · intro b
    obtain ⟨a, ha⟩ := H.coefficient.symm.surjective b
    exact ⟨a, (frameMap_apply H a).trans ha⟩

def frameIso {Y : Scheme} {M : LineBundle Y} (H : AffineLineFrame M) :
    (structureModule Y).over H.openSet ≅ M.sheaf.over H.openSet := by
  letI := frameMap_isIso H
  exact asIso (frameMap H)

/-- Pullback of a genuine local morphism, defined by the normalized local
adjunction. This works on every open and along every scheme morphism. -/
def pullOverHom {Y Z : Scheme} (f : Z ⟶ Y) (U : Y.Opens)
    {E G : OModule Y} (p : E.over U ⟶ G.over U) :
    (pullbackModule f E).over (f ⁻¹ᵁ U) ⟶ (pullbackModule f G).over (f ⁻¹ᵁ U) :=
  (PullbackPairProof.localPullbackHomEquiv f E (pullbackModule f G) U).symm
    (p ≫ ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).over U)

theorem pullOverHom_unit {Y Z : Scheme} (f : Z ⟶ Y) (U : Y.Opens)
    {E G : OModule Y} (p : E.over U ⟶ G.over U)
    (W : Over U) (a : SectionsOn E W.left) :
    (pullOverHom f U p).val.app
        (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W))
        (pullLocalSection f E W.left a) =
      pullLocalSection f G W.left (p.val.app (op W) a) := by
  have h := (PullbackPairProof.localPullbackHomEquiv f E (pullbackModule f G) U).apply_symm_apply
      (p ≫ ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).over U)
  rw [PullbackPairProof.localPullbackHomEquiv_eq_unitPrecompose] at h
  exact congrArg (fun q : E.over U ⟶
    ((Scheme.Modules.pushforward f).obj (pullbackModule f G)).over U =>
      q.val.app (op W) a) h

theorem pullOverHom_id {Y Z : Scheme} (f : Z ⟶ Y) (U : Y.Opens)
    (E : OModule Y) : pullOverHom f U (𝟙 (E.over U)) = 𝟙 _ := by
  apply (PullbackPairProof.localUnitPrecompose_bijective f E (pullbackModule f E) U).injective
  apply SheafOfModules.hom_ext
  ext W a
  change (pullOverHom f U (𝟙 (E.over U))).val.app
      (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W.unop))
      (pullLocalSection f E W.unop.left a) = pullLocalSection f E W.unop.left a
  rw [pullOverHom_unit]
  rfl

theorem pullOverHom_comp {Y Z : Scheme} (f : Z ⟶ Y) (U : Y.Opens)
    {E G H : OModule Y} (p : E.over U ⟶ G.over U) (q : G.over U ⟶ H.over U) :
    pullOverHom f U (p ≫ q) = pullOverHom f U p ≫ pullOverHom f U q := by
  apply (PullbackPairProof.localUnitPrecompose_bijective f E (pullbackModule f H) U).injective
  apply SheafOfModules.hom_ext
  ext W a
  change (pullOverHom f U (p ≫ q)).val.app
      (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W.unop))
      (pullLocalSection f E W.unop.left a) =
    (pullOverHom f U q).val.app
      (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W.unop))
      ((pullOverHom f U p).val.app
        (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W.unop))
        (pullLocalSection f E W.unop.left a))
  rw [pullOverHom_unit, pullOverHom_unit, pullOverHom_unit]
  rfl

def pullOverIso {Y Z : Scheme} (f : Z ⟶ Y) (U : Y.Opens)
    {E G : OModule Y} (e : E.over U ≅ G.over U) :
    (pullbackModule f E).over (f ⁻¹ᵁ U) ≅ (pullbackModule f G).over (f ⁻¹ᵁ U) where
  hom := pullOverHom f U e.hom
  inv := pullOverHom f U e.inv
  hom_inv_id := by rw [← pullOverHom_comp, e.hom_inv_id, pullOverHom_id]
  inv_hom_id := by rw [← pullOverHom_comp, e.inv_hom_id, pullOverHom_id]

/-- The canonical unit comparison takes the local adjunction unit to the
actual structure-sheaf restriction, on every local scalar. -/
theorem unitPullbackMap_local {Y Z : Scheme} (f : Z ⟶ Y)
    (U : Y.Opens) (a : RingSections Y U) :
    (unitPullbackMap f).app (f ⁻¹ᵁ U)
      (pullLocalSection f (structureModule Y) U a) = f.app U a := by
  have h := unitPullbackMap_adjoint f
  exact congrArg (fun q : structureModule Y ⟶
    (Scheme.Modules.pushforward f).obj (structureModule Z) => q.app U a) h

/-- The transported coefficient frame on the actual inverse-image open. -/
def pulledCoefficient {Y Z : Scheme} {M : LineBundle Y}
    (H : AffineLineFrame M) (f : Z ⟶ Y) :
    SectionsOn (pullbackModule f M.sheaf) (f ⁻¹ᵁ H.openSet) ≃ₗ[RingSections Z (f ⁻¹ᵁ H.openSet)]
      RingSections Z (f ⁻¹ᵁ H.openSet) :=
  (((SheafOfModules.evaluation (Z.ringCatSheaf.over (f ⁻¹ᵁ H.openSet))
    (op (Over.mk (𝟙 (f ⁻¹ᵁ H.openSet))))).mapIso
      (pullOverIso f H.openSet (frameIso H))).symm ≪≫
    (((SheafOfModules.evaluation Z.ringCatSheaf (op (f ⁻¹ᵁ H.openSet))).mapIso
      (unitPullbackIso f)))).toLinearEquiv

theorem pulledCoefficient_local {Y Z : Scheme} {M : LineBundle Y}
    (H : AffineLineFrame M) (f : Z ⟶ Y) (a : RingSections Y H.openSet) :
    pulledCoefficient H f (pullLocalSection f M.sheaf H.openSet (H.coefficient.symm a)) =
      f.app H.openSet a := by
  let V := f ⁻¹ᵁ H.openSet
  let e := pullOverIso f H.openSet (frameIso H)
  have hn : e.hom.val.app (op (Over.mk (𝟙 V)))
      (pullLocalSection f (structureModule Y) H.openSet a) =
    pullLocalSection f M.sheaf H.openSet (H.coefficient.symm a) := by
    have h :=
      pullOverHom_unit f H.openSet (frameMap H) (Over.mk (𝟙 H.openSet)) a
    change (pullOverHom f H.openSet (frameMap H)).val.app
        (op (Over.mk ((TopologicalSpace.Opens.map f.base).map (𝟙 H.openSet))))
        (pullLocalSection f (structureModule Y) H.openSet a) =
      pullLocalSection f M.sheaf H.openSet
        ((frameMap H).val.app (op (Over.mk (𝟙 H.openSet))) a) at h
    have hid : (TopologicalSpace.Opens.map f.base).map (𝟙 H.openSet) = 𝟙 V :=
      (TopologicalSpace.Opens.map f.base).map_id H.openSet
    erw [hid, frameMap_apply] at h
    exact h
  calc
    _ = (unitPullbackMap f).app V
        (pullLocalSection f (structureModule Y) H.openSet a) := by
      rw [← hn]
      change (unitPullbackMap f).app V
        (e.inv.val.app (op (Over.mk (𝟙 V)))
          (e.hom.val.app (op (Over.mk (𝟙 V))) _)) = _
      have hid := congrArg (fun q :
          (pullbackModule f (structureModule Y)).over V ⟶
            (pullbackModule f (structureModule Y)).over V =>
        q.val.app (op (Over.mk (𝟙 V)))
          (pullLocalSection f (structureModule Y) H.openSet a)) e.hom_inv_id
      exact congrArg ((unitPullbackMap f).app V) hid
    _ = f.app H.openSet a := unitPullbackMap_local f H.openSet a

private theorem cast_section_back {Y : Scheme} (E : OModule Y)
    {V : Y.Opens} (h : V = ⊤) (s : SectionsOn E V) :
    Equiv.cast (congrArg (fun W => SectionsOn E W) h.symm) (h ▸ s) = s := by
  subst V
  rfl

/-- An actual equivalence between the intrinsic line-valued fat-point
fibre and its scalar functions, using the given affine frame. -/
def jetScalarEquiv : F.JetFiber ≃
    RingSections (pointPowerSubscheme x 2)
      ((pointPowerInclusion x 2) ⁻¹ᵁ F.frame.openSet) :=
  ((Iso.homCongr (unitPullbackIso (pointPowerInclusion x 2))
      (Iso.refl (pullbackModule (pointPowerInclusion x 2) L.sheaf))).trans
    (LeBrunSalamon.PhaseTwentyEight.sectionEquiv
      (pullbackModule (pointPowerInclusion x 2) L.sheaf))).trans
    ((Equiv.cast (congrArg (fun W =>
      SectionsOn (pullbackModule (pointPowerInclusion x 2) L.sheaf) W)
        F.fatPoint_in_frame.symm)).trans
      (pulledCoefficient F.frame (pointPowerInclusion x 2)).toEquiv)

/-- The comparison fixes every local coefficient, including coefficients
which do not extend to a global section. -/
theorem jetScalarEquiv_restrictLocal (a : F.ChartRing) :
    jetScalarEquiv F (F.restrictLocal a) =
      (pointPowerInclusion x 2).app F.frame.openSet a := by
  let i := pointPowerInclusion x 2
  let s := pullLocalSection i L.sheaf F.frame.openSet (F.frame.coefficient.symm a)
  have hcancel (v : GlobalSections (pullbackModule i L.sheaf)) :
      sectionValue ((unitPullbackIso i).inv ≫ unitPullbackMap i ≫
        sectionFromValue v) = v := by
    change sectionValue ((unitPullbackIso i).inv ≫ (unitPullbackIso i).hom ≫
      sectionFromValue v) = v
    rw [Iso.inv_hom_id_assoc, sectionFromValue_spec]
  simp only [jetScalarEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_hom, Category.comp_id]
  change pulledCoefficient F.frame i
    (Equiv.cast (congrArg (fun W => SectionsOn (pullbackModule i L.sheaf) W)
      F.fatPoint_in_frame.symm)
      (sectionValue ((unitPullbackIso i).inv ≫ unitPullbackMap i ≫
        sectionFromValue (show SectionsOn (pullbackModule i L.sheaf) ⊤ from
          F.fatPoint_in_frame ▸ s)))) = _
  rw [hcancel, cast_section_back]
  exact pulledCoefficient_local F.frame i a

/-- The genuine line-valued restriction has precisely the scalar
fat-point kernel in the supplied frame. -/
theorem restrictLocal_equal_iff_scalar (a b : F.ChartRing) :
    F.restrictLocal a = F.restrictLocal b ↔
      (pointPowerInclusion x 2).app F.frame.openSet a =
        (pointPowerInclusion x 2).app F.frame.openSet b := by
  rw [← (jetScalarEquiv F).apply_eq_iff_eq,
    jetScalarEquiv_restrictLocal, jetScalarEquiv_restrictLocal]

end LocalFrameJetProof

end LocalFrameJetProofSection

theorem restrictLocal_surjective : Function.Surjective F.restrictLocal := by
  intro j
  obtain ⟨a, ha⟩ := IntrinsicJetAffineQuotientProof.pointPower_affine_restriction_surjective
    x F.frame.openSet F.frame.isAffine 2 (LocalFrameJetProof.jetScalarEquiv F j)
  refine ⟨a, (LocalFrameJetProof.jetScalarEquiv F).injective ?_⟩
  exact (LocalFrameJetProof.jetScalarEquiv_restrictLocal F a).trans ha


theorem restrictLocal_global (a : AlgebraicSection L.sheaf) :
    F.restrictLocal (F.coefficient a) = jetRestrictionAt x L.sheaf 1 a := by
  let i := pointPowerInclusion x 2
  have hs : F.frame.coefficient.symm (F.coefficient a) =
      L.sheaf.presheaf.map (homOfLE (show F.frame.openSet ≤ ⊤ from le_top)).op
        (sectionValue a) := by
    rw [coefficient, AffineLineFrame.localCoefficient,
      F.frame.coefficient.symm_apply_apply, ScalarSections.section_app_one]
  have hn := (sheafHom_naturality
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L.sheaf)
    (homOfLE (show F.frame.openSet ≤ ⊤ from le_top)) (sectionValue a)).symm
  change pullLocalSection i L.sheaf F.frame.openSet
      (L.sheaf.presheaf.map (homOfLE (show F.frame.openSet ≤ ⊤ from le_top)).op
        (sectionValue a)) =
    (pullbackModule i L.sheaf).presheaf.map
      (homOfLE (show i ⁻¹ᵁ F.frame.openSet ≤ ⊤ from le_top)).op
      (pullLocalSection i L.sheaf ⊤ (sectionValue a)) at hn
  have hcast (V : (pointPowerSubscheme x 2).Opens) (hV : V = ⊤)
      (z : SectionsOn (pullbackModule i L.sheaf) ⊤) :
      (show SectionsOn (pullbackModule i L.sheaf) ⊤ from hV ▸
        (pullbackModule i L.sheaf).presheaf.map
          (homOfLE (show V ≤ ⊤ from le_top)).op z) = z := by
    subst V
    change (pullbackModule i L.sheaf).presheaf.map (𝟙 (Opposite.op ⊤)) z = z
    rw [CategoryTheory.Functor.map_id]
    rfl
  have ht :
      (show SectionsOn (pullbackModule i L.sheaf) ⊤ from F.fatPoint_in_frame ▸
        pullLocalSection i L.sheaf F.frame.openSet
          (F.frame.coefficient.symm (F.coefficient a))) =
      sectionValue (pullSection i a) := by
    rw [hs, hn]
    exact (hcast (i ⁻¹ᵁ F.frame.openSet) F.fatPoint_in_frame
      (pullLocalSection i L.sheaf ⊤ (sectionValue a))).trans (pullSection_value i a).symm
  change unitPullbackMap i ≫ sectionFromValue
      (show SectionsOn (pullbackModule i L.sheaf) ⊤ from F.fatPoint_in_frame ▸
        pullLocalSection i L.sheaf F.frame.openSet
          (F.frame.coefficient.symm (F.coefficient a))) = restrictSection i a
  rw [ht, sectionFromValue_sectionValue]
  exact unitPullbackMap_pullSection i a


/-- Unique normalization on every local function, using actual restrictions. -/
theorem jetCoordinates_existsUnique :
    ∃! e : F.JetFiber ≃ TrivializedFirstJet F.Tangent,
      ∀ a : F.ChartRing, e (F.restrictLocal a) = F.localJet a := by
  classical
  have hker (a b : F.ChartRing) :
      F.restrictLocal a = F.restrictLocal b ↔ F.localJet a = F.localJet b :=
    (LocalFrameJetProof.restrictLocal_equal_iff_scalar F a b).trans
      (F.localJet_equal_iff_fatPoint a b).symm
  let c : F.JetFiber → TrivializedFirstJet F.Tangent := fun j =>
    F.localJet (Classical.choose (F.restrictLocal_surjective j))
  have hc (a : F.ChartRing) : c (F.restrictLocal a) = F.localJet a := by
    apply (hker _ a).mp
    exact Classical.choose_spec (F.restrictLocal_surjective (F.restrictLocal a))
  have hi : Function.Injective c := by
    intro j k h
    obtain ⟨a, rfl⟩ := F.restrictLocal_surjective j
    obtain ⟨b, rfl⟩ := F.restrictLocal_surjective k
    rw [hc, hc] at h
    exact (hker a b).mpr h
  have hs : Function.Surjective c := by
    intro j
    obtain ⟨a, ha⟩ := F.localJet_surjective j
    exact ⟨F.restrictLocal a, (hc a).trans ha⟩
  let e : F.JetFiber ≃ TrivializedFirstJet F.Tangent := Equiv.ofBijective c ⟨hi, hs⟩
  refine ⟨e, hc, ?_⟩
  intro e' he'
  apply Equiv.ext
  intro j
  obtain ⟨a, rfl⟩ := F.restrictLocal_surjective j
  exact (he' a).trans (hc a).symm


def jetCoordinates : F.JetFiber ≃ TrivializedFirstJet F.Tangent :=
  Classical.choose F.jetCoordinates_existsUnique

theorem jetCoordinates_local (a : F.ChartRing) :
    F.jetCoordinates (F.restrictLocal a) = F.localJet a :=
  (Classical.choose_spec F.jetCoordinates_existsUnique).1 a

theorem jetCoordinates_global (a : AlgebraicSection L.sheaf) :
    F.jetCoordinates (jetRestrictionAt x L.sheaf 1 a) = F.localJet (F.coefficient a) := by
  rw [← F.restrictLocal_global a]
  exact F.jetCoordinates_local (F.coefficient a)

end PointFrame

/-- Complex scalar multiplication of an ACTUAL global section. No new
C-module structure on the category of sheaves is postulated. -/
def scaleSection {d : ℕ} (X : SmoothProperComplexVariety d)
    {E : OModule X.scheme} (c : ℂ) (a : AlgebraicSection E) : AlgebraicSection E :=
  sectionFromValue (complexConstant X.structureMap ⊤ c • sectionValue a)

theorem scaleSection_add {d : ℕ} (X : SmoothProperComplexVariety d)
    {E : OModule X.scheme} (c : ℂ) (a b : AlgebraicSection E) :
    scaleSection X c (a+b) = scaleSection X c a + scaleSection X c b := by
  simp only [scaleSection, sectionValue_add, smul_add, sectionFromValue_add]

theorem scaleSection_one {d : ℕ} (X : SmoothProperComplexVariety d)
    {E : OModule X.scheme} (a : AlgebraicSection E) : scaleSection X 1 a = a := by
  unfold scaleSection
  have h : complexConstant X.structureMap ⊤ 1 = 1 :=
    (ScalarSections.constantsOn X.structureMap ⊤).map_one
  rw [h, one_smul, sectionFromValue_sectionValue]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem scaleSection_local {d : ℕ} (X : SmoothProperComplexVariety d)
    (L : LineBundle X.scheme) (F : AffineLineFrame L) (c : ℂ) (a : AlgebraicSection L.sheaf) :
    F.localCoefficient (scaleSection X c a) =
      complexConstant X.structureMap F.openSet c * F.localCoefficient a := by
  simp only [AffineLineFrame.localCoefficient, ScalarSections.section_app_one,
    scaleSection, sectionFromValue_spec]
  change F.coefficient
      (L.sheaf.val.map (homOfLE (show F.openSet ≤ ⊤ from le_top)).op
        (complexConstant X.structureMap ⊤ c • sectionValue a)) =
    complexConstant X.structureMap F.openSet c *
      F.coefficient (L.sheaf.val.map
        (homOfLE (show F.openSet ≤ ⊤ from le_top)).op (sectionValue a))
  rw [L.sheaf.val.map_smul, F.coefficient.map_smul]
  change X.scheme.presheaf.map
      (homOfLE (show F.openSet ≤ ⊤ from le_top)).op
        (complexConstant X.structureMap ⊤ c) *
      F.coefficient (L.sheaf.val.map
        (homOfLE (show F.openSet ≤ ⊤ from le_top)).op (sectionValue a)) =
    complexConstant X.structureMap F.openSet c *
      F.coefficient (L.sheaf.val.map
        (homOfLE (show F.openSet ≤ ⊤ from le_top)).op (sectionValue a))
  exact congrArg
    (fun q : RingSections X.scheme F.openSet => q *
      F.coefficient (L.sheaf.val.map
        (homOfLE (show F.openSet ≤ ⊤ from le_top)).op (sectionValue a)))
    (ScalarSections.complexConstant_restrict X.structureMap
      (homOfLE (show F.openSet ≤ ⊤ from le_top)) c)

/-- A finite coefficient vector at x, with its actual point-derivation map. -/
def coefficientJet {d : ℕ} {X : SmoothProperComplexVariety d} {L : LineBundle X.scheme}
    {B : ExternalSquareSections X L} (E : ExternalExpansion X L B)
    {x : ComplexPoint X} (F : PointFrame X L x) :
    SectionValuedFirstJet F.Tangent (Fin E.size → ℂ) where
  value i := F.evaluation (F.coefficient (E.left i))
  derivative := LinearMap.pi (fun i => F.differential (F.coefficient (E.left i)))

/-- lambda(e_i) are constant complex coefficients. This is a global
section of L, NOT a pointwise function or an assumed Hamiltonian. -/
def contraction {d : ℕ} {X : SmoothProperComplexVariety d} {L : LineBundle X.scheme}
    {B : ExternalSquareSections X L} (E : ExternalExpansion X L B)
    (ell : (Fin E.size → ℂ) →ₗ[ℂ] ℂ) : AlgebraicSection L.sheaf :=
  ∑ i, scaleSection X (ell (Pi.single i 1)) (E.left i)

/-- Pure finite-coordinate identity; no independence hypothesis on the expansion. -/
theorem functional_coordinate_sum (m : ℕ) (ell : (Fin m → ℂ) →ₗ[ℂ] ℂ)
    (v : Fin m → ℂ) : ell v = ∑ i, ell (Pi.single i 1) * v i := by
  have hv : v = ∑ i : Fin m, v i • Pi.single i (1 : ℂ) := by
    funext j
    simp [Pi.single_apply]
  calc
    ell v = ell (∑ i : Fin m, v i • Pi.single i (1 : ℂ)) := congrArg ell hv
    _ = ∑ i : Fin m, v i * ell (Pi.single i 1) := by
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
    _ = ∑ i : Fin m, ell (Pi.single i 1) * v i :=
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The commuting diagram needed at the END of jet:criterion, stated
independently of the contact hypothesis and without jet-surjectivity. -/
theorem contraction_firstJet {d : ℕ} {X : SmoothProperComplexVariety d}
    {L : LineBundle X.scheme} {B : ExternalSquareSections X L}
    (E : ExternalExpansion X L B) {x : ComplexPoint X} (F : PointFrame X L x)
    (ell : (Fin E.size → ℂ) →ₗ[ℂ] ℂ) :
    F.jetCoordinates (jetRestrictionAt x L.sheaf 1 (contraction E ell)) =
      (coefficientJet E F).contractedJet ell := by
  classical
  let c : AlgebraicSection L.sheaf →+ F.ChartRing := {
    toFun := F.coefficient
    map_zero' := by
      simp only [PointFrame.coefficient, AffineLineFrame.localCoefficient,
        ScalarSections.section_app_one, sectionValue_zero, map_zero]
    map_add' := by
      intro a b
      simp only [PointFrame.coefficient, AffineLineFrame.localCoefficient,
        ScalarSections.section_app_one, sectionValue_add, map_add] }
  have hc : F.coefficient (contraction E ell) =
      ∑ i, algebraMap ℂ F.ChartRing (ell (Pi.single i 1)) * F.coefficient (E.left i) := by
    change c (∑ i, scaleSection X (ell (Pi.single i 1)) (E.left i)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact scaleSection_local X L F.frame (ell (Pi.single i 1)) (E.left i)
  have hscalar (D : F.Tangent) (z : ℂ) (a : F.ChartRing) :
      D.val (algebraMap ℂ F.ChartRing z * a) = z * D.val a := by
    change D.val (z • a) = z • D.val a
    exact D.val.map_smul z a
  rw [F.jetCoordinates_global, PointFrame.localJet, hc]
  apply Prod.ext
  · change F.evaluation
        (∑ i, algebraMap ℂ F.ChartRing (ell (Pi.single i 1)) * F.coefficient (E.left i)) =
      ell (fun i => F.evaluation (F.coefficient (E.left i)))
    rw [map_sum]
    simp only [map_mul, AlgHom.commutes]
    exact (functional_coordinate_sum E.size ell
      (fun i => F.evaluation (F.coefficient (E.left i)))).symm
  · apply LinearMap.ext
    intro D
    change D.val
        (∑ i, algebraMap ℂ F.ChartRing (ell (Pi.single i 1)) * F.coefficient (E.left i)) =
      ell (fun i => D.val (F.coefficient (E.left i)))
    rw [map_sum]
    simp only [hscalar]
    exact (functional_coordinate_sum E.size ell
      (fun i => D.val (F.coefficient (E.left i)))).symm


/-- The scalar exterior differential is tensorial AFTER fixing the line frame.
Its sign is opposite the convention theta([u,v]) on the contact distribution. -/
def scalarExterior {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) {x : ComplexPoint X}
    (F : PointFrame X C.sequence.line x)
    (u v : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) : F.ChartRing :=
  tangentActs X.structureMap F.frame.openSet u (localContactValue C F.frame v) -
  tangentActs X.structureMap F.frame.openSet v (localContactValue C F.frame u) -
  localContactValue C F.frame (tangentBracket X.structureMap F.frame.openSet u v)

theorem localContactValue_sub {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) (H : AffineLineFrame C.sequence.line)
    (u v : SectionsOn (tangentSheaf X.structureMap) H.openSet) :
    localContactValue C H (u - v) = localContactValue C H u - localContactValue C H v := by
  have hf : C.sequence.form.app H.openSet (u - v) =
      C.sequence.form.app H.openSet u - C.sequence.form.app H.openSet v :=
    map_sub (C.sequence.form.app H.openSet).hom u v
  change H.coefficient (C.sequence.form.app H.openSet (u - v)) =
    H.coefficient (C.sequence.form.app H.openSet u) -
      H.coefficient (C.sequence.form.app H.openSet v)
  exact (congrArg H.coefficient hf).trans
    (H.coefficient.map_sub (C.sequence.form.app H.openSet u)
      (C.sequence.form.app H.openSet v))

theorem localContactValue_smul {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) (H : AffineLineFrame C.sequence.line)
    (a : RingSections X.scheme H.openSet)
    (v : SectionsOn (tangentSheaf X.structureMap) H.openSet) :
    localContactValue C H (a • v) = a * localContactValue C H v := by
  have hf : C.sequence.form.app H.openSet (a • v) =
      a • C.sequence.form.app H.openSet v :=
    Scheme.Modules.Hom.app_smul C.sequence.form a v
  change H.coefficient (C.sequence.form.app H.openSet (a • v)) =
    a * H.coefficient (C.sequence.form.app H.openSet v)
  calc
    _ = H.coefficient (a • C.sequence.form.app H.openSet v) :=
      congrArg H.coefficient hf
    _ = a • H.coefficient (C.sequence.form.app H.openSet v) :=
      H.coefficient.map_smul a (C.sequence.form.app H.openSet v)
    _ = _ := rfl

theorem localContactValue_neg {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) (H : AffineLineFrame C.sequence.line)
    (v : SectionsOn (tangentSheaf X.structureMap) H.openSet) :
    localContactValue C H (-v) = -localContactValue C H v := by
  have hf : C.sequence.form.app H.openSet (-v) = -C.sequence.form.app H.openSet v :=
    map_neg (C.sequence.form.app H.openSet).hom v
  change H.coefficient (C.sequence.form.app H.openSet (-v)) =
    -H.coefficient (C.sequence.form.app H.openSet v)
  exact (congrArg H.coefficient hf).trans
    (H.coefficient.map_neg (C.sequence.form.app H.openSet v))

/-- The actual contact quotient has a section of scalar value one on each
affine line frame. This uses exactness and affine quasicoherent sections. -/
theorem localContactValue_unit {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) (H : AffineLineFrame C.sequence.line) :
    ∃ v : SectionsOn (tangentSheaf X.structureMap) H.openSet,
      localContactValue C H v = 1 := by
  letI : (intrinsicTangentBundle X).sheaf.IsQuasicoherent :=
    LocalExtensionSplitting.quasicoherent_of_locallyFreeRank
      (intrinsicTangentBundle X).locallyFree
  letI : C.sequence.line.sheaf.IsQuasicoherent :=
    LocalExtensionSplitting.quasicoherent_of_locallyFreeRank C.sequence.line.locallyFree
  letI : Epi C.sequence.form := C.sequence.shortExact.epi_g
  obtain ⟨v, hv⟩ := LocalExtensionSplitting.affine_sectionMap_surjective C.sequence.form
    H.openSet H.isAffine (H.coefficient.symm 1)
  refine ⟨v, ?_⟩
  unfold localContactValue
  rw [hv, H.coefficient.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Correct the affine lift of a scalar Hamiltonian using the actual Levi
isomorphism. The resulting local field preserves the contact distribution. -/
theorem localContactHamiltonian_exists {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) (H : AffineLineFrame C.sequence.line)
    (f : RingSections X.scheme H.openSet) :
    ∃ v : SectionsOn (tangentSheaf X.structureMap) H.openSet,
      localContactValue C H v = f ∧
        ∀ u : SectionsOn (tangentSheaf X.structureMap) H.openSet,
          localContactValue C H u = 0 →
            localContactValue C H (tangentBracket X.structureMap H.openSet v u) = 0 := by
  obtain ⟨r, hr⟩ := localContactValue_unit C H
  let w : SectionsOn (tangentSheaf X.structureMap) H.openSet := f • r
  let v := IntrinsicHamiltonianSurjectivityProof.correctedLift C H.openSet w
  refine ⟨v, ?_, ?_⟩
  · have hv := congrArg H.coefficient
      (IntrinsicHamiltonianSurjectivityProof.correctedLift_value C H.openSet w)
    change localContactValue C H v = localContactValue C H w at hv
    rw [hv]
    change localContactValue C H (f • r) = f
    rw [localContactValue_smul, hr, mul_one]
  · intro u hu
    have hform : C.sequence.form.app H.openSet u = 0 := by
      apply H.coefficient.injective
      change localContactValue C H u =
        H.coefficient (0 : SectionsOn C.sequence.line.sheaf H.openSet)
      exact hu.trans H.coefficient.map_zero.symm
    obtain ⟨z, hz⟩ := ContactClosureProof.exists_kernelSection C.sequence.inclusion
      C.sequence.form C.sequence.comp_zero C.sequence.shortExact H.openSet u hform
    have hcontact := IntrinsicHamiltonianSurjectivityProof.correctedLift_isContact
      C H.openSet w H.openSet (𝟙 H.openSet) z
    change C.sequence.form.app H.openSet (tangentBracket X.structureMap H.openSet
      ((tangentSheaf X.structureMap).presheaf.map (𝟙 H.openSet).op v)
      (C.sequence.inclusion.app H.openSet z)) = 0 at hcontact
    have hid : (tangentSheaf X.structureMap).presheaf.map (𝟙 H.openSet).op v = v := by simp
    rw [hid, hz] at hcontact
    change H.coefficient (C.sequence.form.app H.openSet
      (tangentBracket X.structureMap H.openSet v u)) = 0
    rw [hcontact, map_zero]

/-- The contact covector and exterior two-form are normalized on all local fields. -/
structure ContactAtPoint {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) {x : ComplexPoint X}
    (F : PointFrame X C.sequence.line x) where
  theta : F.Tangent →ₗ[ℂ] ℂ
  exterior : F.Tangent →ₗ[ℂ] (F.Tangent →ₗ[ℂ] ℂ)
  theta_normalized : ∀ v, theta (F.evaluateVector v) =
    F.evaluation (localContactValue C F.frame v)
  exterior_normalized : ∀ u v, exterior (F.evaluateVector u) (F.evaluateVector v) =
    F.evaluation (scalarExterior C F u v)

section ContactAtPointProofSection

set_option backward.isDefEq.respectTransparency false
attribute [local instance] PointFrame.chartTangentModule

namespace ContactAtPointProof

open LeBrunSalamon.PhaseEleven

/-- Cartan's formula is bilinear over the affine function ring. Its
function-linearity is the cancellation of the two Leibniz corrections. -/
def affineExteriorBilinear {A : Type*} [CommRing A] [Algebra ℂ A]
    (θ : AffineOneForm A) : AffineVectorFields A →ₗ[A] AffineOneForm A where
  toFun V :=
    { toFun := affineExteriorDerivativeValue θ V
      map_add' W Z := by
        change V (θ (W + Z)) - (W (θ V) + Z (θ V)) - θ ⁅V, W + Z⁆ =
          (V (θ W) - W (θ V) - θ ⁅V, W⁆) +
            (V (θ Z) - Z (θ V) - θ ⁅V, Z⁆)
        simp only [map_add, lie_add]
        ring
      map_smul' a W := by
        change affineExteriorDerivativeValue θ V (a • W) =
          a * affineExteriorDerivativeValue θ V W
        exact affineExteriorDerivative_smul_right θ a V W }
  map_add' V Z := by
    apply LinearMap.ext
    intro W
    change (V (θ W) + Z (θ W)) - W (θ (V + Z)) - θ ⁅V + Z, W⁆ =
      (V (θ W) - W (θ V) - θ ⁅V, W⁆) +
        (Z (θ W) - W (θ Z) - θ ⁅Z, W⁆)
    simp only [map_add, add_lie]
    ring
  map_smul' a V := by
    apply LinearMap.ext
    intro W
    change affineExteriorDerivativeValue θ (a • V) W =
      a * affineExteriorDerivativeValue θ V W
    exact affineExteriorDerivative_smul_left θ a V W

/-- The scalar contact form on the affine derivation module is transported
through the actual intrinsic tangent comparison. -/
def affineContactCovector {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) {x : ComplexPoint X}
    (F : PointFrame X C.sequence.line x) : AffineOneForm F.ChartRing where
  toFun V := localContactValue C F.frame (F.affineVectorEquiv.symm V)
  map_add' V W := by
    have hf : C.sequence.form.app F.frame.openSet
          (F.affineVectorEquiv.symm V + F.affineVectorEquiv.symm W) =
        C.sequence.form.app F.frame.openSet (F.affineVectorEquiv.symm V) +
          C.sequence.form.app F.frame.openSet (F.affineVectorEquiv.symm W) :=
      map_add (C.sequence.form.app F.frame.openSet).hom
        (F.affineVectorEquiv.symm V) (F.affineVectorEquiv.symm W)
    exact (congrArg (localContactValue C F.frame)
      (F.affineVectorEquiv.symm.map_add V W)).trans
      ((congrArg F.frame.coefficient hf).trans
        (F.frame.coefficient.map_add
          (C.sequence.form.app F.frame.openSet (F.affineVectorEquiv.symm V))
          (C.sequence.form.app F.frame.openSet (F.affineVectorEquiv.symm W))))
  map_smul' a V := by
    exact (congrArg (localContactValue C F.frame)
      (F.affineVectorEquiv.symm.map_smul a V)).trans
      (localContactValue_smul C F.frame
        (show RingSections X.scheme F.frame.openSet from a)
        (F.affineVectorEquiv.symm V))

theorem affineContactCovector_intrinsic {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) {x : ComplexPoint X}
    (F : PointFrame X C.sequence.line x)
    (v : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) :
    affineContactCovector C F (F.affineVectorEquiv v) = localContactValue C F.frame v := by
  change localContactValue C F.frame (F.affineVectorEquiv.symm (F.affineVectorEquiv v)) = _
  rw [F.affineVectorEquiv.symm_apply_apply]

theorem affineExterior_intrinsic {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) {x : ComplexPoint X}
    (F : PointFrame X C.sequence.line x)
    (u v : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) :
    affineExteriorDerivativeValue (affineContactCovector C F)
        (F.affineVectorEquiv u) (F.affineVectorEquiv v) = scalarExterior C F u v := by
  unfold affineExteriorDerivativeValue
  rw [← F.affineVectorEquiv_bracket, affineContactCovector_intrinsic,
    affineContactCovector_intrinsic, affineContactCovector_intrinsic] <;> rfl

end ContactAtPointProof

end ContactAtPointProofSection

/-- Existence is local differential geometry; uniqueness uses evaluated fields. -/
theorem contactAtPoint_exists {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) {x : ComplexPoint X}
    (F : PointFrame X C.sequence.line x) : Nonempty (ContactAtPoint C F) := by
  refine ⟨{
    theta := F.covectorAtPoint (ContactAtPointProof.affineContactCovector C F)
    exterior := F.bilinearAtPoint
      (ContactAtPointProof.affineExteriorBilinear (ContactAtPointProof.affineContactCovector C F))
    theta_normalized := ?_
    exterior_normalized := ?_ }⟩
  · intro v
    rw [← F.evaluateAffineVector_intrinsic v, F.covectorAtPoint_evaluate,
      ContactAtPointProof.affineContactCovector_intrinsic]
  · intro u v
    rw [← F.evaluateAffineVector_intrinsic u, ← F.evaluateAffineVector_intrinsic v,
      F.bilinearAtPoint_evaluate]
    change F.evaluation (LeBrunSalamon.PhaseEleven.affineExteriorDerivativeValue
      (ContactAtPointProof.affineContactCovector C F)
        (F.affineVectorEquiv u) (F.affineVectorEquiv v)) = _
    rw [ContactAtPointProof.affineExterior_intrinsic]

theorem contactAtPoint_unique {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) {x : ComplexPoint X}
    (F : PointFrame X C.sequence.line x) (A D : ContactAtPoint C F) :
    A.theta = D.theta ∧ A.exterior = D.exterior := by
  constructor
  · apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := F.evaluateVector_surjective w
    rw [A.theta_normalized, D.theta_normalized]
  · apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro z
    obtain ⟨u, rfl⟩ := F.evaluateVector_surjective w
    obtain ⟨v, rfl⟩ := F.evaluateVector_surjective z
    rw [A.exterior_normalized, D.exterior_normalized]


theorem contactAtPoint_nondegenerate {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) {x : ComplexPoint X}
    (F : PointFrame X C.sequence.line x) (A : ContactAtPoint C F) :
    A.theta ≠ 0 ∧ ∀ v, A.theta v = 0 →
      (∀ w, A.theta w = 0 → A.exterior v w = 0) → v = 0 := by
  obtain ⟨r, hr⟩ := localContactValue_unit C F.frame
  constructor
  · intro hz
    have hz' : A.theta (F.evaluateVector r) = 0 := by
      rw [hz, LinearMap.zero_apply]
    have hr' : (show F.ChartRing from localContactValue C F.frame r) = 1 := hr
    exact zero_ne_one (hz'.symm.trans
      ((A.theta_normalized r).trans
        ((congrArg F.evaluation hr').trans F.evaluation.map_one)))
  · intro v hv horth
    obtain ⟨u, hu⟩ := F.evaluateVector_surjective v
    have hvalue : F.evaluation (localContactValue C F.frame u) = 0 :=
      (A.theta_normalized u).symm.trans ((congrArg A.theta hu).trans hv)
    let u₀ : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet :=
      u - localContactValue C F.frame u • r
    have hu₀ : localContactValue C F.frame u₀ = 0 := by
      change localContactValue C F.frame (u - localContactValue C F.frame u • r) = 0
      rw [localContactValue_sub, localContactValue_smul, hr, mul_one, sub_self]
    have heval : F.evaluateVector u₀ = v := by
      have hscalar : F.evaluateVector (localContactValue C F.frame u • r) = 0 :=
        (F.evaluateVector_smul
          (show F.ChartRing from localContactValue C F.frame u) r).trans
          ((congrArg (fun z : ℂ => z • F.evaluateVector r) hvalue).trans
            (zero_smul ℂ (F.evaluateVector r)))
      exact (F.evaluateVector_sub u (localContactValue C F.frame u • r)).trans
        ((congrArg (fun z : F.Tangent => F.evaluateVector u - z) hscalar).trans
          ((sub_zero (F.evaluateVector u)).trans hu))
    have hzero (a : F.ChartRing) :
        F.evaluation (tangentActs X.structureMap F.frame.openSet u₀ a) = 0 := by
      let f : F.ChartRing := a - algebraMap ℂ F.ChartRing (F.evaluation a)
      have hf : F.evaluation f = 0 := by
        simp only [f, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
      obtain ⟨w, hw, hcontact⟩ := localContactHamiltonian_exists C F.frame f
      have hθw : A.theta (F.evaluateVector w) = 0 := by
        rw [A.theta_normalized, hw]
        exact hf
      have hpair : A.exterior (F.evaluateVector u₀) (F.evaluateVector w) = 0 := by
        rw [heval]
        exact horth (F.evaluateVector w) hθw
      have hbracket : localContactValue C F.frame
          (tangentBracket X.structureMap F.frame.openSet u₀ w) = 0 := by
        rw [tangentBracket_skew, localContactValue_neg, hcontact u₀ hu₀, neg_zero]
      have h := (A.exterior_normalized u₀ w).symm.trans hpair
      simp only [scalarExterior, hw, hu₀, TangentActionProof.zero_function,
        hbracket, sub_zero] at h
      have hcentered : tangentActs X.structureMap F.frame.openSet u₀ f =
          tangentActs X.structureMap F.frame.openSet u₀ a := by
        let a' : RingSections X.scheme F.frame.openSet := a
        change tangentActs X.structureMap F.frame.openSet u₀
            (a' - complexConstant X.structureMap F.frame.openSet (F.evaluation a)) =
          tangentActs X.structureMap F.frame.openSet u₀ a'
        rw [TangentActionProof.sub_function, PointFrame.EvaluateVectorProof.action_constant,
          sub_zero]
      have hcentered' :
          (show F.ChartRing from tangentActs X.structureMap F.frame.openSet u₀ f) =
            (show F.ChartRing from tangentActs X.structureMap F.frame.openSet u₀ a) := hcentered
      exact (congrArg F.evaluation hcentered').symm.trans h
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    exact (congrArg (fun D : F.Tangent => D.val a) heval).symm.trans (hzero a)

/-- OUTPUT of the coordinate Taylor calculation, not a definition of a kernel. The symmetric part of the
coefficient derivative depends on local coordinates. The contact covector and alternating part are
constrained by actual geometry. The comparison retains the complete first-slot quadratic coefficient. -/
structure TaylorRealization {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    {C : IntrinsicContactStructure X} (K : NormalizedContactKernel X C)
    (E : ExternalExpansion X C.sequence.line K.twoPointSection)
    {x : ComplexPoint X} (F : PointFrame X C.sequence.line x) where
  pointContact : ContactAtPoint C F
  coefficientData : ContactOneJet F.Tangent
  theta_eq : coefficientData.theta = pointContact.theta
  exterior_eq : ∀ u v, coefficientData.exteriorValue u v = pointContact.exterior u v
  compareCoefficients : ∀ v k,
    (coefficientJet E F).derivative v = k • (coefficientJet E F).value →
      Core.LocalJet.IsProjectiveKernelDirection F.Tangent coefficientData v k

/-- SOURCE nonvanishing of B_x in jet:criterion. Any finite expansion works:
if every first-factor coefficient vanishes at x, the whole slice vanishes. -/
theorem coefficient_value_nonzero {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    {C : IntrinsicContactStructure X} (K : NormalizedContactKernel X C)
    (E : ExternalExpansion X C.sequence.line K.twoPointSection)
    {x : ComplexPoint X} (F : PointFrame X C.sequence.line x) :
    (coefficientJet E F).value ≠ 0 := by
  intro hz
  have hz' (i : Fin E.size) : F.evaluation (F.coefficient (E.left i)) = 0 :=
    congrFun hz i
  let ev : RingSections X.scheme F.frame.openSet →+* ℂ := F.evaluation.toRingHom
  obtain ⟨v, hv⟩ := localContactValue_unit C F.frame
  have hh := normalizedSymbol_on_any_expansion C K.normalized E F.frame v v
  have hs : ev (E.secondSlotSecond F.frame v v) = 0 := by
    change ev (∑ i, F.frame.localCoefficient (E.left i) *
      tangentActs X.structureMap F.frame.openSet v
        (tangentActs X.structureMap F.frame.openSet v
          (F.frame.localCoefficient (E.right i)))) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    have hi0 : ev (F.frame.localCoefficient (E.left i)) = 0 := hz' i
    rw [map_mul, hi0, zero_mul]
  rw [hh, hv] at hs
  simp only [mul_one, map_ofNat] at hs
  norm_num at hs

section KernelTaylorProofSection

set_option backward.isDefEq.respectTransparency false

namespace KernelTaylorProof

open Core.ExternalTensorCoordinates
open LeBrunSalamon.PhaseNineteen

/-- Exchange symmetry supplies another expansion of the same section,
with the two actual global coefficient families interchanged. -/
def flippedExpansion {d : ℕ} {X : SmoothProperComplexVariety d}
    {L : LineBundle X.scheme} {B : ExternalSquareSections X L}
    (E : ExternalExpansion X L B)
    (hB : IsSymmetricExternalSection X.structureMap L B) : ExternalExpansion X L B where
  size := E.size
  left := E.right
  right := E.left
  equation := by
    let τ := chosenExternalExchange X.structureMap L
    let swap := ExchangeAlgebraProof.swapSectionAddHom τ.identification
    have hs : swap B = B := hB
    have he := congrArg swap E.equation
    rw [map_sum] at he
    calc
      B = swap B := hs.symm
      _ = ∑ i, swap (externalProductSection X.structureMap (E.left i) (E.right i)) := he
      _ = ∑ i, externalProductSection X.structureMap (E.right i) (E.left i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact τ.onProducts (E.left i) (E.right i)

/-- Apply arbitrary complex-linear coefficient operations to the canonical
tensor equality. In particular, exchange symmetry holds for iterated local
derivatives, with the order of those derivatives retained. -/
theorem operation_sum_exchange {d : ℕ} {X : SmoothProperComplexVariety d}
    {L : LineBundle X.scheme} {B : ExternalSquareSections X L}
    (E : ExternalExpansion X L B)
    (hB : IsSymmetricExternalSection X.structureMap L B)
    (H : AffineLineFrame L)
    (P Q : ComplexSections X.structureMap L.sheaf →ₗ[ℂ]
      Coefficients X.structureMap H.openSet) :
    (∑ i, P (sectionValue (E.left i)) * Q (sectionValue (E.right i))) =
      ∑ i, P (sectionValue (E.right i)) * Q (sectionValue (E.left i)) := by
  let R := TensorProduct.lift ((multiplyLinear X.structureMap H.openSet).compl₁₂ P Q)
  have h := congrArg R (E.tensor_independent (flippedExpansion E hB))
  change R (∑ i, TensorProduct.tmul ℂ
      (M := ComplexSections X.structureMap L.sheaf)
      (N := ComplexSections X.structureMap L.sheaf)
      (sectionValue (E.left i)) (sectionValue (E.right i))) =
    R (∑ i, TensorProduct.tmul ℂ
      (M := ComplexSections X.structureMap L.sheaf)
      (N := ComplexSections X.structureMap L.sheaf)
      (sectionValue (E.right i)) (sectionValue (E.left i))) at h
  rw [map_sum, map_sum] at h
  have hmul (a b : Coefficients X.structureMap H.openSet) :
      multiplyLinear X.structureMap H.openSet a b = a * b := rfl
  simpa only [R, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, hmul] using h

/-- One first-slot derivative and two ordered second-slot derivatives. -/
def mixedThird {d : ℕ} {X : SmoothProperComplexVariety d}
    {L : LineBundle X.scheme} {B : ExternalSquareSections X L}
    (E : ExternalExpansion X L B) (H : AffineLineFrame L)
    (u v w : SectionsOn (tangentSheaf X.structureMap) H.openSet) :
    RingSections X.scheme H.openSet :=
  ∑ i, tangentActs X.structureMap H.openSet u (H.localCoefficient (E.left i)) *
    tangentActs X.structureMap H.openSet v
      (tangentActs X.structureMap H.openSet w (H.localCoefficient (E.right i)))

theorem secondFirst_exchange {d : ℕ} {X : SmoothProperComplexVariety d}
    {L : LineBundle X.scheme} {B : ExternalSquareSections X L}
    (E : ExternalExpansion X L B)
    (hB : IsSymmetricExternalSection X.structureMap L B)
    (H : AffineLineFrame L)
    (u v w : SectionsOn (tangentSheaf X.structureMap) H.openSet) :
    (∑ i, tangentActs X.structureMap H.openSet u
        (tangentActs X.structureMap H.openSet v (H.localCoefficient (E.left i))) *
      tangentActs X.structureMap H.openSet w (H.localCoefficient (E.right i))) =
      mixedThird E H w u v := by
  have h := operation_sum_exchange E hB H
    ((derivativeLinear X.structureMap H.openSet u).comp
      ((derivativeLinear X.structureMap H.openSet v).comp
        (coefficientLinear X.structureMap L H)))
    ((derivativeLinear X.structureMap H.openSet w).comp
      (coefficientLinear X.structureMap L H))
  have hderivative (z : SectionsOn (tangentSheaf X.structureMap) H.openSet)
      (a : Coefficients X.structureMap H.openSet) :
      derivativeLinear X.structureMap H.openSet z a =
        tangentActs X.structureMap H.openSet z a := rfl
  simpa only [LinearMap.comp_apply, coefficientLinear_sectionValue, hderivative,
    mixedThird, mul_comm] using h

theorem derivative_mixedSecond {d : ℕ} {X : SmoothProperComplexVariety d}
    {L : LineBundle X.scheme} {B : ExternalSquareSections X L}
    (E : ExternalExpansion X L B)
    (hB : IsSymmetricExternalSection X.structureMap L B)
    (H : AffineLineFrame L)
    (u v w : SectionsOn (tangentSheaf X.structureMap) H.openSet) :
    tangentActs X.structureMap H.openSet u (E.mixedSecond H v w) =
      mixedThird E H w u v + mixedThird E H v u w := by
  have hdiff : tangentActs X.structureMap H.openSet u (E.mixedSecond H v w) =
      (∑ i, tangentActs X.structureMap H.openSet u
          (tangentActs X.structureMap H.openSet v (H.localCoefficient (E.left i))) *
        tangentActs X.structureMap H.openSet w (H.localCoefficient (E.right i))) +
      mixedThird E H v u w := by
    change (TangentActionProof.functionAddHom X.structureMap H.openSet u)
      (∑ i, tangentActs X.structureMap H.openSet v (H.localCoefficient (E.left i)) *
        tangentActs X.structureMap H.openSet w (H.localCoefficient (E.right i))) = _
    rw [map_sum]
    unfold mixedThird
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    change tangentActs X.structureMap H.openSet u
        (tangentActs X.structureMap H.openSet v (H.localCoefficient (E.left i)) *
          tangentActs X.structureMap H.openSet w (H.localCoefficient (E.right i))) = _
    rw [TangentActionProof.leibniz]
    ring
  rw [secondFirst_exchange E hB H u v w] at hdiff
  exact hdiff

theorem mixedThird_commutator {d : ℕ} {X : SmoothProperComplexVariety d}
    {L : LineBundle X.scheme} {B : ExternalSquareSections X L}
    (E : ExternalExpansion X L B) (H : AffineLineFrame L)
    (u v w : SectionsOn (tangentSheaf X.structureMap) H.openSet) :
    mixedThird E H u v w - mixedThird E H u w v =
      E.mixedSecond H u (tangentBracket X.structureMap H.openSet v w) := by
  simp only [mixedThird, ExternalExpansion.mixedSecond, tangentBracket_spec,
    mul_sub, Finset.sum_sub_distrib]

theorem mixedSecond_normalized {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    {C : IntrinsicContactStructure X} (K : NormalizedContactKernel X C)
    (E : ExternalExpansion X C.sequence.line K.twoPointSection)
    (H : AffineLineFrame C.sequence.line)
    (u v : SectionsOn (tangentSheaf X.structureMap) H.openSet) :
    E.mixedSecond H u v =
      -(2 * localContactValue C H u * localContactValue C H v) := by
  rw [E.mixedSecond_eq_neg_of_orderTwo K.orderTwo H u v,
    normalizedSymbol_on_any_expansion C K.normalized E H u v]

theorem mixedSecond_proportional {d : ℕ} {X : SmoothProperComplexVariety d}
    {L : LineBundle X.scheme} {B : ExternalSquareSections X L}
    (E : ExternalExpansion X L B) {x : ComplexPoint X} (F : PointFrame X L x)
    (u : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) (k : ℂ)
    (h : ∀ i, F.evaluation (tangentActs X.structureMap F.frame.openSet u
        (F.coefficient (E.left i))) = k * F.evaluation (F.coefficient (E.left i)))
    (w : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) :
    F.evaluation (E.mixedSecond F.frame u w) =
      k * F.evaluation (E.secondSlotFirst F.frame w) := by
  let ev : RingSections X.scheme F.frame.openSet →+* ℂ := F.evaluation.toRingHom
  have heval (i : Fin E.size) :
      ev (tangentActs X.structureMap F.frame.openSet u
          (F.frame.localCoefficient (E.left i))) =
        k * ev (F.frame.localCoefficient (E.left i)) := h i
  change ev (∑ i,
      tangentActs X.structureMap F.frame.openSet u (F.frame.localCoefficient (E.left i)) *
        tangentActs X.structureMap F.frame.openSet w (F.frame.localCoefficient (E.right i))) =
    k * ev (∑ i, F.frame.localCoefficient (E.left i) *
      tangentActs X.structureMap F.frame.openSet w (F.frame.localCoefficient (E.right i)))
  rw [map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul, map_mul, heval i]
  ring

theorem mixedThird_proportional {d : ℕ} {X : SmoothProperComplexVariety d}
    {L : LineBundle X.scheme} {B : ExternalSquareSections X L}
    (E : ExternalExpansion X L B) {x : ComplexPoint X} (F : PointFrame X L x)
    (u : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) (k : ℂ)
    (h : ∀ i, F.evaluation (tangentActs X.structureMap F.frame.openSet u
        (F.coefficient (E.left i))) = k * F.evaluation (F.coefficient (E.left i)))
    (v w : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) :
    F.evaluation (mixedThird E F.frame u v w) =
      k * F.evaluation (E.secondSlotSecond F.frame v w) := by
  let ev : RingSections X.scheme F.frame.openSet →+* ℂ := F.evaluation.toRingHom
  have heval (i : Fin E.size) :
      ev (tangentActs X.structureMap F.frame.openSet u
          (F.frame.localCoefficient (E.left i))) =
        k * ev (F.frame.localCoefficient (E.left i)) := h i
  change ev (∑ i,
      tangentActs X.structureMap F.frame.openSet u (F.frame.localCoefficient (E.left i)) *
        tangentActs X.structureMap F.frame.openSet v
          (tangentActs X.structureMap F.frame.openSet w (F.frame.localCoefficient (E.right i)))) =
    k * ev (∑ i, F.frame.localCoefficient (E.left i) *
      tangentActs X.structureMap F.frame.openSet v
        (tangentActs X.structureMap F.frame.openSet w (F.frame.localCoefficient (E.right i))))
  rw [map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul, map_mul, heval i]
  ring

/-- The symmetry-forced third-order identity in horizontal directions.
Both fields are horizontal on the entire frame. Differentiating the three
vanishing mixed Hessians and retaining the ordered-derivative commutators
forces their bracket to have zero contact value at the point. -/
theorem horizontal_bracket_value_zero {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    {C : IntrinsicContactStructure X} (K : NormalizedContactKernel X C)
    (E : ExternalExpansion X C.sequence.line K.twoPointSection)
    {x : ComplexPoint X} (F : PointFrame X C.sequence.line x)
    (u w r : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet)
    (hu : localContactValue C F.frame u = 0)
    (hw : localContactValue C F.frame w = 0)
    (hr : localContactValue C F.frame r = 1) (k : ℂ)
    (h : ∀ i, F.evaluation (tangentActs X.structureMap F.frame.openSet u
        (F.coefficient (E.left i))) = k * F.evaluation (F.coefficient (E.left i))) :
    F.evaluation (localContactValue C F.frame
      (tangentBracket X.structureMap F.frame.openSet u w)) = 0 := by
  let T (a b c : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) : ℂ :=
    F.evaluation (mixedThird E F.frame a b c)
  have hMu (a : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) :
      E.mixedSecond F.frame u a = 0 := by
    rw [mixedSecond_normalized K E F.frame u a]
    simp only [hu, mul_zero, zero_mul, neg_zero]
  have hMw (a : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) :
      E.mixedSecond F.frame w a = 0 := by
    rw [mixedSecond_normalized K E F.frame w a]
    simp only [hw, mul_zero, zero_mul, neg_zero]
  have hMrw : E.mixedSecond F.frame r w = 0 := by
    rw [mixedSecond_normalized K E F.frame r w]
    simp only [hw, mul_zero, neg_zero]
  have hTuw (a : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) :
      T u a w = 0 := by
    change F.evaluation (mixedThird E F.frame u a w) = 0
    rw [mixedThird_proportional E F u k h a w,
      normalizedSymbol_on_any_expansion C K.normalized E F.frame a w]
    simp only [hw, mul_zero, map_zero]
  have hTwu (a : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) :
      T u w a = 0 := by
    change F.evaluation (mixedThird E F.frame u w a) = 0
    rw [mixedThird_proportional E F u k h w a,
      normalizedSymbol_on_any_expansion C K.normalized E F.frame w a]
    simp only [hw, mul_zero, zero_mul, map_zero]
  have hexchange (a b c : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) :
      F.evaluation (tangentActs X.structureMap F.frame.openSet a
        (E.mixedSecond F.frame b c)) = T c a b + T b a c := by
    rw [derivative_mixedSecond E K.symmetric F.frame a b c, map_add] <;> rfl
  have hcomm (a b c : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) :
      T a b c - T a c b =
        F.evaluation (E.mixedSecond F.frame a
          (tangentBracket X.structureMap F.frame.openSet b c)) := by
    change F.evaluation (mixedThird E F.frame a b c) -
      F.evaluation (mixedThird E F.frame a c b) = _
    rw [← map_sub, mixedThird_commutator]
  have hA := hexchange r u w
  rw [hMu w, TangentActionProof.zero_function, map_zero, hTuw r, add_zero] at hA
  have hB := hexchange w u r
  rw [hMu r, TangentActionProof.zero_function, map_zero, hTwu r, add_zero] at hB
  have hC := hcomm w u r
  rw [hMw, map_zero] at hC
  have hD := hexchange u r w
  rw [hMrw, TangentActionProof.zero_function, map_zero] at hD
  have hE := hcomm r u w
  have hM : F.evaluation (E.mixedSecond F.frame r
      (tangentBracket X.structureMap F.frame.openSet u w)) = 0 := by
    linear_combination hA + hB - hC - hD - hE
  rw [mixedSecond_normalized K E F.frame r _, hr] at hM
  have hfinal : -(2 * F.evaluation (localContactValue C F.frame
      (tangentBracket X.structureMap F.frame.openSet u w))) = 0 := by
    let ev : RingSections X.scheme F.frame.openSet →+* ℂ := F.evaluation.toRingHom
    change -(2 * ev (localContactValue C F.frame
      (tangentBracket X.structureMap F.frame.openSet u w))) = 0
    have hMraw : ev (-(2 * 1 * localContactValue C F.frame
        (tangentBracket X.structureMap F.frame.openSet u w))) = 0 := hM
    simpa only [map_neg, map_mul, map_one, map_ofNat, mul_one] using hMraw
  linear_combination (-1 / 2 : ℂ) * hfinal

/-- A horizontal point derivation has an intrinsic representative that is
horizontal on the whole affine frame. The correction vanishes at the point. -/
theorem horizontal_representative {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) {x : ComplexPoint X}
    (F : PointFrame X C.sequence.line x) (A : ContactAtPoint C F)
    (v : F.Tangent) (hv : A.theta v = 0) :
    ∃ u : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet,
      F.evaluateVector u = v ∧ localContactValue C F.frame u = 0 := by
  obtain ⟨u, hu⟩ := F.evaluateVector_surjective v
  obtain ⟨r, hr⟩ := localContactValue_unit C F.frame
  have hvalue : F.evaluation (localContactValue C F.frame u) = 0 :=
    (A.theta_normalized u).symm.trans ((congrArg A.theta hu).trans hv)
  refine ⟨u - localContactValue C F.frame u • r, ?_, ?_⟩
  · rw [F.evaluateVector_sub, F.evaluateVector_smul, hvalue, zero_smul, sub_zero, hu]
  · rw [localContactValue_sub, localContactValue_smul, hr, mul_one, sub_self]

/-- Direct local injectivity from the actual second- and third-derivative
identities. This proof does not use first-jet generation or the immersion
conclusion: proportional first-factor coefficients force horizontality;
exchange symmetry forces Levi orthogonality; contact nondegeneracy finishes. -/
theorem proportional_coefficients_zero {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    {C : IntrinsicContactStructure X} (K : NormalizedContactKernel X C)
    (E : ExternalExpansion X C.sequence.line K.twoPointSection)
    {x : ComplexPoint X} (F : PointFrame X C.sequence.line x) (A : ContactAtPoint C F)
    (v : F.Tangent) (k : ℂ)
    (h : (coefficientJet E F).derivative v = k • (coefficientJet E F).value) :
    v = 0 ∧ k = 0 := by
  have hcoeff (u : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet)
      (hu : F.evaluateVector u = v) (i : Fin E.size) :
      F.evaluation (tangentActs X.structureMap F.frame.openSet u
        (F.coefficient (E.left i))) = k * F.evaluation (F.coefficient (E.left i)) := by
    have hi := congrFun h i
    change v.val (F.coefficient (E.left i)) =
      k * F.evaluation (F.coefficient (E.left i)) at hi
    exact (congrArg (fun D : F.Tangent => D.val (F.coefficient (E.left i))) hu).trans hi
  obtain ⟨u, hu⟩ := F.evaluateVector_surjective v
  obtain ⟨r, hr⟩ := localContactValue_unit C F.frame
  have hM := mixedSecond_proportional E F u k (hcoeff u hu) r
  rw [E.secondSlotFirst_zero_of_orderTwo K.orderTwo F.frame r, map_zero, mul_zero] at hM
  rw [mixedSecond_normalized K E F.frame u r, hr] at hM
  have hM' : -(2 * F.evaluation (localContactValue C F.frame u)) = 0 := by
    let ev : RingSections X.scheme F.frame.openSet →+* ℂ := F.evaluation.toRingHom
    change -(2 * ev (localContactValue C F.frame u)) = 0
    have hMraw : ev (-(2 * localContactValue C F.frame u * 1)) = 0 := hM
    simpa only [map_neg, map_mul, map_one, map_ofNat, mul_one] using hMraw
  have hvalue : F.evaluation (localContactValue C F.frame u) = 0 := by
    linear_combination (-1 / 2 : ℂ) * hM'
  have hθv : A.theta v = 0 :=
    (congrArg A.theta hu).symm.trans ((A.theta_normalized u).trans hvalue)
  obtain ⟨u₀, hu₀, hθu₀⟩ := horizontal_representative C F A v hθv
  have horth : ∀ w, A.theta w = 0 → A.exterior v w = 0 := by
    intro w hw
    obtain ⟨w₀, hw₀, hθw₀⟩ := horizontal_representative C F A w hw
    have hbr := horizontal_bracket_value_zero K E F u₀ w₀ r hθu₀ hθw₀ hr k
      (hcoeff u₀ hu₀)
    rw [← hu₀, ← hw₀, A.exterior_normalized]
    simp only [scalarExterior, hθu₀, hθw₀, TangentActionProof.zero_function,
      sub_self, zero_sub, map_neg, hbr, neg_zero]
  have hvzero := (contactAtPoint_nondegenerate C F A).2 v hθv horth
  have hks : k • (coefficientJet E F).value = 0 := by
    rw [← h, hvzero, map_zero]
  exact ⟨hvzero, (smul_eq_zero.mp hks).resolve_right (coefficient_value_nonzero K E F)⟩

theorem contactExterior_skew {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) {x : ComplexPoint X}
    (F : PointFrame X C.sequence.line x) (A : ContactAtPoint C F) (u v : F.Tangent) :
    A.exterior u v = -A.exterior v u := by
  obtain ⟨u, rfl⟩ := F.evaluateVector_surjective u
  obtain ⟨v, rfl⟩ := F.evaluateVector_surjective v
  rw [A.exterior_normalized, A.exterior_normalized]
  have hs : scalarExterior C F u v = -scalarExterior C F v u := by
    unfold scalarExterior
    rw [tangentBracket_skew, localContactValue_neg]
    ring
  rw [hs, map_neg]

/-- An alternating representative of the contact coefficient one-jet.
The exterior part is fixed by the genuine contact geometry; the symmetric
part is immaterial after the coefficient comparison has been proved. -/
def contactOneJet {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) {x : ComplexPoint X}
    (F : PointFrame X C.sequence.line x) (A : ContactAtPoint C F) : ContactOneJet F.Tangent where
  theta := A.theta
  nonzero := (contactAtPoint_nondegenerate C F A).1
  coefficientDerivative := (1 / 2 : ℂ) • A.exterior
  leviNondegenerate := by
    intro v hv h
    apply (contactAtPoint_nondegenerate C F A).2 v hv
    intro w hw
    have he := h w hw
    change (1 / 2 : ℂ) * A.exterior v w - (1 / 2 : ℂ) * A.exterior w v = 0 at he
    rw [contactExterior_skew C F A w v] at he
    linear_combination he

theorem contactOneJet_exterior {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) {x : ComplexPoint X}
    (F : PointFrame X C.sequence.line x) (A : ContactAtPoint C F) (u v : F.Tangent) :
    (contactOneJet C F A).exteriorValue u v = A.exterior u v := by
  change (1 / 2 : ℂ) * A.exterior u v - (1 / 2 : ℂ) * A.exterior v u = A.exterior u v
  rw [contactExterior_skew C F A v u]
  ring

end KernelTaylorProof

end KernelTaylorProofSection

/-- SOURCE jet:local-calculation then jet:kernel. Must be proved from
symmetry and the normalized symbol, not from the final jet-generation target. -/
theorem taylorRealization_exists {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    {C : IntrinsicContactStructure X} (K : NormalizedContactKernel X C)
    (E : ExternalExpansion X C.sequence.line K.twoPointSection)
    {x : ComplexPoint X} (F : PointFrame X C.sequence.line x) :
    Nonempty (TaylorRealization K E F) := by
  obtain ⟨A⟩ := contactAtPoint_exists C F
  refine ⟨{
    pointContact := A
    coefficientData := KernelTaylorProof.contactOneJet C F A
    theta_eq := rfl
    exterior_eq := KernelTaylorProof.contactOneJet_exterior C F A
    compareCoefficients := ?_ }⟩
  intro v k h
  obtain ⟨hv, hk⟩ := KernelTaylorProof.proportional_coefficients_zero K E F A v k h
  subst v
  subst k
  constructor
  · intro s
    simp [ContactOneJet.firstSlotLinear]
  · intro s
    simp [ContactOneJet.firstSlotQuadratic, ContactOneJet.exteriorValue, ContactOneJet.quadratic]

/-- Exact algebraic deduction; no contact-conic or classification theorem is used. -/
theorem TaylorRealization.immersive {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    {C : IntrinsicContactStructure X} {K : NormalizedContactKernel X C}
    {E : ExternalExpansion X C.sequence.line K.twoPointSection}
    {x : ComplexPoint X} {F : PointFrame X C.sequence.line x}
    (T : TaylorRealization K E F) (hnz : (coefficientJet E F).value ≠ 0) :
    (coefficientJet E F).IsProjectivelyImmersive := by
  refine ⟨hnz, ?_⟩
  intro v k h
  exact Core.LocalJet.projectiveKernelDirection_zero F.Tangent T.coefficientData v k
    (T.compareCoefficients v k h)

/-- Coefficient contractions generate all first jets once the three specific geometric comparisons have
been established. The dimension bound below is an OUTPUT, never a substitute for this surjectivity. -/
theorem contractions_surjective_of_immersive {d : ℕ} {X : SmoothProperComplexVariety d}
    {L : LineBundle X.scheme} {B : ExternalSquareSections X L}
    (E : ExternalExpansion X L B) {x : ComplexPoint X} (F : PointFrame X L x)
    (hi : (coefficientJet E F).IsProjectivelyImmersive)
    (hc : ∀ ell, F.jetCoordinates (jetRestrictionAt x L.sheaf 1 (contraction E ell)) =
      (coefficientJet E F).contractedJet ell) :
    Function.Surjective (fun ell => jetRestrictionAt x L.sheaf 1 (contraction E ell)) := by
  intro j
  obtain ⟨ell, he⟩ := immersiveKernel_separatesFirstJets F.Tangent (Fin E.size → ℂ)
    (coefficientJet E F) hi (F.jetCoordinates j)
  exact ⟨ell, F.jetCoordinates.injective ((hc ell).trans he)⟩



/-- Three smaller obligations replace the monolithic symmetric-jet input.
No constructor or instance supplying the entire package is admitted. -/
structure Inputs : Prop where
  nonzero : ∀ (n : ℕ) (X : SmoothProperComplexVariety (2*n+1))
    (C : IntrinsicContactStructure X) (K : NormalizedContactKernel X C)
    (E : ExternalExpansion X C.sequence.line K.twoPointSection)
    (x : ComplexPoint X) (F : PointFrame X C.sequence.line x),
      (coefficientJet E F).value ≠ 0
  taylor : ∀ (n : ℕ) (X : SmoothProperComplexVariety (2*n+1))
    (C : IntrinsicContactStructure X) (K : NormalizedContactKernel X C)
    (E : ExternalExpansion X C.sequence.line K.twoPointSection)
    (x : ComplexPoint X) (F : PointFrame X C.sequence.line x),
      Nonempty (TaylorRealization K E F)
  contractions : ∀ (d : ℕ) (X : SmoothProperComplexVariety d) (L : LineBundle X.scheme)
    (B : ExternalSquareSections X L) (E : ExternalExpansion X L B)
    (x : ComplexPoint X) (F : PointFrame X L x) (ell : (Fin E.size → ℂ) →ₗ[ℂ] ℂ),
      F.jetCoordinates (jetRestrictionAt x L.sheaf 1 (contraction E ell)) =
        (coefficientJet E F).contractedJet ell

/-- Preferred proof route for jet:criterion. Only local normalization/duality
foundations and the three supplied lemmas are used, not the old admitted criterion. -/
theorem Inputs.assemble (H : Inputs) : SymmetricJetCriterion := by
  intro n X C K x j
  obtain ⟨F⟩ := pointFrame_exists X C.sequence.line x
  obtain ⟨E⟩ := externalExpansion_exists X C.sequence.line K.twoPointSection
  obtain ⟨T⟩ := H.taylor n X C K E x F
  have hi := T.immersive (H.nonzero n X C K E x F)
  obtain ⟨ell, he⟩ := contractions_surjective_of_immersive E F hi
    (H.contractions (2*n+1) X C.sequence.line K.twoPointSection E x F) j
  exact ⟨contraction E ell, he⟩

/-! Frame covariance is triangular, NOT just multiplication by a scalar. -/
section FrameChange
variable (V S : Type*) [AddCommGroup V] [Module ℂ V]
  [AddCommGroup S] [Module ℂ S]

/-- If the local coefficient is multiplied by q, dw gains (dq)*w. -/
def changeFrame (J : SectionValuedFirstJet V S) (q : ℂ) (dq : V →ₗ[ℂ] ℂ) :
    SectionValuedFirstJet V S where
  value := q • J.value
  derivative := q • J.derivative + dq.smulRight J.value

theorem changeFrame_immersive_iff (J : SectionValuedFirstJet V S)
    (q : ℂ) (hq : q ≠ 0) (dq : V →ₗ[ℂ] ℂ) :
    (changeFrame V S J q dq).IsProjectivelyImmersive ↔ J.IsProjectivelyImmersive := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro hz
      apply h.1
      change q • J.value = 0
      rw [hz, smul_zero]
    · intro v k hv
      apply h.2 v (k + q⁻¹ * dq v)
      change q • J.derivative v + dq v • J.value =
        (k + q⁻¹ * dq v) • (q • J.value)
      rw [hv, smul_smul, smul_smul, ← add_smul]
      congr 1
      field_simp [hq] <;> ring
  · intro h
    refine ⟨smul_ne_zero hq h.1, ?_⟩
    intro v k hv
    apply h.2 v (k - q⁻¹ * dq v)
    have hv' := congrArg (fun z : S => q⁻¹ • z) hv
    change q⁻¹ • (q • J.derivative v + dq v • J.value) =
      q⁻¹ • (k • (q • J.value)) at hv'
    have hscalar : q⁻¹ * (k * q) = k := by field_simp [hq] <;> ring
    have heq : J.derivative v + (q⁻¹ * dq v) • J.value = k • J.value := by
      simpa only [smul_add, smul_smul, inv_mul_cancel₀ hq, one_smul, hscalar] using hv'
    rw [sub_smul]
    exact eq_sub_iff_add_eq.mpr heq


/-- Scalar first jets transform by (a,da) |-> (q*a, q*da+a*dq). -/
def changeScalarJet (q : ℂ) (dq : V →ₗ[ℂ] ℂ) (j : TrivializedFirstJet V) :
    TrivializedFirstJet V := (q*j.1, q • j.2 + j.1 • dq)

theorem changeScalarJet_bijective (q : ℂ) (hq : q ≠ 0) (dq : V →ₗ[ℂ] ℂ) :
    Function.Bijective (changeScalarJet V q dq) := by
  let g : TrivializedFirstJet V → TrivializedFirstJet V := fun j =>
    (q⁻¹ * j.1, q⁻¹ • (j.2 - (q⁻¹ * j.1) • dq))
  have hleft : Function.LeftInverse g (changeScalarJet V q dq) := by
    rintro ⟨a, da⟩
    apply Prod.ext
    · change q⁻¹ * (q * a) = a
      field_simp [hq]
    · apply LinearMap.ext
      intro v
      change q⁻¹ * (q * da v + a * dq v - (q⁻¹ * (q * a)) * dq v) = da v
      field_simp [hq] <;> ring
  have hright : Function.RightInverse g (changeScalarJet V q dq) := by
    rintro ⟨a, da⟩
    apply Prod.ext
    · change q * (q⁻¹ * a) = a
      field_simp [hq]
    · apply LinearMap.ext
      intro v
      change q * (q⁻¹ * (da v - (q⁻¹ * a) * dq v)) +
        (q⁻¹ * a) * dq v = da v
      field_simp [hq] <;> ring
  exact ⟨hleft.injective, hright.surjective⟩


theorem changeFrame_contractedJet (J : SectionValuedFirstJet V S)
    (q : ℂ) (dq : V →ₗ[ℂ] ℂ) (ell : S →ₗ[ℂ] ℂ) :
    (changeFrame V S J q dq).contractedJet ell =
      changeScalarJet V q dq (J.contractedJet ell) := by
  apply Prod.ext
  · simp only [changeFrame, changeScalarJet, SectionValuedFirstJet.contractedJet,
      map_smul, smul_eq_mul]
  · apply LinearMap.ext
    intro v
    simp only [changeFrame, changeScalarJet, SectionValuedFirstJet.contractedJet,
      LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, map_add, map_smul, smul_eq_mul]
    ring


/-- Multiplying a frame by zero is excluded: it is not a line trivialization. -/
theorem changeFrame_zero_not_immersive (J : SectionValuedFirstJet V S)
    (dq : V →ₗ[ℂ] ℂ) : ¬ (changeFrame V S J 0 dq).IsProjectivelyImmersive := by
  intro h
  exact h.1 (by simp [changeFrame])
end FrameChange

/-- Dependency inventory of this refinement, not a list of proved results. -/
def proofOrder : List String :=
  [ "pointFrame_exists; evaluation; tangent_finite; tangent_dimension",
    "restrictLocal_surjective; jetCoordinates_existsUnique (ALL local functions)",
    "scaleSection_local; functional_coordinate_sum; contraction_firstJet",
    "contactAtPoint_exists; contactAtPoint_nondegenerate",
    "coefficient_value_nonzero; symmetry-forced cubic; taylorRealization_exists",
    "TaylorRealization.immersive; contractions_surjective_of_immersive; Inputs.assemble" ]

end Jets


/-! ## 5. Refined assembly: the original theorem is still the final output -/

/-- Same proof route as Skeleton.AlgebraicInputs, replacing two large slots by four moving-pair, three
ordered-symbol, and three symmetric-jet obligations. The jets field is finer than the old symmetricJets
field; symmetricJets remains a derived accessor. Use Jets.Inputs, not an admitted global criterion. -/
structure AlgebraicInputs (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) : Prop where
  nonprimitive : NonprimitiveBranch
  smoothing : PrimitiveSmoothing P p
  movingPair : MovingPairInputs P p
  diagonal : DiagonalInputs P p
  jets : Jets.Inputs
  Hamiltonians : HamiltonianEvaluation
  integration : AlgebraicIntegration
  classification : HomogeneousClassification

/-- Compatibility accessor; the criterion is now derived from three smaller inputs. -/
def AlgebraicInputs.symmetricJets (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (H : AlgebraicInputs P p) : SymmetricJetCriterion := Jets.Inputs.assemble H.jets

def AlgebraicInputs.toSkeleton (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (H : AlgebraicInputs P p) : Skeleton.AlgebraicInputs P p where
  nonprimitive := H.nonprimitive
  smoothing := H.smoothing
  movingPairAndDescent := MovingPairInputs.assemble P p H.movingPair
  familyToDiagonal := DiagonalInputs.assemble P p H.diagonal
  symmetricJets := Jets.Inputs.assemble H.jets
  Hamiltonians := H.Hamiltonians
  integration := H.integration
  classification := H.classification

universe uR
structure ProjectInputs (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) : Prop where
  algebraic : AlgebraicInputs P p
  riemannian : Skeleton.RiemannianInputs.{uR}

def ProjectInputs.toSkeleton (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (H : ProjectInputs.{uR} P p) : Skeleton.ProjectInputs.{uR} P p where
  algebraic := AlgebraicInputs.toSkeleton P p H.algebraic
  riemannian := H.riemannian

theorem project_contactFanoClassification (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (H : AlgebraicInputs P p) : ContactFanoClassification :=
  Skeleton.project_contactFanoClassification P p (AlgebraicInputs.toSkeleton P p H)

theorem project_parallelCurvature (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (H : ProjectInputs.{uR} P p) {n : ℕ} (M : ClosedPositiveQK.{uR} n) :
    IsLocallyRiemannianSymmetric n M.space.carrier :=
  Skeleton.project_parallelCurvature P p (ProjectInputs.toSkeleton P p H) M

/-- Refined preferred root: same hypotheses on M, and no use of the
admitted original conjecture, *_target shortcuts, or admitted constructors
of the input packages. Foundational definitions may still use sorryAx. -/
theorem leBrunSalamon_project (n : ℕ) (M : Type uR)
    [EMetricSpace M] [ChartedSpace (Model n) M] [IsManifold (model n) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
    [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
      (fun x : M => TangentSpace (model n) x)]
    [IsRiemannianManifold (model n) M] [Nonempty M] [CompactSpace M] [ConnectedSpace M]
    (H : ProjectInputs.{uR} canonicalProjectiveLine canonicalMarkedPoint)
    (hn : 2 ≤ n) (hQK : IsPositiveQuaternionicKahler n M) :
    IsLocallyRiemannianSymmetric n M :=
  Skeleton.leBrunSalamon_project n M
    (ProjectInputs.toSkeleton canonicalProjectiveLine canonicalMarkedPoint H) hn hQK

end LeBrunSalamon.Refinement

/-! The original global first-jet declarations are scheduled here, after
the actual point-frame and third-derivative proofs they require. Their
qualified names and statements are unchanged. -/
namespace LeBrunSalamon.Core

open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTen LeBrunSalamon.PhaseFourteen
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Refinement.Jets

namespace NormalizedContactKernel

variable {n : ℕ} {X : SmoothProperComplexVariety (2 * n + 1)}
  {C : IntrinsicContactStructure X}

/-- Source: jet:criterion. The global first-jet theorem follows from the
actual coefficient contractions and the symmetry-forced third-order identity. -/
theorem separatesFirstJets (K : NormalizedContactKernel X C) :
    SeparatesFirstJets X C.sequence.line := by
  intro x j
  obtain ⟨F⟩ := pointFrame_exists X C.sequence.line x
  obtain ⟨E⟩ := externalExpansion_exists X C.sequence.line K.twoPointSection
  obtain ⟨T⟩ := taylorRealization_exists K E F
  have hi := T.immersive (coefficient_value_nonzero K E F)
  obtain ⟨ell, he⟩ := contractions_surjective_of_immersive E F hi
    (contraction_firstJet E F) j
  exact ⟨contraction E ell, he⟩


end NormalizedContactKernel

/-- This is a genuine term-level assembly, with NO new sorry and NO use of the older unconditional
contact-Fano jet-generation target. Its geometric proof obligations are exactly the three explicit inputs
and the symmetric-jet criterion on a normalized kernel. -/
theorem manuscriptCore_firstJets (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (H : ManuscriptCoreInputs P p)
    {n : ℕ} (X : ContactFanoManifold n) :
    SeparatesFirstJets X.variety X.contact.sequence.line := by
  classical
  by_cases hp : HasPrimitiveContactPicard X.contact
  · obtain ⟨g⟩ := H.smoothing n X hp
    obtain ⟨K⟩ := H.kernelConstruction n X hp g
    exact K.separatesFirstJets
  · exact H.nonprimitive n X hp


end LeBrunSalamon.Core

/-!
# Construction layer: manuscript-sized proof obligations

This layer EXPANDS the skeleton rather than declaring more versions of the final
conjecture. There are three separately usable parts:
* actual point derivations and square-zero test algebras;
* the suitable-pair / relative-Hom / smoothing argument of smoothing.tex;
* the finite-image / split-sheet / purity argument of descent.tex.

Objects are constrained by maps, equations, or universal properties. Theorems
marked `by sorry` are obligations, including classical comparison theorems.
No instance or admitted existence theorem supplies an entire input package.
The source snapshot and Lean/mathlib versions remain those recorded in Project.
This layer is included in the recorded Stage 2 build; its admitted obligations remain open.
-/
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

/-! ## Scalar restriction and canonical fibres -/

/-- A composition comparison, with the equality of the actual morphisms fixed.
The sheaf isomorphism cannot be replaced by an arbitrary fibre identification. -/
def compositionPullback {T Y Z : Scheme} (f : T ⟶ Y) (g : Y ⟶ Z)
    (h : T ⟶ Z) (e : f ≫ g = h) (E : OModule Z) :
    pullbackModule f (pullbackModule g E) ≅ pullbackModule h E :=
  (Scheme.Modules.pullbackComp f g).app E ≪≫
    eqToIso (congrArg (fun k : T ⟶ Z => pullbackModule k E) e)

set_option backward.isDefEq.respectTransparency false in
theorem pullbackComp_homEquiv {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    {E : OModule Z} {M : OModule X}
    (h : pullbackModule f (pullbackModule g E) ⟶ M) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _
      ((Scheme.Modules.pullbackComp f g).inv.app E ≫ h) =
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ h) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app M := by
  let adj := (Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  let adj' := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  have hu := unit_conjugateEquiv adj adj' (Scheme.Modules.pullbackComp f g).inv E
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at hu
  change adj'.homEquiv _ _ ((Scheme.Modules.pullbackComp f g).inv.app E ≫ h) =
    adj.homEquiv _ _ h ≫ (Scheme.Modules.pushforwardComp f g).hom.app M
  rw [adj'.homEquiv_apply, adj.homEquiv_apply, Functor.map_comp,
    ← Category.assoc, ← hu, Category.assoc]
  simpa only [Category.assoc, pullbackModule, Functor.comp_obj, Functor.id_obj] using
    congrArg (fun k => adj.unit.app E ≫ k)
    ((Scheme.Modules.pushforwardComp f g).hom.naturality h).symm

set_option backward.isDefEq.respectTransparency false in
theorem structurePushforwardMap_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    structurePushforwardMap g ≫
      (Scheme.Modules.pushforward g).map (structurePushforwardMap f) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app (structureModule X) =
      structurePushforwardMap (f ≫ g) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem unitPullbackMap_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullbackComp f g).inv.app (structureModule Z) ≫
      (Scheme.Modules.pullback f).map (unitPullbackMap g) ≫ unitPullbackMap f =
        unitPullbackMap (f ≫ g) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [pullbackComp_homEquiv,
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_left,
    unitPullbackMap_adjoint,
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_naturality_right,
    unitPullbackMap_adjoint, unitPullbackMap_adjoint]
  exact structurePushforwardMap_comp f g

set_option backward.isDefEq.respectTransparency false in
theorem unitPullbackMap_comp_hom {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullbackComp f g).hom.app (structureModule Z) ≫
      unitPullbackMap (f ≫ g) =
        (Scheme.Modules.pullback f).map (unitPullbackMap g) ≫ unitPullbackMap f := by
  rw [← unitPullbackMap_comp f g]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem unitPullbackIso_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (unitPullbackIso f).inv ≫ (Scheme.Modules.pullback f).map (unitPullbackIso g).inv ≫
      (Scheme.Modules.pullbackComp f g).hom.app (structureModule Z) =
        (unitPullbackIso (f ≫ g)).inv := by
  apply (cancel_mono (unitPullbackIso (f ≫ g)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id]
  change (unitPullbackIso f).inv ≫ (Scheme.Modules.pullback f).map (unitPullbackIso g).inv ≫
    (Scheme.Modules.pullbackComp f g).hom.app (structureModule Z) ≫
      unitPullbackMap (f ≫ g) = 𝟙 _
  rw [unitPullbackMap_comp_hom]
  change (unitPullbackIso f).inv ≫ (Scheme.Modules.pullback f).map (unitPullbackIso g).inv ≫
    (Scheme.Modules.pullback f).map (unitPullbackIso g).hom ≫ (unitPullbackIso f).hom = 𝟙 _
  simp [← Functor.map_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem pullSection_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    {E : OModule Z} (s : AlgebraicSection E) :
    pullSection f (pullSection g s) ≫ (Scheme.Modules.pullbackComp f g).hom.app E =
      pullSection (f ≫ g) s := by
  have hn := (Scheme.Modules.pullbackComp f g).hom.naturality s
  change (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map s) ≫
      (Scheme.Modules.pullbackComp f g).hom.app E =
    (Scheme.Modules.pullbackComp f g).hom.app (structureModule Z) ≫
      (Scheme.Modules.pullback (f ≫ g)).map s at hn
  simp only [pullSection, restrictSection, Functor.map_comp, Category.assoc]
  rw [hn]
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ (Scheme.Modules.pullback (f ≫ g)).map s) (unitPullbackIso_comp f g)

set_option backward.isDefEq.respectTransparency false in
theorem compositionPullback_sections {T Y Z : Scheme}
    (f : T ⟶ Y) (g : Y ⟶ Z) (h : T ⟶ Z) (e : f ≫ g = h)
    {E : OModule Z} (s : AlgebraicSection E) :
    pullSection f (pullSection g s) ≫ (compositionPullback f g h e E).hom =
      pullSection h s := by
  subst h
  simpa [compositionPullback] using pullSection_comp f g s

/-- Global sections with the C-structure induced by the specified base map. -/
def CSections {X : Scheme} (sX : X ⟶ ComplexBase) (E : OModule X) : Type _ :=
  GlobalSections E

instance cSectionsAddCommGroup {X : Scheme} (sX : X ⟶ ComplexBase) (E : OModule X) :
    AddCommGroup (CSections sX E) := inferInstanceAs (AddCommGroup (GlobalSections E))

set_option backward.isDefEq.respectTransparency false in
/-- The underlying function is the actual pullback of complex constants. -/
def complexConstants {X : Scheme} (sX : X ⟶ ComplexBase) :
    ℂ →+* RingSections X ⊤ where
  toFun := complexConstant sX ⊤
  map_zero' := by simp [complexConstant]
  map_one' := by simp [complexConstant]
  map_add' := by intro a b; simp [complexConstant]
  map_mul' := by intro a b; simp [complexConstant]

set_option backward.isDefEq.respectTransparency false in
theorem complexConstants_apply_top {X : Scheme} (sX : X ⟶ ComplexBase) (c : ℂ) :
    complexConstants sX c = sX.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) := by
  simp [complexConstants, complexConstant]

set_option backward.isDefEq.respectTransparency false in
theorem complexConstants_naturality {X Y : Scheme} (f : X ⟶ Y)
    (sX : X ⟶ ComplexBase) (sY : Y ⟶ ComplexBase) (h : f ≫ sY = sX) (c : ℂ) :
    f.appTop (complexConstants sY c) = complexConstants sX c := by
  rw [complexConstants_apply_top, complexConstants_apply_top]
  change (sY.appTop ≫ f.appTop) ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) = _
  rw [← Scheme.Hom.comp_appTop, h]

instance cSectionsModule {X : Scheme} (sX : X ⟶ ComplexBase) (E : OModule X) :
    Module ℂ (CSections sX E) :=
  Module.compHom (GlobalSections E) (complexConstants sX)

set_option backward.isDefEq.respectTransparency false in
/-- C-linear map on genuine global sections induced by an O-linear map. -/
def onCSections {X : Scheme} (sX : X ⟶ ComplexBase)
    {E F : OModule X} (f : E ⟶ F) : CSections sX E →ₗ[ℂ] CSections sX F where
  toFun a := f.app ⊤ a
  map_add' := by intro a b; exact map_add (f.app ⊤).hom a b
  map_smul' := by
    intro c a
    exact Scheme.Modules.Hom.app_smul f (complexConstants sX c) a

set_option backward.isDefEq.respectTransparency false in
theorem onCSections_bijective_of_iso {X : Scheme} (sX : X ⟶ ComplexBase)
    {E F : OModule X} (e : E ≅ F) : Function.Bijective (onCSections sX e.hom) := by
  let : IsIso (e.hom.app ⊤) :=
    (Scheme.Modules.Hom.isIso_iff_isIso_app (φ := e.hom)).mp inferInstance ⊤
  exact ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)

abbrev Fiber {X : Scheme} (E : OModule X) (x : ComplexBase ⟶ X) :=
  CSections (𝟙 ComplexBase) (pullbackModule x E)

set_option backward.isDefEq.respectTransparency false in
def pullCSectionsAlong {Y Z : Scheme} (f : Y ⟶ Z)
    (sY : Y ⟶ ComplexBase) (sZ : Z ⟶ ComplexBase) (hf : f ≫ sZ = sY)
    (E : OModule Z) : CSections sZ E →ₗ[ℂ] CSections sY (pullbackModule f E) where
  toFun a := sectionValue (pullSection f (sectionFromValue a))
  map_add' := by
    intro a b
    simp only [pullSection_value, sectionFromValue_spec]
    exact map_add (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E).app ⊤).hom a b
  map_smul' := by
    intro c a
    have h := pullSectionValue_smul f E (complexConstants sZ c) a
    rw [complexConstants_naturality f sY sZ hf] at h
    exact h

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of a section, not a choice of a vector in a marked vector space. -/
def evaluateSection {X : Scheme} (sX : X ⟶ ComplexBase)
    (E : OModule X) (x : ComplexBase ⟶ X) (hx : x ≫ sX = 𝟙 ComplexBase) :
    CSections sX E →ₗ[ℂ] Fiber E x :=
  pullCSectionsAlong x (𝟙 ComplexBase) sX hx E

def fiberMap {X : Scheme} {E F : OModule X} (f : E ⟶ F)
    (x : ComplexBase ⟶ X) : Fiber E x →ₗ[ℂ] Fiber F x :=
  onCSections (𝟙 ComplexBase) ((Scheme.Modules.pullback x).map f)

def fiberComposition {T Y : Scheme} (f : T ⟶ Y) (x : ComplexBase ⟶ T)
    (y : ComplexBase ⟶ Y) (e : x ≫ f = y) (E : OModule Y) :
    Fiber (pullbackModule f E) x →ₗ[ℂ] Fiber E y :=
  onCSections (𝟙 ComplexBase) (compositionPullback x f y e E).hom

set_option backward.isDefEq.respectTransparency false in
theorem fiberComposition_bijective {T Y : Scheme} (f : T ⟶ Y)
    (x : ComplexBase ⟶ T) (y : ComplexBase ⟶ Y) (e : x ≫ f = y) (E : OModule Y) :
    Function.Bijective (fiberComposition f x y e E) :=
  onCSections_bijective_of_iso (𝟙 ComplexBase) (compositionPullback x f y e E)

noncomputable section FiberRankConstruction
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
open Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight

namespace FiberRankProof

/-- Evaluation of a finite free sheaf is a finite free module. -/
def finiteFreeSectionsEquiv
    {C : Type} [Category.{0} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat) [HasSheafify J AddCommGrpCat]
    [J.WEqualsLocallyBijective AddCommGrpCat]
    (U : Cᵒᵖ) (r : ℕ) :
    (SheafOfModules.free (R := R) (Fin r)).val.obj U ≃ₗ[R.obj.obj U]
      (Fin r → R.obj.obj U) := by
  let F := SheafOfModules.evaluation R U
  let family := fun _ : Fin r => SheafOfModules.unit R
  letI : HasBiproduct family := HasBiproduct.of_hasProduct family
  let e := F.mapIso (biproductIso family).symm ≪≫
    asIso (piComparison F family) ≪≫ ModuleCat.piIsoPi (fun i => F.obj (family i))
  exact e.toLinearEquiv

/-- The actual complex scalar action is transported through ΓSpecIso, not
through a chosen abstract field isomorphism. -/
def complexSectionsEquiv (G : OModule ComplexBase) {r : ℕ}
    (e : GlobalSections G ≃ₗ[RingSections ComplexBase ⊤]
      (Fin r → RingSections ComplexBase ⊤)) :
    CSections (𝟙 ComplexBase) G ≃ₗ[ℂ] (Fin r → ℂ) := by
  let γ := Scheme.ΓSpecIso (CommRingCat.of ℂ)
  let f : CSections (𝟙 ComplexBase) G →ₗ[ℂ] (Fin r → ℂ) :=
    { toFun := fun v i => γ.hom (e v i)
      map_add' := by
        intro v w
        ext i
        simp only [map_add, Pi.add_apply]
      map_smul' := by
        intro c v
        ext i
        change γ.hom (e (complexConstants (𝟙 ComplexBase) c •
          (show GlobalSections G from v)) i) =
          c * γ.hom (e v i)
        rw [e.map_smul]
        change γ.hom (complexConstants (𝟙 ComplexBase) c * e v i) = _
        rw [map_mul, complexConstants_apply_top]
        change γ.hom (γ.inv c) * γ.hom (e v i) = _
        simp }
  apply LinearEquiv.ofBijective f
  constructor
  · intro v w h
    apply e.injective
    ext i
    apply (ConcreteCategory.bijective_of_isIso γ.hom).injective
    exact congrFun h i
  · intro v
    obtain ⟨w, hw⟩ := e.surjective (fun i => γ.inv (v i))
    refine ⟨w, ?_⟩
    ext i
    change γ.hom (e w i) = v i
    rw [hw]
    simp

/-- Pulling an actual local frame through the point's factorization gives a
global free frame on Spec ℂ. This avoids any admitted pullback-rank theorem. -/
theorem fiber_freeIso {X : Scheme} {r : ℕ}
    (E : AlgebraicVectorBundle X r) (x : ComplexBase ⟶ X) :
    Nonempty (SheafOfModules.free (R := ComplexBase.ringCatSheaf) (Fin r) ≅
      pullbackModule x E.sheaf) := by
  obtain ⟨q, hq, hr⟩ := E.locallyFree
  letI := hq
  obtain ⟨i, hi⟩ :=
    ((_root_.Opens.coversTop_iff X q.X).mp q.coversTop).exists_mem
      (x (IsLocalRing.closedPoint ℂ))
  let U : X.Opens := q.X i
  have hxU : Set.range x ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change x z ∈ U
    rw [Subsingleton.elim z (IsLocalRing.closedPoint ℂ)]
    exact hi
  let g := IsOpenImmersion.lift U.ι x hxU
  have hg : g ≫ U.ι = x := IsOpenImmersion.lift_fac U.ι x hxU
  let F := Scheme.Modules.pullback g
  letI : F.IsLeftAdjoint :=
    (SheafOfModules.pullbackPushforwardAdjunction g.toRingCatSheafHom).isLeftAdjoint
  let freePullback := SheafOfModules.mapFreeIso F (Fin r) (unitPullbackIso g).symm
  let e := DominantSectionInjectivityProof.localFreePullbackIso q hr i
  let comp : pullbackModule g (pullbackModule U.ι E.sheaf) ≅
      pullbackModule x E.sheaf :=
    (Scheme.Modules.pullbackComp g U.ι).app E.sheaf ≪≫
      (Scheme.Modules.pullbackCongr hg).app E.sheaf
  exact ⟨freePullback ≪≫ F.mapIso e ≪≫ comp⟩

/-- Explicit finite-dimensional model for the original fiber definition. -/
theorem fiber_linearEquiv {X : Scheme} {r : ℕ}
    (E : AlgebraicVectorBundle X r) (x : ComplexBase ⟶ X) :
    Nonempty (Fiber E.sheaf x ≃ₗ[ℂ] (Fin r → ℂ)) := by
  obtain ⟨e⟩ := fiber_freeIso E x
  let eΓ : GlobalSections (SheafOfModules.free (R := ComplexBase.ringCatSheaf) (Fin r))
      ≃ₗ[RingSections ComplexBase ⊤] GlobalSections (pullbackModule x E.sheaf) :=
    ((SheafOfModules.evaluation ComplexBase.ringCatSheaf (op ⊤)).mapIso e).toLinearEquiv
  let eFree := finiteFreeSectionsEquiv ComplexBase.ringCatSheaf (op ⊤) r
  exact ⟨complexSectionsEquiv (pullbackModule x E.sheaf) (eΓ.symm.trans eFree)⟩

/-- Both former fiber-rank claims follow from the same actual equivalence. -/
theorem fiber_rank_and_finite {X : Scheme} {r : ℕ}
    (E : AlgebraicVectorBundle X r) (x : ComplexBase ⟶ X) :
    Module.finrank ℂ (Fiber E.sheaf x) = r ∧
      FiniteDimensional ℂ (Fiber E.sheaf x) := by
  obtain ⟨e⟩ := fiber_linearEquiv E x
  refine ⟨?_, ?_⟩
  · simpa using e.finrank_eq
  · exact Module.Finite.of_injective e.toLinearMap e.injective

end FiberRankProof

end FiberRankConstruction

/-- The actual complex fibre is identified with Fin r → ℂ through a local
free frame and the canonical ΓSpecIso. The historical declaration name is
retained for compatibility; no fibre-rank result is assumed in this proof. -/
theorem _root_.LeBrunSalamon.PublishedInputs.BaseChangeFibers.fiber_rank_and_finite
    {X : Scheme} {r : ℕ} (E : AlgebraicVectorBundle X r)
    (x : ComplexBase ⟶ X) :
    Module.finrank ℂ (Fiber E.sheaf x) = r ∧
      FiniteDimensional ℂ (Fiber E.sheaf x) := by
  exact FiberRankProof.fiber_rank_and_finite E x

/-- Project API wrapper for fiber dimension. -/
theorem fiber_dimension {X : Scheme} {r : ℕ} (E : AlgebraicVectorBundle X r)
    (x : ComplexBase ⟶ X) : Module.finrank ℂ (Fiber E.sheaf x) = r :=
  (LeBrunSalamon.PublishedInputs.BaseChangeFibers.fiber_rank_and_finite E x).1

/-- Project API wrapper for finite-dimensionality of a vector-bundle fiber. -/
theorem fiber_finite {X : Scheme} {r : ℕ} (E : AlgebraicVectorBundle X r)
    (x : ComplexBase ⟶ X) : FiniteDimensional ℂ (Fiber E.sheaf x) :=
  (LeBrunSalamon.PublishedInputs.BaseChangeFibers.fiber_rank_and_finite E x).2

/- The actual pullback/global-section exactness translation. The generic
EGA local splitting boundary lives in LSVectorBundlePullback. -/
section FiberExactConstruction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiberExactProof

/-- The existing actual frame on the field-valued point proves the
quasi-coherence required for the affine section-surjectivity theorem. -/
theorem fiber_quasicoherent {X : Scheme.{0}} {r : ℕ}
    (E : AlgebraicVectorBundle X r) (x : ComplexBase ⟶ X) :
    (pullbackModule x E.sheaf).IsQuasicoherent := by
  obtain ⟨e⟩ := FiberRankProof.fiber_freeIso E x
  exact LocalExtensionSplitting.quasicoherent_of_locallyFreeRank
    (locallyFreeOfRank_iso e (freeSheaf_rank ComplexBase r))

/-- Injectivity, surjectivity and image/kernel equality for the actual
fiber maps. No abstract replacement vector spaces or chosen linear maps
are substituted for the project's canonical pullback/global-section maps. -/
theorem vectorBundle_fiber_exact {X : Scheme.{0}} {a b c : ℕ}
    (E : AlgebraicVectorBundle X a) (F : AlgebraicVectorBundle X b)
    (G : AlgebraicVectorBundle X c) (i : E.sheaf ⟶ F.sheaf) (q : F.sheaf ⟶ G.sheaf)
    (h0 : i ≫ q = 0) (h : (ShortComplex.mk i q h0).ShortExact)
    (x : ComplexBase ⟶ X) :
    Function.Injective (fiberMap i x) ∧ Function.Surjective (fiberMap q x) ∧
      LinearMap.range (fiberMap i x) = LinearMap.ker (fiberMap q x) := by
  let H := Scheme.Modules.pullback x
  have hex := LeBrunSalamon.VectorBundlePullback.vectorBundle_pullback_shortExact x E F G i q h0 h
  letI : Mono (H.map i) := hex.mono_f
  letI : Epi (H.map q) := hex.epi_g
  letI : (pullbackModule x F.sheaf).IsQuasicoherent := fiber_quasicoherent F x
  letI : (pullbackModule x G.sheaf).IsQuasicoherent := fiber_quasicoherent G x
  have hz : H.map i ≫ H.map q = 0 := by rw [← H.map_comp, h0, H.map_zero]
  refine ⟨ExtensionGluing.sectionMap_injective (H.map i) ⊤,
    LocalExtensionSplitting.spec_sectionMap_surjective (H.map q), ?_⟩
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    change (H.map q).app ⊤ ((H.map i).app ⊤ w) = 0
    have he := congrArg (fun f => f.app ⊤ w) hz
    exact he
  · intro hv
    change (H.map q).app ⊤ v = 0 at hv
    obtain ⟨w, hw, _⟩ :=
      ExtensionGluing.existsUnique_kernelSection (H.map i) (H.map q) hz hex ⊤ v hv
    exact ⟨w, hw⟩

end FiberExactProof
end FiberExactConstruction

/-- The original fiber maps are exact by the proved pullback theorem,
affine section surjectivity, and left exactness on sections. The historical
public declaration name is preserved; no fiber-exactness result is admitted. -/
theorem _root_.LeBrunSalamon.PublishedInputs.BaseChangeFibers.vectorBundle_fiber_exact
    {X : Scheme} {a b c : ℕ}
    (E : AlgebraicVectorBundle X a) (F : AlgebraicVectorBundle X b)
    (G : AlgebraicVectorBundle X c) (i : E.sheaf ⟶ F.sheaf) (q : F.sheaf ⟶ G.sheaf)
    (h0 : i ≫ q = 0) (h : (ShortComplex.mk i q h0).ShortExact)
    (x : ComplexBase ⟶ X) :
    Function.Injective (fiberMap i x) ∧ Function.Surjective (fiberMap q x) ∧
      LinearMap.range (fiberMap i x) = LinearMap.ker (fiberMap q x) := by
  exact FiberExactProof.vectorBundle_fiber_exact E F G i q h0 h x

/-- Project API wrapper for exactness on complex fibers. -/
theorem vectorBundle_fiber_exact {X : Scheme} {a b c : ℕ}
    (E : AlgebraicVectorBundle X a) (F : AlgebraicVectorBundle X b)
    (G : AlgebraicVectorBundle X c) (i : E.sheaf ⟶ F.sheaf) (q : F.sheaf ⟶ G.sheaf)
    (h0 : i ≫ q = 0) (h : (ShortComplex.mk i q h0).ShortExact)
    (x : ComplexBase ⟶ X) :
    Function.Injective (fiberMap i x) ∧ Function.Surjective (fiberMap q x) ∧
      LinearMap.range (fiberMap i x) = LinearMap.ker (fiberMap q x) :=
  LeBrunSalamon.PublishedInputs.BaseChangeFibers.vectorBundle_fiber_exact
    E F G i q h0 h x

/-! ## Point derivations and explicit dual-number tests -/
namespace Infinitesimal

section Algebra
variable (A : Type*) [CommRing A] [Algebra ℂ A]

/-- This is a submodule, not a subtype missing its vector-space structure. -/
def tangentSpace (p : A →ₐ[ℂ] ℂ) : Submodule ℂ (A →ₗ[ℂ] ℂ) where
  carrier := {D : A →ₗ[ℂ] ℂ | ∀ a b, D (a*b) = p a * D b + p b * D a}
  zero_mem' := by intro a b; simp
  add_mem' := by
    intro D E hD hE a b
    simp only [LinearMap.add_apply, hD a b, hE a b]
    ring
  smul_mem' := by
    intro c D hD a b
    simp only [LinearMap.smul_apply, smul_eq_mul, hD a b]
    ring

abbrev Tangent (p : A →ₐ[ℂ] ℂ) := ↥(tangentSpace A p)

def evaluateFunction (p : A →ₐ[ℂ] ℂ) (a : A) : Tangent A p →ₗ[ℂ] ℂ where
  toFun D := D.val a
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem tangent_kills_one (p : A →ₐ[ℂ] ℂ) (D : Tangent A p) : D.val 1 = 0 := by
  have h := D.property 1 1
  simp only [one_mul, map_one] at h
  linear_combination -h

theorem tangent_kills_constants (p : A →ₐ[ℂ] ℂ) (D : Tangent A p) (c : ℂ) :
    D.val (algebraMap ℂ A c) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, tangent_kills_one, smul_zero]

theorem tangent_kills_maximalSquare (p : A →ₐ[ℂ] ℂ) (D : Tangent A p)
    (a : A) (ha : a ∈ (RingHom.ker p.toRingHom)^2) : D.val a = 0 := by
  rw [pow_two] at ha
  exact Submodule.mul_induction_on ha
    (fun x hx y hy => by
      change p x = 0 at hx
      change p y = 0 at hy
      rw [D.property x y, hx, hy]
      simp)
    (fun x y hx hy => by simp [map_add, hx, hy])

end Algebra

/-- Push tangent vectors forward by precomposing with the map on functions. -/
def tangentMap {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] (f : A →ₐ[ℂ] B) (p : B →ₐ[ℂ] ℂ) :
    Tangent B p →ₗ[ℂ] Tangent A (p.comp f) where
  toFun D := ⟨D.val.comp f.toLinearMap, by
    intro a b
    simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      map_mul, AlgHom.comp_apply] using D.property (f a) (f b)⟩
  map_add' := by intro D E; apply Subtype.ext; ext a; rfl
  map_smul' := by intro c D; apply Subtype.ext; ext a; rfl

theorem tangentMap_apply {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] (f : A →ₐ[ℂ] B) (p : B →ₐ[ℂ] ℂ)
    (D : Tangent B p) (a : A) : (tangentMap f p D).val a = D.val (f a) := rfl

/-- The actual ring C[epsilon]/(epsilon^2). -/
def dualIdeal : Ideal (Polynomial ℂ) := Ideal.span {Polynomial.X^2}
abbrev Dual := Polynomial ℂ ⧸ dualIdeal

def epsilon : Dual := Ideal.Quotient.mk dualIdeal Polynomial.X

def residue : Dual →ₐ[ℂ] ℂ where
  toRingHom := Ideal.Quotient.lift dualIdeal (Polynomial.evalRingHom 0) (by
    intro f hf
    have hker : dualIdeal ≤ RingHom.ker (Polynomial.evalRingHom (0 : ℂ)) := by
      rw [dualIdeal, Ideal.span_singleton_le_iff_mem]
      simp
    exact hker hf)
  commutes' := by intro c; change Polynomial.eval 0 (Polynomial.C c) = c; simp

theorem epsilon_square : epsilon^2 = 0 := by
  rw [epsilon, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

theorem epsilon_ne_zero : epsilon ≠ 0 := by
  intro h
  have hm : (Polynomial.X : Polynomial ℂ) ∈ dualIdeal :=
    Ideal.Quotient.eq_zero_iff_mem.mp h
  have hd : (Polynomial.X : Polynomial ℂ)^2 ∣ Polynomial.X :=
    Ideal.mem_span_singleton.mp hm
  have hc := Polynomial.X_pow_dvd_iff.mp hd 1 (by decide)
  simpa using hc

/-- The coefficients are uniquely normalized by 1 and epsilon. -/
theorem dual_normalForm (z : Dual) :
    ∃! ab : ℂ × ℂ, z = algebraMap ℂ Dual ab.1 + epsilon * algebraMap ℂ Dual ab.2 := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨(f.coeff 0, f.coeff 1), ?_, ?_⟩
  · change Ideal.Quotient.mk dualIdeal f = Ideal.Quotient.mk dualIdeal
      (Polynomial.C (f.coeff 0) + Polynomial.X * Polynomial.C (f.coeff 1))
    rw [Ideal.Quotient.eq]
    apply Ideal.mem_span_singleton.mpr
    apply Polynomial.X_pow_dvd_iff.mpr
    intro d hd
    interval_cases d <;> simp
  · rintro ⟨a, b⟩ h
    change Ideal.Quotient.mk dualIdeal f = Ideal.Quotient.mk dualIdeal
      (Polynomial.C a + Polynomial.X * Polynomial.C b) at h
    have hd : Polynomial.X^2 ∣ f - (Polynomial.C a + Polynomial.X * Polynomial.C b) :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
    have h0 := Polynomial.X_pow_dvd_iff.mp hd 0 (by decide)
    have h1 := Polynomial.X_pow_dvd_iff.mp hd 1 (by decide)
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_zero,
      Polynomial.coeff_X_mul_zero, add_zero] at h0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C,
      Polynomial.coeff_X_mul, if_false, Nat.one_ne_zero, if_true, add_zero, zero_add] at h1
    apply Prod.ext
    · exact (sub_eq_zero.mp h0).symm
    · exact (sub_eq_zero.mp h1).symm

def linearCoefficient (z : Dual) : ℂ := (Classical.choose (dual_normalForm z)).2

theorem residue_normalForm (a b : ℂ) :
    residue (algebraMap ℂ Dual a + epsilon * algebraMap ℂ Dual b) = a := by
  have he : residue epsilon = 0 := by
    change Polynomial.eval 0 Polynomial.X = (0 : ℂ)
    simp
  simp [he]

theorem linearCoefficient_normalForm (a b : ℂ) :
    linearCoefficient (algebraMap ℂ Dual a + epsilon * algebraMap ℂ Dual b) = b := by
  have h := (Classical.choose_spec (dual_normalForm
    (algebraMap ℂ Dual a + epsilon * algebraMap ℂ Dual b))).2 (a, b) rfl
  exact (congrArg Prod.snd h).symm

/-- Formula for the infinitesimal point corresponding to a derivation. -/
def tangentToDual {A : Type*} [CommRing A] [Algebra ℂ A]
    (p : A →ₐ[ℂ] ℂ) (D : Tangent A p) : A →ₐ[ℂ] Dual where
  toFun a := algebraMap ℂ Dual (p a) + epsilon * algebraMap ℂ Dual (D.val a)
  map_zero' := by simp
  map_one' := by simp [tangent_kills_one]
  map_add' := by intro a b; simp [map_add, mul_add]; ring
  map_mul' := by
    intro a b
    have hD : D.val (a * b) = p a * D.val b + p b * D.val a := D.property a b
    simp only [hD, map_mul, map_add]
    ring_nf
    simp [epsilon_square]
  commutes' := by intro c; simp [tangent_kills_constants]

theorem tangentToDual_residue {A : Type*} [CommRing A] [Algebra ℂ A]
    (p : A →ₐ[ℂ] ℂ) (D : Tangent A p) : residue.comp (tangentToDual p D) = p := by
  ext a
  exact residue_normalForm (p a) (D.val a)

/-- All dual-number lifts, not just a chosen family, are detected. -/
theorem dual_normalForm_reconstruct (z : Dual) :
    z = algebraMap ℂ Dual (residue z) + epsilon * algebraMap ℂ Dual (linearCoefficient z) := by
  obtain ⟨⟨a, b⟩, rfl, _⟩ := dual_normalForm z
  rw [residue_normalForm, linearCoefficient_normalForm]

theorem linearCoefficient_algebraMap (a : ℂ) :
    linearCoefficient (algebraMap ℂ Dual a) = 0 := by
  simpa using linearCoefficient_normalForm a 0

theorem linearCoefficient_add (z w : Dual) :
    linearCoefficient (z + w) = linearCoefficient z + linearCoefficient w := by
  obtain ⟨⟨a, b⟩, rfl, _⟩ := dual_normalForm z
  obtain ⟨⟨d, e⟩, rfl, _⟩ := dual_normalForm w
  have hsum :
      (algebraMap ℂ Dual a + epsilon * algebraMap ℂ Dual b) +
      (algebraMap ℂ Dual d + epsilon * algebraMap ℂ Dual e) =
      algebraMap ℂ Dual (a + d) + epsilon * algebraMap ℂ Dual (b + e) := by
    simp only [map_add]; ring
  rw [hsum]
  simp only [linearCoefficient_normalForm]

theorem linearCoefficient_mul (z w : Dual) :
    linearCoefficient (z * w) = residue z * linearCoefficient w +
      residue w * linearCoefficient z := by
  obtain ⟨⟨a, b⟩, rfl, _⟩ := dual_normalForm z
  obtain ⟨⟨d, e⟩, rfl, _⟩ := dual_normalForm w
  have hprod :
      (algebraMap ℂ Dual a + epsilon * algebraMap ℂ Dual b) *
      (algebraMap ℂ Dual d + epsilon * algebraMap ℂ Dual e) =
      algebraMap ℂ Dual (a * d) + epsilon * algebraMap ℂ Dual (a * e + b * d) := by
    simp only [map_add, map_mul]
    ring_nf
    simp [epsilon_square]
  rw [hprod]
  simp only [linearCoefficient_normalForm, residue_normalForm]
  ring

theorem linearCoefficient_smul (c : ℂ) (z : Dual) :
    linearCoefficient (c • z) = c • linearCoefficient z := by
  rw [Algebra.smul_def c z, linearCoefficient_mul, linearCoefficient_algebraMap]
  simp

/-- All dual-number lifts, not just a chosen family, are detected. -/
theorem tangentToDual_bijective {A : Type*} [CommRing A] [Algebra ℂ A]
    (p : A →ₐ[ℂ] ℂ) :
    Function.Bijective (fun D : Tangent A p =>
      (⟨tangentToDual p D, tangentToDual_residue p D⟩ :
        {f : A →ₐ[ℂ] Dual // residue.comp f = p})) := by
  constructor
  · intro D E h
    apply Subtype.ext
    ext a
    have he := congrArg (fun f : {f : A →ₐ[ℂ] Dual // residue.comp f = p} =>
      linearCoefficient (f.val a)) h
    change linearCoefficient (algebraMap ℂ Dual (p a) + epsilon * algebraMap ℂ Dual (D.val a)) =
      linearCoefficient (algebraMap ℂ Dual (p a) + epsilon * algebraMap ℂ Dual (E.val a)) at he
    simpa only [linearCoefficient_normalForm] using he
  · intro f
    have hres (a : A) : residue (f.val a) = p a :=
      congrArg (fun g : A →ₐ[ℂ] ℂ => g a) f.property
    let d : A →ₗ[ℂ] ℂ :=
      { toFun := fun a => linearCoefficient (f.val a)
        map_add' := by intro a b; rw [map_add, linearCoefficient_add]
        map_smul' := by intro c a; simp only [map_smul, linearCoefficient_smul, RingHom.id_apply] }
    let D : Tangent A p := ⟨d, by
      intro a b
      change linearCoefficient (f.val (a * b)) =
        p a * linearCoefficient (f.val b) + p b * linearCoefficient (f.val a)
      rw [map_mul, linearCoefficient_mul, hres a, hres b]⟩
    refine ⟨D, ?_⟩
    apply Subtype.ext
    ext a
    change algebraMap ℂ Dual (p a) +
      epsilon * algebraMap ℂ Dual (linearCoefficient (f.val a)) = f.val a
    rw [← hres a]
    exact (dual_normalForm_reconstruct (f.val a)).symm

theorem tangentToDual_natural {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] (f : A →ₐ[ℂ] B) (p : B →ₐ[ℂ] ℂ)
    (D : Tangent B p) : tangentToDual (p.comp f) (tangentMap f p D) =
      (tangentToDual p D).comp f := by
  ext a
  rfl

/-- Rescaling the infinitesimal parameter, not rescaling an arbitrary label. -/
def scaleDual (c : ℂ) : Dual →ₐ[ℂ] Dual where
  toFun z := algebraMap ℂ Dual (residue z) +
    epsilon * algebraMap ℂ Dual (c * linearCoefficient z)
  map_zero' := by
    have hl : linearCoefficient (0 : Dual) = 0 := by
      simpa using linearCoefficient_normalForm 0 0
    simp [hl]
  map_one' := by
    have hl : linearCoefficient (1 : Dual) = 0 := by
      simpa using linearCoefficient_normalForm 1 0
    simp [hl]
  map_add' := by
    intro z w
    obtain ⟨⟨a, b⟩, rfl, _⟩ := dual_normalForm z
    obtain ⟨⟨d, e⟩, rfl, _⟩ := dual_normalForm w
    have hsum :
        (algebraMap ℂ Dual a + epsilon * algebraMap ℂ Dual b) +
        (algebraMap ℂ Dual d + epsilon * algebraMap ℂ Dual e) =
        algebraMap ℂ Dual (a + d) + epsilon * algebraMap ℂ Dual (b + e) := by
      simp only [map_add]; ring
    rw [hsum]
    simp only [residue_normalForm, linearCoefficient_normalForm]
    simp only [map_add, mul_add]
    ring
  map_mul' := by
    intro z w
    obtain ⟨⟨a, b⟩, rfl, _⟩ := dual_normalForm z
    obtain ⟨⟨d, e⟩, rfl, _⟩ := dual_normalForm w
    have hprod :
        (algebraMap ℂ Dual a + epsilon * algebraMap ℂ Dual b) *
        (algebraMap ℂ Dual d + epsilon * algebraMap ℂ Dual e) =
        algebraMap ℂ Dual (a * d) + epsilon * algebraMap ℂ Dual (a * e + b * d) := by
      simp only [map_add, map_mul]
      ring_nf
      simp [epsilon_square]
    rw [hprod]
    simp only [residue_normalForm, linearCoefficient_normalForm]
    simp only [map_add, map_mul]
    ring_nf
    simp [epsilon_square]
  commutes' := by
    intro a
    have hl : linearCoefficient (algebraMap ℂ Dual a) = 0 := by
      simpa using linearCoefficient_normalForm a 0
    simp [hl]

theorem tangentToDual_smul {A : Type*} [CommRing A] [Algebra ℂ A]
    (p : A →ₐ[ℂ] ℂ) (c : ℂ) (D : Tangent A p) :
    tangentToDual p (c • D) = (scaleDual c).comp (tangentToDual p D) := by
  ext a
  change algebraMap ℂ Dual (p a) + epsilon * algebraMap ℂ Dual (c * D.val a) =
    algebraMap ℂ Dual (residue (algebraMap ℂ Dual (p a) + epsilon * algebraMap ℂ Dual (D.val a))) +
    epsilon * algebraMap ℂ Dual
      (c * linearCoefficient (algebraMap ℂ Dual (p a) + epsilon * algebraMap ℂ Dual (D.val a)))
  rw [residue_normalForm, linearCoefficient_normalForm]

abbrev DualScheme : Scheme := Spec (CommRingCat.of Dual)
def dualToC : DualScheme ⟶ ComplexBase :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ Dual))
def origin : ComplexBase ⟶ DualScheme :=
  Spec.map (CommRingCat.ofHom residue.toRingHom)

theorem origin_overC : origin ≫ dualToC = 𝟙 ComplexBase := by
  unfold origin dualToC
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap ℂ Dual) ≫
      CommRingCat.ofHom residue.toRingHom = 𝟙 (CommRingCat.of ℂ) := by
    ext c
    exact residue.commutes c
  rw [h, Spec.map_id]


/-- A genuine infinitesimal deformation of a scheme point. -/
structure PointLift (X : Scheme) (sX : X ⟶ ComplexBase)
    (x : PointsOver ComplexBase (𝟙 ComplexBase) X sX) where
  map : DualScheme ⟶ X
  overC : map ≫ sX = dualToC
  reduces : origin ≫ map = x.val

/-- A zero-order point is not a tangent vector until its first-order lift
has been specified. Nilpotent test schemes are indispensable here. -/
def constantLift {X : Scheme} {sX : X ⟶ ComplexBase}
    (x : PointsOver ComplexBase (𝟙 ComplexBase) X sX) : PointLift X sX x where
  map := dualToC ≫ x.val
  overC := by simp [Category.assoc, x.property]
  reduces := by simp [← Category.assoc, origin_overC]

end Infinitesimal

/-! ## Pointed affine charts of deformation spaces -/
namespace Charts

structure PointedAffine where
  scheme : Scheme
  affine : IsAffine scheme
  toC : scheme ⟶ ComplexBase
  point : PointsOver ComplexBase (𝟙 ComplexBase) scheme toC

attribute [instance] PointedAffine.affine

namespace PointedAffine
variable (A : PointedAffine)

def Ring : Type _ := RingSections A.scheme ⊤
instance ringCommRing : CommRing A.Ring :=
  inferInstanceAs (CommRing (RingSections A.scheme ⊤))
instance ringAlgebra : Algebra ℂ A.Ring := (complexConstants A.toC).toAlgebra

set_option backward.isDefEq.respectTransparency false in
def evaluation : A.Ring →ₐ[ℂ] ℂ where
  toRingHom := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp A.point.val.appTop.hom
  commutes' := by
    intro c
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (A.point.val.appTop (complexConstants A.toC c)) = c
    rw [complexConstants_naturality A.point.val (𝟙 ComplexBase) A.toC A.point.property]
    rw [complexConstants_apply_top]
    simp

abbrev Tangent := Infinitesimal.Tangent A.Ring A.evaluation

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coordinate-free use of an affine chart: tangent vectors correspond to
ALL lifts of its centre to Spec(C[epsilon]/epsilon^2). -/
theorem tangentLiftEquiv_exists :
    ∃ e : A.Tangent ≃ Infinitesimal.PointLift A.scheme A.toC A.point,
      ∀ D a, (e D).map.appTop a =
        (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
          (Infinitesimal.tangentToDual A.evaluation D a) := by
  classical
  have hiso : A.scheme.isoSpec.inv.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of A.Ring)).inv := by
    have hh : A.scheme.isoSpec.hom.appTop =
        (Scheme.ΓSpecIso (CommRingCat.of A.Ring)).hom := by
      change A.scheme.toSpecΓ.appTop = _
      exact Scheme.toSpecΓ_appTop A.scheme
    apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of A.Ring)).hom).mp
    calc
      A.scheme.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A.Ring)).hom =
          A.scheme.isoSpec.inv.appTop ≫ A.scheme.isoSpec.hom.appTop := by rw [hh]
      _ = (A.scheme.isoSpec.hom ≫ A.scheme.isoSpec.inv).appTop := by
        rw [Scheme.Hom.comp_appTop]
      _ = 𝟙 _ := by rw [A.scheme.isoSpec.hom_inv_id]; rfl
      _ = (Scheme.ΓSpecIso (CommRingCat.of A.Ring)).inv ≫
          (Scheme.ΓSpecIso (CommRingCat.of A.Ring)).hom :=
        (Scheme.ΓSpecIso (CommRingCat.of A.Ring)).inv_hom_id.symm
  let mkMap (φ : A.Ring →ₐ[ℂ] Infinitesimal.Dual) :
      Infinitesimal.DualScheme ⟶ A.scheme :=
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ A.scheme.isoSpec.inv
  have hmap (φ : A.Ring →ₐ[ℂ] Infinitesimal.Dual) :
      (mkMap φ).appTop = CommRingCat.ofHom φ.toRingHom ≫
        (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv := by
    dsimp only [mkMap]
    rw [Scheme.Hom.comp_appTop, hiso]
    exact (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ.toRingHom)).symm
  have hmapValue (φ : A.Ring →ₐ[ℂ] Infinitesimal.Dual) (a : A.Ring) :
      (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom ((mkMap φ).appTop a) =
        φ a := by
    rw [hmap]
    exact (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).commRingCatIsoToRingEquiv.apply_symm_apply _
  have hscalar (z : RingSections ComplexBase ⊤) :
      (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom
        (Infinitesimal.dualToC.appTop z) =
      algebraMap ℂ Infinitesimal.Dual ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom z) := by
    exact congrArg (fun q : Γ(ComplexBase, ⊤) ⟶ CommRingCat.of Infinitesimal.Dual => q z)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap ℂ Infinitesimal.Dual)))
  have hresidue (z : RingSections Infinitesimal.DualScheme ⊤) :
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (Infinitesimal.origin.appTop z) =
      Infinitesimal.residue
        ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom z) := by
    exact congrArg (fun q : Γ(Infinitesimal.DualScheme, ⊤) ⟶ CommRingCat.of ℂ => q z)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom Infinitesimal.residue.toRingHom))
  let lift (D : A.Tangent) : Infinitesimal.PointLift A.scheme A.toC A.point :=
    { map := mkMap (Infinitesimal.tangentToDual A.evaluation D)
      overC := by
        apply ext_of_isAffine
        ext z
        apply (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).commRingCatIsoToRingEquiv.injective
        change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom
            ((mkMap (Infinitesimal.tangentToDual A.evaluation D)).appTop (A.toC.appTop z)) =
          (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom
            (Infinitesimal.dualToC.appTop z)
        rw [hmapValue, hscalar]
        have hz : A.toC.appTop z = algebraMap ℂ A.Ring
            ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom z) := by
          change A.toC.appTop z = complexConstants A.toC
            ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom z)
          rw [complexConstants_apply_top]
          exact congrArg (fun w => A.toC.appTop w)
            ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.symm_apply_apply z).symm
        rw [hz]
        exact (Infinitesimal.tangentToDual A.evaluation D).commutes _
      reduces := by
        apply ext_of_isAffine
        ext a
        apply (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.injective
        change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
            (Infinitesimal.origin.appTop
              ((mkMap (Infinitesimal.tangentToDual A.evaluation D)).appTop a)) =
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (A.point.val.appTop a)
        rw [hresidue, hmapValue]
        exact congrArg (fun φ : A.Ring →ₐ[ℂ] ℂ => φ a)
          (Infinitesimal.tangentToDual_residue A.evaluation D) }
  let functions (L : Infinitesimal.PointLift A.scheme A.toC A.point) :
      A.Ring →ₐ[ℂ] Infinitesimal.Dual :=
    { toRingHom := (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom.hom.comp
        L.map.appTop.hom
      commutes' := by
        intro c
        change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom
            (L.map.appTop (complexConstants A.toC c)) = algebraMap ℂ Infinitesimal.Dual c
        rw [complexConstants_naturality L.map Infinitesimal.dualToC A.toC L.overC,
          complexConstants_apply_top, hscalar]
        congr 1
        exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.apply_symm_apply c }
  have hfunctions (L : Infinitesimal.PointLift A.scheme A.toC A.point) :
      Infinitesimal.residue.comp (functions L) = A.evaluation := by
    ext a
    change Infinitesimal.residue
        ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom (L.map.appTop a)) =
      A.evaluation a
    rw [← hresidue]
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((Infinitesimal.origin ≫ L.map).appTop a) = _
    rw [L.reduces]
    rfl
  have hext (L M : Infinitesimal.PointLift A.scheme A.toC A.point)
      (h : L.map = M.map) : L = M := by
    cases L
    cases M
    cases h
    rfl
  have hbij : Function.Bijective lift := by
    constructor
    · intro D E h
      apply Subtype.ext
      apply LinearMap.ext
      intro a
      have hm := congrArg
        (fun L : Infinitesimal.PointLift A.scheme A.toC A.point =>
          (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom (L.map.appTop a)) h
      change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom
          ((mkMap (Infinitesimal.tangentToDual A.evaluation D)).appTop a) =
        (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom
          ((mkMap (Infinitesimal.tangentToDual A.evaluation E)).appTop a) at hm
      rw [hmapValue, hmapValue] at hm
      have hc := congrArg Infinitesimal.linearCoefficient hm
      change Infinitesimal.linearCoefficient
          (algebraMap ℂ Infinitesimal.Dual (A.evaluation a) +
            Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual (D.val a)) =
        Infinitesimal.linearCoefficient
          (algebraMap ℂ Infinitesimal.Dual (A.evaluation a) +
            Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual (E.val a)) at hc
      simpa only [Infinitesimal.linearCoefficient_normalForm] using hc
    · intro L
      obtain ⟨D, hD⟩ := (Infinitesimal.tangentToDual_bijective A.evaluation).2
        ⟨functions L, hfunctions L⟩
      refine ⟨D, hext (lift D) L ?_⟩
      apply ext_of_isAffine
      ext a
      apply (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).commRingCatIsoToRingEquiv.injective
      change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom
          ((mkMap (Infinitesimal.tangentToDual A.evaluation D)).appTop a) =
        (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom (L.map.appTop a)
      rw [hmapValue]
      exact congrArg (fun φ : {φ : A.Ring →ₐ[ℂ] Infinitesimal.Dual //
        Infinitesimal.residue.comp φ = A.evaluation} => φ.val a) hD
  refine ⟨Equiv.ofBijective lift hbij, ?_⟩
  intro D a
  change (mkMap (Infinitesimal.tangentToDual A.evaluation D)).appTop a = _
  exact congrArg (fun q : Γ(A.scheme, ⊤) ⟶ Γ(Infinitesimal.DualScheme, ⊤) => q a)
    (hmap (Infinitesimal.tangentToDual A.evaluation D))


def tangentLiftEquiv : A.Tangent ≃ Infinitesimal.PointLift A.scheme A.toC A.point :=
  Classical.choose A.tangentLiftEquiv_exists

theorem tangentLiftEquiv_normalized (D : A.Tangent) (a : A.Ring) :
    (A.tangentLiftEquiv D).map.appTop a =
      (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
        (Infinitesimal.tangentToDual A.evaluation D a) :=
  Classical.choose_spec A.tangentLiftEquiv_exists D a

end PointedAffine

structure Hom (A B : PointedAffine) where
  map : A.scheme ⟶ B.scheme
  overC : map ≫ B.toC = A.toC
  atCentre : A.point.val ≫ map = B.point.val

set_option backward.isDefEq.respectTransparency false in
def Hom.onFunctions {A B : Charts.PointedAffine} (f : Charts.Hom A B) :
    B.Ring →ₐ[ℂ] A.Ring where
  toRingHom := f.map.appTop.hom
  commutes' := by
    intro c
    exact complexConstants_naturality f.map A.toC B.toC f.overC c

set_option backward.isDefEq.respectTransparency false in
theorem Hom.evaluation_onFunctions {A B : Charts.PointedAffine} (f : Charts.Hom A B)
    (a : B.Ring) : A.evaluation (f.onFunctions a) = B.evaluation a := by
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    (A.point.val.appTop (f.map.appTop a)) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (B.point.val.appTop a)
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    ((f.map.appTop ≫ A.point.val.appTop) a) = _
  rw [← Scheme.Hom.comp_appTop, f.atCentre]

set_option backward.isDefEq.respectTransparency false in
def Hom.differential {A B : Charts.PointedAffine} (f : Charts.Hom A B) :
    A.Tangent →ₗ[ℂ] B.Tangent where
  toFun D := ⟨D.val.comp f.onFunctions.toLinearMap, by
    intro a b
    change D.val (f.onFunctions (a*b)) = B.evaluation a * D.val (f.onFunctions b) +
      B.evaluation b * D.val (f.onFunctions a)
    rw [map_mul, D.property, Hom.evaluation_onFunctions, Hom.evaluation_onFunctions]⟩
  map_add' := by intro D E; apply Subtype.ext; ext a; rfl
  map_smul' := by intro c D; apply Subtype.ext; ext a; rfl

theorem Hom.differential_apply {A B : PointedAffine} (f : Hom A B)
    (D : A.Tangent) (a : B.Ring) : (f.differential D).val a = D.val (f.onFunctions a) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem Hom.differential_zero_iff_constantLift {A B : PointedAffine} (f : Hom A B)
    (D : A.Tangent) : f.differential D = 0 ↔
      (A.tangentLiftEquiv D).map ≫ f.map = Infinitesimal.dualToC ≫ B.point.val := by
  have hleft (a : B.Ring) :
      (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom
        (((A.tangentLiftEquiv D).map ≫ f.map).appTop a) =
      algebraMap ℂ Infinitesimal.Dual (B.evaluation a) +
        Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual
          (D.val (f.onFunctions a)) := by
    change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom
        ((A.tangentLiftEquiv D).map.appTop (f.onFunctions a)) = _
    calc
      _ = Infinitesimal.tangentToDual A.evaluation D (f.onFunctions a) := by
        rw [A.tangentLiftEquiv_normalized]
        exact (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).commRingCatIsoToRingEquiv.apply_symm_apply _
      _ = _ := by
        change algebraMap ℂ Infinitesimal.Dual (A.evaluation (f.onFunctions a)) +
          Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual
            (D.val (f.onFunctions a)) = _
        rw [f.evaluation_onFunctions]
  have hright (a : B.Ring) :
      (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom
        ((Infinitesimal.dualToC ≫ B.point.val).appTop a) =
      algebraMap ℂ Infinitesimal.Dual (B.evaluation a) := by
    exact congrArg (fun q : Γ(ComplexBase, ⊤) ⟶ CommRingCat.of Infinitesimal.Dual =>
      q (B.point.val.appTop a))
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap ℂ Infinitesimal.Dual)))
  constructor
  · intro h
    apply ext_of_isAffine
    ext a
    apply (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).commRingCatIsoToRingEquiv.injective
    change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom
        (((A.tangentLiftEquiv D).map ≫ f.map).appTop a) =
      (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom
        ((Infinitesimal.dualToC ≫ B.point.val).appTop a)
    rw [hleft, hright]
    have hd : D.val (f.onFunctions a) = 0 :=
      congrArg (fun z : B.Tangent => z.val a) h
    rw [hd, map_zero, mul_zero, add_zero]
  · intro h
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    have hc := congrArg (fun g : Infinitesimal.DualScheme ⟶ B.scheme =>
      (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).hom (g.appTop a)) h
    rw [hleft, hright] at hc
    have hd := congrArg Infinitesimal.linearCoefficient hc
    rw [Infinitesimal.linearCoefficient_normalForm,
      Infinitesimal.linearCoefficient_algebraMap] at hd
    exact hd


/-- Smoothness at the centre, represented by an actual source neighborhood. -/
def SmoothAtCentre {A B : PointedAffine} (f : Hom A B) : Prop :=
  ∃ U : A.scheme.Opens, (Set.range A.point.val ⊆ U) ∧ Smooth (U.ι ≫ f.map)

theorem smooth_differential_surjective {A B : PointedAffine} (f : Hom A B)
    (hf : SmoothAtCentre f) : Function.Surjective f.differential := by sorry

/-- Converse needs BOTH schemes smooth over C; it is not asserted for
arbitrary singular sources from surjectivity of Zariski tangent maps alone. -/
theorem differential_surjective_implies_smooth {A B : PointedAffine} (f : Hom A B)
    (hA : Smooth A.toC) (hB : Smooth B.toC)
    (hd : Function.Surjective f.differential) : SmoothAtCentre f := by sorry

theorem tangent_finite_of_lfp (A : PointedAffine)
    (hA : LocallyOfFinitePresentation A.toC) : FiniteDimensional ℂ A.Tangent := by
  letI : LocallyOfFinitePresentation A.toC := hA
  letI : Algebra.FiniteType ℂ A.Ring := by
    apply RingHom.finiteType_algebraMap.mp
    exact Refinement.Jets.PointFrame.PointDerivationFiniteProof.constantsOn_finiteType
      A.toC ⊤ (isAffineOpen_top A.scheme)
  exact Refinement.Jets.PointFrame.PointDerivationFiniteProof.pointDerivations_finite
    A.evaluation (Infinitesimal.tangentSpace A.Ring A.evaluation) (fun D => D.property)


theorem tangent_dimension_of_smooth (A : PointedAffine) (d : ℕ)
    (hA : SmoothOfRelativeDimension d A.toC) :
    Module.finrank ℂ A.Tangent = d := by sorry

end Charts

/-! ## Contact-line geometry with actual evaluation subspaces -/
/- SOURCE-ONLY generated-fibre evaluation bridge; UNCOMPILED. -/
namespace GeneratedFiberEvaluation

open Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance {Y : Scheme} (x : ComplexBase ⟶ Y) :
    PreservesColimitsOfSize.{0, 0}
      (show SheafOfModules.{0} Y.ringCatSheaf ⥤
        SheafOfModules.{0} ComplexBase.ringCatSheaf from Scheme.Modules.pullback x) :=
  (SheafOfModules.pullbackPushforwardAdjunction x.toRingCatSheafHom).leftAdjoint_preservesColimits

/-- Sections of a sheaf of modules over the empty open are zero. -/
private theorem empty_section_eq_zero (M : OModule ComplexBase)
    (a : M.val.obj (op (⊥ : ComplexBase.Opens))) : a = 0 := by
  let F : TopCat.Sheaf AddCommGrpCat ComplexBase := ⟨M.presheaf, M.isSheaf⟩
  have h := (TopCat.Sheaf.isTerminalOfEmpty F).hom_ext (𝟙 _) 0
  have ha := congrArg
    (fun f : F.obj.obj (op ⊥) ⟶ F.obj.obj (op ⊥) => f a) h
  simpa using ha

/-- The span of an actual family of compatible sections is a subsheaf on
Spec C.  Locality uses the one-point topology, including the empty open. -/
private def generatorSpan (M : OModule ComplexBase)
    (σ : SheafOfModules.GeneratingSections M) : M.Submodule where
  obj U := Submodule.span (ComplexBase.ringCatSheaf.obj.obj U)
    (Set.range (fun i : σ.I => (show M.val.obj U from (σ.s i).val U)))
  map := by
    intro U V f a ha
    change M.val.map f a ∈ Submodule.span
      (ComplexBase.ringCatSheaf.obj.obj V)
      (Set.range (fun i : σ.I => (show M.val.obj V from (σ.s i).val V)))
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      rw [PresheafOfModules.sections_property]
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add a b ha hb ia ib =>
      rw [map_add]
      exact Submodule.add_mem _ ia ib
    | smul r a ha ia =>
      rw [M.val.map_smul]
      exact Submodule.smul_mem _ _ ia
  isSheaf := by
    intro U a hcover
    by_cases hnonempty : (U.unop : Set ComplexBase).Nonempty
    · obtain ⟨p, hp⟩ := hnonempty
      obtain ⟨V, i, hi, hpV⟩ := hcover p hp
      have hVU : V = U.unop := by
        apply le_antisymm (leOfHom i)
        intro q hq
        have hqp : q = p := Subsingleton.elim _ _
        simpa only [hqp] using hpV
      subst V
      have hiid : i = 𝟙 U.unop := Subsingleton.elim _ _
      subst i
      change M.val.map (𝟙 U) a ∈ Submodule.span
        (ComplexBase.ringCatSheaf.obj.obj U)
        (Set.range (fun j : σ.I => (show M.val.obj U from (σ.s j).val U))) at hi
      simpa using hi
    · have hU : U.unop = ⊥ := by
        apply SetLike.coe_injective
        exact Set.not_nonempty_iff_eq_empty.mp hnonempty
      have hU' : U = op (⊥ : ComplexBase.Opens) := congrArg op hU
      subst U
      rw [empty_section_eq_zero M a]
      exact Submodule.zero_mem _

/-- At Spec C, an epimorphism from a free sheaf really makes its specified
global sections span the module of global sections.  This does not assume
that epimorphisms are globally surjective on arbitrary spaces. -/
theorem generators_span_top (M : OModule ComplexBase)
    (σ : SheafOfModules.GeneratingSections M) :
    Submodule.span (RingSections ComplexBase ⊤)
      (Set.range (fun i : σ.I =>
        (show M.val.obj (op ⊤) from (σ.s i).val (op ⊤)))) = ⊤ := by
  let N : SheafOfModules.Submodule
      (show SheafOfModules.{0} ComplexBase.ringCatSheaf from M) := generatorSpan M σ
  let t : σ.I → N.toSheafOfModules.sections := fun i =>
    PresheafOfModules.sectionsMk
      (fun U => ⟨(σ.s i).val U, Submodule.subset_span ⟨i, rfl⟩⟩)
      (by
        intro U V f
        apply Subtype.ext
        exact PresheafOfModules.sections_property (σ.s i) f)
  let φ : SheafOfModules.free σ.I ⟶ N.toSheafOfModules :=
    N.toSheafOfModules.freeHomEquiv.symm t
  have hfac : φ ≫ N.ι = σ.π := by
    apply M.freeHomEquiv.injective
    funext i
    erw [SheafOfModules.freeHomEquiv_comp_apply]
    change SheafOfModules.sectionsMap N.ι
        ((N.toSheafOfModules.freeHomEquiv
          (N.toSheafOfModules.freeHomEquiv.symm t)) i) =
      (M.freeHomEquiv (M.freeHomEquiv.symm σ.s)) i
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    apply PresheafOfModules.sections_ext
    intro U
    rfl
  haveI : Epi (φ ≫ N.ι) := by rw [hfac]; exact σ.epi
  haveI : Epi N.ι := epi_of_epi φ N.ι
  haveI : Mono N.ι :=
    (SheafOfModules.forget ComplexBase.ringCatSheaf).mono_of_mono_map
      (inferInstanceAs (Mono N.toSubmodule.ι))
  haveI : IsIso N.ι := isIso_of_mono_of_epi N.ι
  apply top_unique
  intro a ha
  obtain ⟨b, hb⟩ :=
    (onCSections_bijective_of_iso (𝟙 ComplexBase) (asIso N.ι)).2 a
  change (b : N.toSubmodule.obj (op ⊤)).val = a at hb
  exact hb ▸ b.property

private theorem sectionValue_unitHomEquiv_symm {Y : Scheme}
    (E : OModule Y) (s : E.sections) :
    sectionValue (E.unitHomEquiv.symm s) = globalSectionFamilyEquiv E s := by
  exact congrArg (fun t : E.sections => t.val (op ⊤))
    (E.unitHomEquiv.apply_symm_apply s)

private theorem sectionFromValue_globalFamily {Y : Scheme}
    (E : OModule Y) (s : E.sections) :
    sectionFromValue (globalSectionFamilyEquiv E s) = E.unitHomEquiv.symm s := by
  apply (sectionValue_bijective E).1
  rw [sectionFromValue_spec, sectionValue_unitHomEquiv_symm]

/-- The pulled generating family is normalized by the very same unit
pullback isomorphism used in the existing section-evaluation definition. -/
private theorem pulled_generator_value {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (E : OModule Y) (x : ComplexBase ⟶ Y) (hx : x ≫ sY = 𝟙 ComplexBase)
    (σ : SheafOfModules.GeneratingSections E) (i : σ.I) :
    evaluateSection sY E x hx (globalSectionFamilyEquiv E (σ.s i)) =
      ((σ.map (Scheme.Modules.pullback x) (unitPullbackIso x).symm).s i).val
        (op ⊤) := by
  let σ' := σ.map (Scheme.Modules.pullback x) (unitPullbackIso x).symm
  have hleg : SheafOfModules.ιFree i ≫ σ.π = E.unitHomEquiv.symm (σ.s i) := by
    symm
    simpa only [SheafOfModules.GeneratingSections.π, Equiv.apply_symm_apply] using
      (SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply σ.π i)
  have hmap : SheafOfModules.ιFree i ≫ σ'.π =
      pullSection x (E.unitHomEquiv.symm (σ.s i)) := by
    change SheafOfModules.ιFree i ≫
        (σ.map (Scheme.Modules.pullback x) (unitPullbackIso x).symm).π = _
    rw [SheafOfModules.GeneratingSections.map_π_eq, ← Category.assoc,
      SheafOfModules.ιFree_mapFreeIso_hom, Category.assoc,
      ← Functor.map_comp, hleg] <;> rfl
  have hsection : (pullbackModule x E).unitHomEquiv.symm (σ'.s i) =
      pullSection x (E.unitHomEquiv.symm (σ.s i)) := by
    calc
      _ = SheafOfModules.ιFree i ≫ σ'.π := by
        simpa only [SheafOfModules.GeneratingSections.π, Equiv.apply_symm_apply] using
          (SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply σ'.π i)
      _ = _ := hmap
  change sectionValue (pullSection x
      (sectionFromValue (globalSectionFamilyEquiv E (σ.s i)))) =
    (σ'.s i).val (op ⊤)
  rw [sectionFromValue_globalFamily, ← hsection, sectionValue_unitHomEquiv_symm] <;> rfl

/-- The scalar restriction used by CSections at Spec C has all coefficients
in its image; it is the canonical Γ(Spec C,O) identification. -/
private theorem complexConstants_id_surjective :
    Function.Surjective (complexConstants (𝟙 ComplexBase)) := by
  intro r
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom r, ?_⟩
  rw [complexConstants_apply_top]
  simp

/-- Global generation implies surjectivity of the actual pullback evaluation
at every complex rational point.  No local-freeness assumption is needed. -/
theorem evaluateSection_surjective_of_globallyGenerated
    {Y : Scheme} (sY : Y ⟶ ComplexBase) (E : OModule Y)
    (x : ComplexBase ⟶ Y) (hx : x ≫ sY = 𝟙 ComplexBase)
    (hE : IsGloballyGenerated E) :
    Function.Surjective (evaluateSection sY E x hx) := by
  obtain ⟨σ⟩ := hE
  let σ' := σ.map (Scheme.Modules.pullback x) (unitPullbackIso x).symm
  intro v
  have hv : v ∈ Submodule.span (RingSections ComplexBase ⊤)
      (Set.range (fun i : σ'.I =>
        (show (pullbackModule x E).val.obj (op ⊤) from (σ'.s i).val (op ⊤)))) := by
    rw [generators_span_top (pullbackModule x E) σ']
    trivial
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    exact ⟨globalSectionFamilyEquiv E (σ.s i),
      pulled_generator_value sY E x hx σ i⟩
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb ia ib =>
    obtain ⟨u, hu⟩ := ia
    obtain ⟨w, hw⟩ := ib
    exact ⟨u + w, by rw [map_add, hu, hw]⟩
  | smul r a ha ia =>
    obtain ⟨u, hu⟩ := ia
    obtain ⟨c, hc⟩ := complexConstants_id_surjective r
    refine ⟨c • u, ?_⟩
    rw [map_smul, hu]
    change (complexConstants (𝟙 ComplexBase) c) •
        (show (pullbackModule x E).val.obj (op ⊤) from a) =
      r • (show (pullbackModule x E).val.obj (op ⊤) from a)
    rw [hc]

end GeneratedFiberEvaluation

namespace Lines

abbrev P := canonicalProjectiveLine
abbrev marking := canonicalMarkedPoint

/-- The other standard point is [0:1], specified by actual homogeneous coordinates. -/
def infinity : ProjectiveLinePoint P := by
  let v : Fin 2 → ℂ := Pi.single 1 1
  have hv : v ≠ 0 := by
    intro h
    have h1 := congrFun h 1
    simpa [v] using h1
  let x := Classical.choose (projectiveCoordinates_pointOfVector (projectiveCoordinates 1) v hv)
  exact ⟨x.val, x.property⟩

theorem zero_ne_infinity : marking.map ≠ infinity.map := by
  let v0 : Fin 2 → ℂ := Pi.single 0 1
  let v1 : Fin 2 → ℂ := Pi.single 1 1
  have hv0 : v0 ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simpa [v0] using h0
  have hv1 : v1 ≠ 0 := by
    intro h
    have h1 := congrFun h 1
    simpa [v1] using h1
  let x0 := Classical.choose
    (projectiveCoordinates_pointOfVector (projectiveCoordinates 1) v0 hv0)
  let x1 := Classical.choose
    (projectiveCoordinates_pointOfVector (projectiveCoordinates 1) v1 hv1)
  have hx0 : (projectiveCoordinates 1).Represents x0 v0 :=
    (Classical.choose_spec
      (projectiveCoordinates_pointOfVector (projectiveCoordinates 1) v0 hv0)).1
  have hx1 : (projectiveCoordinates 1).Represents x1 v1 :=
    (Classical.choose_spec
      (projectiveCoordinates_pointOfVector (projectiveCoordinates 1) v1 hv1)).1
  intro h
  change x0.val = x1.val at h
  have hpoints : x0 = x1 := Subtype.ext h
  obtain ⟨c, _hc, hcoords⟩ :=
    (projectiveCoordinates_samePoint_iff (projectiveCoordinates 1) x0 x1 v0 v1 hx0 hx1).mp hpoints
  have h1 := congrFun hcoords 1
  simpa [v0, v1] using h1

structure FreeLine {n : ℕ} (X : ContactFanoManifold n) where
  curve : RationalCurve P X.variety
  degreeOne : IsIntrinsicContactLine P marking X.contact curve
  free : IsFreeRationalCurve P X.variety (intrinsicTangentBundle X.variety) curve

abbrev TangentFiber {d : ℕ} (X : SmoothProperComplexVariety d) (x : ComplexPoint X) :=
  Fiber (tangentSheaf X.structureMap) x.map

def contactFiber {n : ℕ} (X : ContactFanoManifold n) (x : ComplexPoint X.variety) :
    TangentFiber X.variety x →ₗ[ℂ] Fiber X.contact.sequence.line.sheaf x.map :=
  fiberMap X.contact.sequence.form x.map

def contactPlane {n : ℕ} (X : ContactFanoManifold n) (x : ComplexPoint X.variety) :
    Submodule ℂ (TangentFiber X.variety x) := LinearMap.ker (contactFiber X x)

/-- Sign convention: this is theta([u,v]), i.e. minus d(alpha) on F.
Only NONVANISHING is used in selecting a suitable pair. -/
def leviFiberValue {n : ℕ} (X : ContactFanoManifold n) (x : ComplexPoint X.variety)
    (u v : Fiber X.contact.sequence.distribution.sheaf x.map) :
    Fiber X.contact.sequence.line.sheaf x.map :=
  (pullbackPair x.map (intrinsicLeviPair X.contact.sequence)).apply ⊤ u v

def NonzeroLeviPair {n : ℕ} (X : ContactFanoManifold n) (x : ComplexPoint X.variety)
    (a b : TangentFiber X.variety x) : Prop :=
  ∃ u v : Fiber X.contact.sequence.distribution.sheaf x.map,
    fiberMap X.contact.sequence.inclusion x.map u = a ∧
    fiberMap X.contact.sequence.inclusion x.map v = b ∧ leviFiberValue X x u v ≠ 0

set_option backward.isDefEq.respectTransparency false in
/-- Values of sections of f*TX at the node, transported by the actual equality f(0)=x. -/
theorem leviFiberValue_smul_smul {n : ℕ} (X : ContactFanoManifold n)
    (x : ComplexPoint X.variety) (c d : ℂ)
    (u v : Fiber X.contact.sequence.distribution.sheaf x.map) :
    leviFiberValue X x (c • u) (d • v) = c • d • leviFiberValue X x u v := by
  change (pullbackPair x.map (intrinsicLeviPair X.contact.sequence)).apply ⊤
      ((complexConstants (𝟙 ComplexBase) c) •
        (show SectionsOn (pullbackModule x.map X.contact.sequence.distribution.sheaf) ⊤ from u))
      ((complexConstants (𝟙 ComplexBase) d) •
        (show SectionsOn (pullbackModule x.map X.contact.sequence.distribution.sheaf) ⊤ from v)) =
    (complexConstants (𝟙 ComplexBase) c) •
      ((complexConstants (𝟙 ComplexBase) d) •
        (pullbackPair x.map (intrinsicLeviPair X.contact.sequence)).apply ⊤ u v)
  simp only [map_smul, LinearMap.smul_apply, smul_smul, mul_comm]

set_option backward.isDefEq.respectTransparency false in
theorem contactPlane_dimension {n : ℕ} (X : ContactFanoManifold n)
    (x : ComplexPoint X.variety) : Module.finrank ℂ (contactPlane X x) = 2*n := by
  have hex := vectorBundle_fiber_exact X.contact.sequence.distribution
    (intrinsicTangentBundle X.variety) X.contact.sequence.line
    X.contact.sequence.inclusion X.contact.sequence.form
    X.contact.sequence.comp_zero X.contact.sequence.shortExact x.map
  change Module.finrank ℂ (LinearMap.ker (fiberMap X.contact.sequence.form x.map)) = 2*n
  rw [← hex.2.2, LinearMap.finrank_range_of_inj hex.1]
  exact fiber_dimension X.contact.sequence.distribution x.map

def nodeEvaluation {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X)
    (x : ComplexPoint X.variety) (hx : marking.map ≫ f.curve.map = x.map) :
    CSections P.structureMap (pullbackModule f.curve.map (tangentSheaf X.variety.structureMap))
      →ₗ[ℂ] TangentFiber X.variety x :=
  (fiberComposition f.curve.map marking.map x.map hx
    (tangentSheaf X.variety.structureMap)).comp
      (evaluateSection P.structureMap _ marking.map marking.overC)

/-- Holding the OUTER endpoint fixed gives the positive node directions.
This does not choose a splitting or insert an arbitrary Lagrangian subspace. -/
def positiveNodeSpace {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X)
    (x : ComplexPoint X.variety) (hx : marking.map ≫ f.curve.map = x.map) :
    Submodule ℂ (TangentFiber X.variety x) :=
  Submodule.map (nodeEvaluation f x hx)
    (LinearMap.ker (evaluateSection P.structureMap
      (pullbackModule f.curve.map (tangentSheaf X.variety.structureMap))
      infinity.map infinity.overC))

/-- The tangent map uses the canonical differential, not an extra field in FreeLine. -/
def nodeDifferential {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X)
    (x : ComplexPoint X.variety) (hx : marking.map ≫ f.curve.map = x.map) :
    Fiber (tangentSheaf P.structureMap) marking.map →ₗ[ℂ] TangentFiber X.variety x :=
  (fiberComposition f.curve.map marking.map x.map hx
    (tangentSheaf X.variety.structureMap)).comp
      (fiberMap (differentialOver (projectiveLineVariety P) X.variety
        f.curve.map f.curve.overC) marking.map)

theorem nodeEvaluation_surjective {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map) :
    Function.Surjective (nodeEvaluation f x hx) := by
  change Function.Surjective
    ((fiberComposition f.curve.map marking.map x.map hx
      (tangentSheaf X.variety.structureMap)).comp
      (evaluateSection P.structureMap _ marking.map marking.overC))
  exact (fiberComposition_bijective f.curve.map marking.map x.map hx
    (tangentSheaf X.variety.structureMap)).2.comp
      (GeneratedFiberEvaluation.evaluateSection_surjective_of_globallyGenerated
        P.structureMap _ marking.map marking.overC f.free)


end Lines

end LeBrunSalamon.Construction

end
