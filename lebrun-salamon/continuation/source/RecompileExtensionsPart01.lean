import LSP1TangentSections
import LSP1SourceAlgebra
import LSP1TensorSquare
import LSP1TensorTaylor
import LSAffineFrame
import LSAffineDerivations
import RecompileExtensionCore
import LSConePole
import LSSecondDiagonalAlgebra
import LSSectionCover
import LSExternalFrameCoefficients
import LSPublishedProjectiveSpace
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
import Mathlib.Topology.Sheaves.SheafCondition.Sites

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


/- BEGIN UNCOMPILED continuation cech_yoneda_comparison.lean.txt -/
/-!
The actual two-open Cech equation and the original Yoneda vanishing predicate.

Uncompiled continuation. Insert after LocalExtensionSplitting and
ExtensionRealization. Both implications now use constructed actual extensions
and actual right inverses, rather than redefining the cohomology predicate.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.TwoChartSections LeBrunSalamon.P1Charts

namespace LeBrunSalamon.CechYoneda

/-- On a covering pair of affine opens, a locally free kernel has the
original universal extension-splitting property exactly when its actual
two-open difference equation is always solvable. -/
theorem vanishing_iff_pairDifference_surjective {X : Scheme} {E : OModule X} {r : ℕ}
    (hE : IsLocallyFreeOfRank E r) (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hcover : U ⊔ V = ⊤) :
    HasVanishingFirstCohomology E ↔ Function.Surjective (pairDifference E U V) :=
  ⟨ExtensionRealization.pairDifference_surjective_of_hasVanishingFirstCohomology
      E U V hcover,
    LocalExtensionSplitting.firstCohomology_of_affine_pair hE U V hU hV hcover⟩

/-- The original twist has vanishing first cohomology exactly in degrees
at least -1. The negative direction is backed by a realized nonsplit extension. -/
theorem twist_firstCohomology_iff (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (d : ℤ) : HasVanishingFirstCohomology (projectiveTwist P p d).sheaf ↔ -1 ≤ d :=
  (vanishing_iff_pairDifference_surjective (projectiveTwist P p d).locallyFree
    (chartOpen 0) (chartOpen 1) (chartOpen_affine 0) (chartOpen_affine 1)
    chartOpen_zero_sup_one).trans (P1TwistSections.pairDifference_surjective_iff P p d)

end LeBrunSalamon.CechYoneda

end
/- END UNCOMPILED continuation cech_yoneda_comparison.lean.txt -/

/- BEGIN UNCOMPILED continuation split_cohomology.lean.txt -/
/-!
Actual first-cohomology vanishing for finite split bundles.

Uncompiled continuation. Insert after the original
HasVanishingFirstCohomology definition, DirectSumGeometry.coproduct_total,
P1SplitBundles.splitSheaf_rank, LocalExtensionSplitting, and
ExtensionRealization's negative-twist obstruction. The original Yoneda
predicate and its quantification over every middle sheaf are unchanged.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseEighteen LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.TwoChartSections LeBrunSalamon.P1Charts
open scoped BigOperators

namespace LeBrunSalamon.FirstCohomology

/-- Vanishing of the original extension-splitting predicate passes to an
actual retract. Push out an extension along the inclusion, split that
actual pushed extension, then map it back using the retraction. -/
theorem of_retract {X : Scheme} {E F : OModule X}
    (j : E ⟶ F) (r : F ⟶ E) (hjr : j ≫ r = 𝟙 E)
    (hF : HasVanishingFirstCohomology F) : HasVanishingFirstCohomology E := by
  intro M i p hz hex
  let S := ShortComplex.mk i p hz
  let T := S.push j
  have hT : T.ShortExact := hex.push j
  obtain ⟨s, hs⟩ := hF T.X₂ T.f T.g T.zero hT
  have hcomm : i ≫ 𝟙 M = j ≫ (r ≫ i) := by
    rw [Category.comp_id, ← Category.assoc, hjr, Category.id_comp]
  have hzero : i ≫ p = j ≫ (0 : F ⟶ structureModule X) := by simpa using hz
  let k : T.X₂ ⟶ M := pushout.desc (𝟙 M) (r ≫ i) hcomm
  have hk : k ≫ p = T.g := by
    change pushout.desc (𝟙 M) (r ≫ i) hcomm ≫ p = pushout.desc p 0 hzero
    apply pushout.hom_ext
    · rw [pushout.inl_desc_assoc, pushout.inl_desc, Category.id_comp]
    · rw [pushout.inr_desc_assoc, pushout.inr_desc, Category.assoc, hz, comp_zero]
  exact ⟨s ≫ k, by rw [Category.assoc, hk, hs]⟩

/-- The original Yoneda-vanishing predicate is invariant under an actual
sheaf isomorphism; no cohomology group or Ext model is substituted. -/
theorem iso_iff {X : Scheme} {E F : OModule X} (e : E ≅ F) :
    HasVanishingFirstCohomology E ↔ HasVanishingFirstCohomology F :=
  ⟨fun h => of_retract e.inv e.hom e.inv_hom_id h,
    fun h => of_retract e.hom e.inv e.hom_inv_id h⟩

/-- Every actual coproduct summand inherits the original vanishing
predicate through its specified inclusion and projection. -/
theorem coproduct_summand {X : Scheme} {I : Type} (E : I → OModule X)
    (h : HasVanishingFirstCohomology (∐ E)) (i : I) :
    HasVanishingFirstCohomology (E i) := by
  classical
  exact of_retract (Sigma.ι E i) (Sigma.π E i) (Sigma.ι_π_eq_id E i) h

end LeBrunSalamon.FirstCohomology

namespace LeBrunSalamon.DirectSumCech

/-- Evaluation of an actual sheaf morphism on one specified section is
additive in that morphism. This retains the original open-section types. -/
def homValue {X : Scheme} (E F : OModule X) (U : X.Opens) (s : SectionsOn E U) :
    (E ⟶ F) →+ SectionsOn F U where
  toFun f := f.app U s
  map_zero' := rfl
  map_add' f g := rfl

/-- Finite reconstruction of sections of the actual sheaf coproduct,
obtained from its established categorical projection/inclusion identity. -/
theorem coproduct_section_total {X : Scheme} {I : Type} [Fintype I] [DecidableEq I]
    (E : I → OModule X) (U : X.Opens) (s : SectionsOn (∐ E) U) :
    (∑ i, (Sigma.ι E i).app U ((Sigma.π E i).app U s)) = s := by
  classical
  have h := congrArg (homValue (∐ E) (∐ E) U s) (DirectSumGeometry.coproduct_total E)
  rw [map_sum] at h
  change (∑ i, (Sigma.ι E i).app U ((Sigma.π E i).app U s)) = s at h
  exact h

/-- Solve the actual two-open equation for a finite coproduct by
projecting its overlap section, solving each summand, and summing the
actual included local solutions. The empty coproduct is covered too. -/
theorem pairDifference_surjective {X : Scheme} {I : Type} [Fintype I]
    (E : I → OModule X) (U V : X.Opens)
    (h : ∀ i, Function.Surjective (pairDifference (E i) U V)) :
    Function.Surjective (pairDifference (∐ E) U V) := by
  classical
  intro w
  choose ab hab using fun i => h i ((Sigma.π E i).app (U ⊓ V) w)
  refine ⟨∑ i, ((Sigma.ι E i).app U (ab i).1, (Sigma.ι E i).app V (ab i).2), ?_⟩
  rw [map_sum]
  calc
    _ = ∑ i, (Sigma.ι E i).app (U ⊓ V) ((Sigma.π E i).app (U ⊓ V) w) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← ExtensionGluing.pairDifference_map, hab i]
    _ = w := coproduct_section_total E (U ⊓ V) w

/-- Conversely, the actual two-open differential of each summand is
surjective if the coproduct differential is. This uses its actual split
projection and does not use a numerical dimension count. -/
theorem pairDifference_summand_surjective {X : Scheme} {I : Type}
    (E : I → OModule X) (U V : X.Opens)
    (h : Function.Surjective (pairDifference (∐ E) U V)) (i : I) :
    Function.Surjective (pairDifference (E i) U V) := by
  classical
  intro w
  obtain ⟨ab, hab⟩ := h ((Sigma.ι E i).app (U ⊓ V) w)
  refine ⟨((Sigma.π E i).app U ab.1, (Sigma.π E i).app V ab.2), ?_⟩
  rw [← ExtensionGluing.pairDifference_map, hab]
  change (Sigma.ι E i ≫ Sigma.π E i).app (U ⊓ V) w = w
  rw [Sigma.ι_π_eq_id] <;> rfl

theorem pairDifference_surjective_iff {X : Scheme} {I : Type} [Fintype I]
    (E : I → OModule X) (U V : X.Opens) :
    Function.Surjective (pairDifference (∐ E) U V) ↔
      ∀ i, Function.Surjective (pairDifference (E i) U V) :=
  ⟨fun h i => pairDifference_summand_surjective E U V h i,
    pairDifference_surjective E U V⟩

end LeBrunSalamon.DirectSumCech

namespace LeBrunSalamon.P1SplitBundles

/-- The actual two-chart differential of the original split sheaf is
surjective exactly when each original twist degree is at least -1. -/
theorem splitSheaf_pairDifference_surjective_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (a : TangentSplittingProfile r) :
    Function.Surjective (pairDifference (splitSheaf P p a) (chartOpen 0) (chartOpen 1)) ↔
      ∀ i, -1 ≤ a.degree i := by
  rw [splitSheaf, DirectSumCech.pairDifference_surjective_iff]
  exact forall_congr' (fun i => P1TwistSections.pairDifference_surjective_iff P p (a.degree i))

/-- The actual finite-sum differential and whole-affine unit lifts split
every original extension of O by this split sheaf. Its middle term is
arbitrary; affine lifting derives the needed regularity from exactness. -/
theorem splitSheaf_firstCohomology_of_ge_neg_one (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (a : TangentSplittingProfile r)
    (h : ∀ i, -1 ≤ a.degree i) : HasVanishingFirstCohomology (splitSheaf P p a) :=
  LocalExtensionSplitting.firstCohomology_of_affine_pair
    (P1SplitBundles.splitSheaf_rank P p a) (chartOpen 0) (chartOpen 1)
    (chartOpen_affine 0) (chartOpen_affine 1) chartOpen_zero_sup_one
    ((splitSheaf_pairDifference_surjective_iff P p a).mpr h)

/-- The converse uses the realized nonsplit twist extension after passing
to each actual summand retract. It does not identify Yoneda H1 with a
chosen Cech quotient by definition. -/
theorem splitSheaf_firstCohomology_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ} (a : TangentSplittingProfile r) :
    HasVanishingFirstCohomology (splitSheaf P p a) ↔ ∀ i, -1 ≤ a.degree i := by
  constructor
  · intro h i
    apply ExtensionRealization.twist_degree_ge_neg_one_of_hasVanishingFirstCohomology
      P p (a.degree i)
    exact FirstCohomology.coproduct_summand
      (fun j : Fin r => (projectiveTwist P p (a.degree j)).sheaf) h i
  · exact splitSheaf_firstCohomology_of_ge_neg_one P p a

/-- The original first-cohomology criterion for a bundle with a supplied
actual splitting. Classification of arbitrary bundles is not used. -/
theorem splitBundle_firstCohomology_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ}
    (E : AlgebraicVectorBundle ProjectiveLine r) (a : TangentSplittingProfile r)
    (ha : RealizesSplitting P p E a) :
    HasVanishingFirstCohomology E.sheaf ↔ ∀ i, -1 ≤ a.degree i := by
  obtain ⟨e⟩ := ha
  exact (FirstCohomology.iso_iff e).trans (splitSheaf_firstCohomology_iff P p a)

end LeBrunSalamon.P1SplitBundles

end
/- END UNCOMPILED continuation split_cohomology.lean.txt -/

/- BEGIN UNCOMPILED continuation split_tensor.lean.txt -/
/-!
Actual tensor twists of a supplied splitting and two-point obstructions.

Uncompiled continuation. Insert after the finite-sum cohomology comparison.
Tensor distributes through the actual coproduct by its proved tensor-Hom
adjunction, and each summand is identified by the original twist-addition iso.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseEighteen LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo

namespace LeBrunSalamon.P1SplitBundles

/-- Tensoring the actual direct sum by O(k) adds k to each summand degree.
The comparison uses the actual tensor-Hom adjunction and twist-addition maps. -/
def splitTensorIso (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (a : TangentSplittingProfile r) (k : ℤ) :
    tensorSheaf (splitSheaf P p a) (projectiveTwist P p k).sheaf ≅
      splitSheaf P p ⟨fun i => a.degree i + k⟩ := by
  letI := tensorRight_preservesColimits
    (internalHomPresentation (projectiveTwist P p k).sheaf)
  exact PreservesCoproduct.iso (tensorRightFunctor (projectiveTwist P p k).sheaf)
      (fun i : Fin r => (projectiveTwist P p (a.degree i)).sheaf) ≪≫
    Sigma.mapIso (fun i => Classical.choice (projectiveTwist_add P p (a.degree i) k))

/-- A supplied actual splitting transports through tensoring by a twist.
No existence theorem for splittings of arbitrary bundles is used. -/
def realizedTensorIso (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {r : ℕ} (E : AlgebraicVectorBundle ProjectiveLine r) (a : TangentSplittingProfile r)
    (ha : RealizesSplitting P p E a) (k : ℤ) :
    tensorSheaf E.sheaf (projectiveTwist P p k).sheaf ≅
      splitSheaf P p ⟨fun i => a.degree i + k⟩ :=
  tensorIso (Classical.choice ha) (Iso.refl _) ≪≫ splitTensorIso P p a k

/-- The actual original Yoneda vanishing criterion for every integer
twist of a bundle with a supplied splitting. -/
theorem realizedTensor_firstCohomology_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ}
    (E : AlgebraicVectorBundle ProjectiveLine r) (a : TangentSplittingProfile r)
    (ha : RealizesSplitting P p E a) (k : ℤ) :
    HasVanishingFirstCohomology (tensorSheaf E.sheaf (projectiveTwist P p k).sheaf) ↔
      ∀ i, -1 ≤ a.degree i + k :=
  (FirstCohomology.iso_iff (realizedTensorIso P p E a ha k)).trans
    (splitSheaf_firstCohomology_iff P p ⟨fun i => a.degree i + k⟩)

/-- Positive splitting degrees eliminate the original two-point
obstruction predicate, for the actual tensor product with O(-2). -/
theorem veryFreeBundle_twoPointObstructions_vanish (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ}
    (E : AlgebraicVectorBundle ProjectiveLine r) (a : TangentSplittingProfile r)
    (ha : RealizesSplitting P p E a) (hpos : a.IsVeryFree) :
    HasVanishingFirstCohomology
      (tensorSheaf E.sheaf (projectiveTwist P p (-2)).sheaf) := by
  apply (realizedTensor_firstCohomology_iff P p E a ha (-2)).mpr
  intro i
  have hi := hpos i
  omega

end LeBrunSalamon.P1SplitBundles

end
/- END UNCOMPILED continuation split_tensor.lean.txt -/

namespace LeBrunSalamon.PhaseThirtyTwo

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseEighteen
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight

theorem splitBundle_firstCohomology_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ}
    (E : AlgebraicVectorBundle ProjectiveLine r) (a : TangentSplittingProfile r)
    (ha : RealizesSplitting P p E a) :
    HasVanishingFirstCohomology E.sheaf ↔ ∀ i, -1 ≤ a.degree i := by
  exact P1SplitBundles.splitBundle_firstCohomology_iff P p E a ha

theorem freeBundle_firstCohomology_vanishes (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ}
    (E : AlgebraicVectorBundle ProjectiveLine r) (hE : IsGloballyGenerated E.sheaf) :
    HasVanishingFirstCohomology E.sheaf := by
  obtain ⟨a, ha⟩ := birkhoffGrothendieck P p E
  apply (splitBundle_firstCohomology_iff P p E a ha).mpr
  have hfree := (splitBundle_globallyGenerated_iff P p E a ha).mp hE
  intro i
  have hi := hfree i
  omega

theorem veryFreeBundle_twoPointObstructions_vanish (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {r : ℕ}
    (E : AlgebraicVectorBundle ProjectiveLine r) (a : TangentSplittingProfile r)
    (ha : RealizesSplitting P p E a) (hpos : a.IsVeryFree) :
    HasVanishingFirstCohomology
      (tensorSheaf E.sheaf (projectiveTwist P p (-2)).sheaf) := by
  exact P1SplitBundles.veryFreeBundle_twoPointObstructions_vanish P p E a ha hpos

def degreeOnCurve (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} {X : SmoothProperComplexVariety d}
    (f : ParametrizedCurve P X) (L : LineBundle X.scheme) : ℤ :=
  projectiveLineDegree P p (pullbackLine f.map L)

def IsIntrinsicContactLine (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X) (f : RationalCurve P X) : Prop :=
  degreeOnCurve P p f.toParametrizedCurve C.sequence.line = 1

def IsIntrinsicContactConic (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X) (f : RationalCurve P X) : Prop :=
  degreeOnCurve P p f.toParametrizedCurve C.sequence.line = 2

theorem contact_anticanonicalDegree (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) (f : ParametrizedCurve P X) :
    degreeOnCurve P p f (anticanonicalLine X) =
      ((n : ℤ) + 1) * degreeOnCurve P p f C.sequence.line := by
  obtain ⟨e⟩ := contact_anticanonical X C
  obtain ⟨t⟩ := linePower_pullback f.map C.sequence.line (n + 1)
  unfold degreeOnCurve
  calc
    projectiveLineDegree P p (pullbackLine f.map (anticanonicalLine X)) =
        projectiveLineDegree P p (linePower (pullbackLine f.map C.sequence.line) (n + 1)) :=
      projectiveLineDegree_iso P p _ _ ((Scheme.Modules.pullback f.map).mapIso e ≪≫ t)
    _ = ((n : ℤ) + 1) * projectiveLineDegree P p (pullbackLine f.map C.sequence.line) := by
      rw [projectiveLineDegree_power]
      simp only [Nat.cast_add, Nat.cast_one]


set_option backward.isDefEq.respectTransparency false in
/-- Every candidate for theta composed with df has to vanish for a
contact line: this follows from Hom(O(2),O(1))=0. -/
theorem intrinsicContactLine_velocity_zero (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) (f : RationalCurve P X)
    (hf : IsIntrinsicContactLine P p C f)
    (v : tangentSheaf P.structureMap ⟶ pullbackModule f.map C.sequence.line.sheaf) :
    v = 0 := by
  obtain ⟨eT⟩ := projectiveLine_tangent_twist P p
  have hL := projectiveLineDegree_spec P p (pullbackLine f.map C.sequence.line)
  change projectiveLineDegree P p (pullbackLine f.map C.sequence.line) = 1 at hf
  rw [hf] at hL
  obtain ⟨eL⟩ := hL
  have hz := descendingDegree_noHom P p 2 1 (by norm_num) (eT.inv ≫ v ≫ eL.hom)
  have he := congrArg (fun w => eT.hom ≫ w ≫ eL.inv) hz
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.hom_inv_id_assoc, comp_zero, zero_comp] using he

set_option backward.isDefEq.respectTransparency false in
/-- For a degree-two curve, a nonzero contact velocity is everywhere
nonzero: both source and target are O(2). -/
theorem intrinsicContactConic_nonzeroVelocity_isIso (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) (f : RationalCurve P X)
    (hf : IsIntrinsicContactConic P p C f)
    (v : tangentSheaf P.structureMap ⟶ pullbackModule f.map C.sequence.line.sheaf)
    (hv : v ≠ 0) : IsIso v := by
  obtain ⟨eT⟩ := projectiveLine_tangent_twist P p
  have hL := projectiveLineDegree_spec P p (pullbackLine f.map C.sequence.line)
  change projectiveLineDegree P p (pullbackLine f.map C.sequence.line) = 2 at hf
  rw [hf] at hL
  obtain ⟨eL⟩ := hL
  let w := eT.inv ≫ v ≫ eL.hom
  have hw : w ≠ 0 := by
    intro hz
    apply hv
    have he := congrArg (fun w => eT.hom ≫ w ≫ eL.inv) hz
    simpa only [w, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc, comp_zero, zero_comp] using he
  haveI : IsIso w := equalDegree_nonzeroHom_isIso P p 2 w hw
  have he : v = eT.hom ≫ w ≫ eL.inv := by simp [w]
  rw [he]
  infer_instance

/-- Primitive Picard condition: L, rather than an unspecified ample
root of L, generates all line-bundle isomorphism classes. -/
def HasPrimitiveContactPicard {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X) : Prop :=
  ∀ M : LineBundle X.scheme,
    ∃! k : ℤ, Nonempty (M.sheaf ≅ (linePowerInt C.sequence.line k).sheaf)

/-- Classical contact-line existence is a separate theorem from the
primitive Picard hypothesis, not a field built into it. -/
theorem primitiveContactFano_hasFreeContactLine
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) {n : ℕ}
    (X : ContactFanoManifold n) (hPic : HasPrimitiveContactPicard X.contact) :
    ∃ f : RationalCurve P X.variety,
      IsIntrinsicContactLine P p X.contact f ∧
      IsFreeRationalCurve P X.variety (intrinsicTangentBundle X.variety) f := by sorry

end LeBrunSalamon.PhaseThirtyTwo



/-!
# Phase 33 -- splitting arithmetic with explicit geometric boundaries

These are integer profiles and linear-algebra statements. The bridge to
actual bundles is `RealizesSplitting` in Phase 32. Expected dimension is
never promoted to actual smoothness, dominance, or generic finiteness.
-/

namespace LeBrunSalamon.PhaseThirtyThree

open LeBrunSalamon.PhaseEighteen LeBrunSalamon.PhaseTwenty

variable {r : ℕ}

def profileDegree (a : TangentSplittingProfile r) : ℤ := ∑ i, a.degree i

def twistProfile (a : TangentSplittingProfile r) (k : ℤ) : TangentSplittingProfile r :=
  ⟨fun i => a.degree i + k⟩

def dualProfile (a : TangentSplittingProfile r) : TangentSplittingProfile r :=
  ⟨fun i => -a.degree i⟩

def profileEulerCharacteristic (a : TangentSplittingProfile r) : ℤ :=
  (a.predictedHZero : ℤ) - (a.predictedHOne : ℤ)

theorem profile_riemannRoch (a : TangentSplittingProfile r) :
    profileEulerCharacteristic a = (r : ℤ) + profileDegree a := by
  unfold profileEulerCharacteristic TangentSplittingProfile.predictedHZero TangentSplittingProfile.predictedHOne profileDegree
  push_cast
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ i : Fin r, (((a.degree i + 1).toNat : ℤ) - ((-a.degree i - 1).toNat : ℤ))) =
        ∑ i : Fin r, (a.degree i + 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      omega
    _ = (r : ℤ) + ∑ i : Fin r, a.degree i := by simp [Finset.sum_add_distrib, add_comm]

theorem twistProfile_degree (a : TangentSplittingProfile r) (k : ℤ) :
    profileDegree (twistProfile a k) = profileDegree a + (r : ℤ) * k := by
  simp [profileDegree, twistProfile, Finset.sum_add_distrib]

theorem dualProfile_degree (a : TangentSplittingProfile r) :
    profileDegree (dualProfile a) = -profileDegree a := by
  simp [profileDegree, dualProfile]

theorem profile_serreDuality_number (a : TangentSplittingProfile r) :
    a.predictedHOne = (twistProfile (dualProfile a) (-2)).predictedHZero := by
  unfold TangentSplittingProfile.predictedHOne TangentSplittingProfile.predictedHZero
  apply Finset.sum_congr rfl
  intro i hi
  simp only [twistProfile, dualProfile]
  congr 1
  ring

theorem profile_hOne_zero_iff (a : TangentSplittingProfile r) :
    a.predictedHOne = 0 ↔ ∀ i, -1 ≤ a.degree i := by
  simp only [TangentSplittingProfile.predictedHOne, Finset.sum_eq_zero_iff,
    Finset.mem_univ, forall_true_left, Int.toNat_eq_zero]
  constructor <;> intro h i <;> have hi := h i <;> omega

theorem profile_hZero_zero_iff (a : TangentSplittingProfile r) :
    a.predictedHZero = 0 ↔ ∀ i, a.degree i < 0 := by
  simp only [TangentSplittingProfile.predictedHZero, Finset.sum_eq_zero_iff,
    Finset.mem_univ, forall_true_left, Int.toNat_eq_zero]
  constructor <;> intro h i <;> have hi := h i <;> omega

theorem freeProfile_hOne_zero (a : TangentSplittingProfile r) (h : a.IsFree) :
    a.predictedHOne = 0 := by
  apply (profile_hOne_zero_iff a).mpr
  intro i
  have hi := h i
  omega

theorem freeProfile_hZero (a : TangentSplittingProfile r) (h : a.IsFree) :
    (a.predictedHZero : ℤ) = (r : ℤ) + profileDegree a := by
  have he := profile_riemannRoch a
  simpa [profileEulerCharacteristic, freeProfile_hOne_zero a h] using he

theorem profile_twoPointObstructions_zero_iff (a : TangentSplittingProfile r) :
    a.predictedTwoMarkedHOne = 0 ↔ a.IsVeryFree := by
  simp only [TangentSplittingProfile.predictedTwoMarkedHOne, TangentSplittingProfile.IsVeryFree,
    Finset.sum_eq_zero_iff, Finset.mem_univ, forall_true_left, Int.toNat_eq_zero]
  constructor <;> intro h i <;> have hi := h i <;> omega

theorem profile_twoPointEuler (a : TangentSplittingProfile r) :
    (a.predictedTwoMarkedHZero : ℤ) - (a.predictedTwoMarkedHOne : ℤ) =
      profileDegree a - (r : ℤ) := by
  have he := profile_riemannRoch (twistProfile a (-2))
  have h0 : (twistProfile a (-2)).predictedHZero = a.predictedTwoMarkedHZero := by
    unfold TangentSplittingProfile.predictedHZero TangentSplittingProfile.predictedTwoMarkedHZero
    apply Finset.sum_congr rfl
    intro i hi
    simp only [twistProfile]
    congr 1
    ring
  have h1 : (twistProfile a (-2)).predictedHOne = a.predictedTwoMarkedHOne := by
    unfold TangentSplittingProfile.predictedHOne TangentSplittingProfile.predictedTwoMarkedHOne
    apply Finset.sum_congr rfl
    intro i hi
    simp only [twistProfile]
    congr 1
    ring
  rw [profileEulerCharacteristic, h0, h1, twistProfile_degree] at he
  omega

theorem veryFreeProfile_degreeBound (a : TangentSplittingProfile r)
    (h : a.IsVeryFree) : (r : ℤ) ≤ profileDegree a := by
  calc
    (r : ℤ) = ∑ _i : Fin r, (1 : ℤ) := by simp
    _ ≤ ∑ i : Fin r, a.degree i := Finset.sum_le_sum (fun i hi => h i)

theorem minimumVeryFreeDegree_forces_allOnes (a : TangentSplittingProfile r)
    (h : a.IsVeryFree) (hd : profileDegree a = r) :
    ∀ i, a.degree i = 1 := by
  have hs : (∑ i : Fin r, (a.degree i - 1)) = 0 := by
    simp only [profileDegree] at hd
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    omega
  have hn : ∀ i ∈ (Finset.univ : Finset (Fin r)), 0 ≤ a.degree i - 1 := by
    intro i hi
    exact sub_nonneg.mpr (h i)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hs
  intro i
  have hi := hz i (Finset.mem_univ i)
  omega

/-- The near-minimal very-free degree has one 2 and all remaining 1s.
This numerical conclusion is not a proof that a smoothing exists. -/
theorem nextVeryFreeDegree_forces_quasiLine (a : TangentSplittingProfile r)
    (h : a.IsVeryFree) (hd : profileDegree a = (r : ℤ) + 1) :
    ∃! j : Fin r, a.degree j = 2 ∧ ∀ i, i ≠ j → a.degree i = 1 := by
  have hs : (∑ i : Fin r, (a.degree i - 1)) = 1 := by
    simp only [profileDegree] at hd
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    omega
  have hn : ∀ i ∈ (Finset.univ : Finset (Fin r)), 0 ≤ a.degree i - 1 := by
    intro i hi
    exact sub_nonneg.mpr (h i)
  have hex : ∃ j : Fin r, a.degree j - 1 ≠ 0 := by
    by_contra hh
    push Not at hh
    have : (∑ i : Fin r, (a.degree i - 1)) = 0 := Finset.sum_eq_zero (fun i hi => hh i)
    omega
  obtain ⟨j, hj⟩ := hex
  have hle : a.degree j - 1 ≤ 1 := by
    calc
      a.degree j - 1 ≤ ∑ i : Fin r, (a.degree i - 1) :=
        Finset.single_le_sum hn (Finset.mem_univ j)
      _ = 1 := hs
  have hj2 : a.degree j = 2 := by have := h j; omega
  have hothers : ∀ i, i ≠ j → a.degree i = 1 := by
    intro i hij
    have hij' : j ≠ i := Ne.symm hij
    have hsum : (a.degree j - 1) + (a.degree i - 1) ≤ 1 := by
      calc
        (a.degree j - 1) + (a.degree i - 1) ≤ ∑ k : Fin r, (a.degree k - 1) := by
          have hh := Finset.sum_le_sum_of_subset_of_nonneg
            (show ({j,i} : Finset (Fin r)) ⊆ Finset.univ from Finset.subset_univ _)
            (fun k hk hk' => hn k hk)
          simpa only [Finset.sum_pair hij'] using hh
        _ = 1 := hs
    have := h i
    omega
  refine ⟨j, ⟨hj2, hothers⟩, ?_⟩
  intro k hk
  by_contra hkj
  have := hothers k hkj
  omega

theorem quasiLineProfile_totalDegree (n : ℕ) :
    profileDegree (quasiLineProfile n) = 2 * ((n : ℤ) + 1) := by
  simp [profileDegree, quasiLineProfile, Fin.sum_univ_succ]
  omega

theorem freeContactLine_positiveDegreeSum (n : ℕ) (hn : 1 ≤ n) :
    profileDegree (standardContactLineProfile n) = (n : ℤ) + 1 := by
  exact standardContactLineProfile_degree n hn

/-- All possible maps O(2)->⊕O(a_i) vanish if every a_i<2.
This records the arithmetic test; its bundle version uses Phase 32. -/
def CanReceiveNonzeroTangentMap (a : TangentSplittingProfile r) : Prop :=
  ∃ i, 2 ≤ a.degree i

theorem veryFree_with_tangent_degreeBound (a : TangentSplittingProfile r)
    (h : a.IsVeryFree) (ht : CanReceiveNonzeroTangentMap a) :
    (r : ℤ) + 1 ≤ profileDegree a := by
  have hb := veryFreeProfile_degreeBound a h
  obtain ⟨i, hi⟩ := ht
  by_contra hc
  have heq : profileDegree a = r := by omega
  have hi1 := minimumVeryFreeDegree_forces_allOnes a h heq i
  omega

/-- Parameterized Hom(P1,X) has three automorphism dimensions. Fixing
two SOURCE marks leaves a one-dimensional stabilizer, not zero. -/
def expectedParametrizedHomDimension (d : ℕ) (antiDegree : ℤ) : ℤ :=
  (d : ℤ) + antiDegree

def expectedUnparameterizedMarkedDimension (d marks : ℕ)
    (antiDegree : ℤ) : ℤ :=
  (d : ℤ) + antiDegree - 3 + (marks : ℤ)

theorem twoMarkedDimension_agrees (d : ℕ) (a : ℤ) :
    expectedUnparameterizedMarkedDimension d 2 a =
      expectedTwoMarkedMapDimension d a := by
  simp [expectedUnparameterizedMarkedDimension, expectedTwoMarkedMapDimension]
  ring

theorem quasiLine_parametrizedEvaluationRelativeDimension (n : ℕ) :
    expectedParametrizedHomDimension (2 * n + 1) (2 * ((n : ℤ) + 1)) -
      2 * (2 * (n : ℤ) + 1) = 1 := by
  simp [expectedParametrizedHomDimension]
  ring

theorem quasiLine_unparameterizedEvaluationRelativeDimension (n : ℕ) :
    expectedUnparameterizedMarkedDimension (2 * n + 1) 2 (2 * ((n : ℤ) + 1)) -
      2 * (2 * (n : ℤ) + 1) = 0 := by
  simp [expectedUnparameterizedMarkedDimension]
  ring

theorem fixedTwoPointParameterization_kernelDimension (n : ℕ) :
    (quasiLineProfile n).predictedTwoMarkedHZero = 1 := by
  exact (quasiLineProfile_cohomology n).2.2.1

end LeBrunSalamon.PhaseThirtyThree

/-!
# Phase 34 -- the normalization/evaluation linear-algebra lemma

The normalization sequence on a nodal union identifies sections with pairs having the same value at the
node. This phase proves neither that normalization sequence nor H1 vanishing: it isolates the exact linear
algebra to apply AFTER those geometric results have been supplied.
-/

namespace LeBrunSalamon.PhaseThirtyFour

section Matching

variable {V₁ V₂ N W₁ W₂ : Type*}
variable [AddCommGroup V₁] [Module ℂ V₁]
variable [AddCommGroup V₂] [Module ℂ V₂]
variable [AddCommGroup N] [Module ℂ N]
variable [AddCommGroup W₁] [Module ℂ W₁]
variable [AddCommGroup W₂] [Module ℂ W₂]

/-- Sections on two components match at the node. -/
def matchingSections (e₁ : V₁ →ₗ[ℂ] N) (e₂ : V₂ →ₗ[ℂ] N) :
    Submodule ℂ (V₁ × V₂) where
  carrier := {v | e₁ v.1 = e₂ v.2}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change e₁ (v.1 + w.1) = e₂ (v.2 + w.2)
    simp only [map_add]
    exact congrArg₂ (· + ·) hv hw
  smul_mem' := by
    intro c v hv
    change e₁ (c • v.1) = e₂ (c • v.2)
    simp only [map_smul]
    exact congrArg (c • ·) hv

def matchingEndpointMap (e₁ : V₁ →ₗ[ℂ] N) (e₂ : V₂ →ₗ[ℂ] N)
    (q₁ : V₁ →ₗ[ℂ] W₁) (q₂ : V₂ →ₗ[ℂ] W₂) :
    matchingSections e₁ e₂ →ₗ[ℂ] (W₁ × W₂) where
  toFun v := (q₁ v.val.1, q₂ v.val.2)
  map_add' := by intro v w; ext <;> simp
  map_smul' := by intro c v; ext <;> simp

/-- Node values obtainable while the outer endpoint is held fixed. -/
def endpointFixedNodeValues (e : V₁ →ₗ[ℂ] N) (q : V₁ →ₗ[ℂ] W₁) :
    Submodule ℂ N := Submodule.map e (LinearMap.ker q)

theorem normalization_sectionDimension
    [FiniteDimensional ℂ V₁] [FiniteDimensional ℂ V₂]
    [FiniteDimensional ℂ N]
    (e₁ : V₁ →ₗ[ℂ] N) (e₂ : V₂ →ₗ[ℂ] N)
    (he₁ : Function.Surjective e₁) :
    Module.finrank ℂ (matchingSections e₁ e₂) + Module.finrank ℂ N =
      Module.finrank ℂ V₁ + Module.finrank ℂ V₂ := by
  let d : (V₁ × V₂) →ₗ[ℂ] N :=
    e₁.comp (LinearMap.fst ℂ V₁ V₂) - e₂.comp (LinearMap.snd ℂ V₁ V₂)
  have hd : Function.Surjective d := by
    intro n
    obtain ⟨v, hv⟩ := he₁ n
    refine ⟨(v, 0), ?_⟩
    simpa [d] using hv
  have hk : LinearMap.ker d = matchingSections e₁ e₂ := by
    ext v
    change e₁ v.1 - e₂ v.2 = 0 ↔ e₁ v.1 = e₂ v.2
    exact sub_eq_zero
  have h := d.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hd, finrank_top, hk, Module.finrank_prod] at h
  omega

/-- This is the evaluation-cokernel computation used by smoothing: the obstruction is the node quotient by
the two positive subspaces. Surjectivity of the two endpoint maps is essential. -/
theorem matchingEndpoint_cokernel
    (e₁ : V₁ →ₗ[ℂ] N) (e₂ : V₂ →ₗ[ℂ] N)
    (q₁ : V₁ →ₗ[ℂ] W₁) (q₂ : V₂ →ₗ[ℂ] W₂)
    (he₁ : Function.Surjective e₁)
    (hq₁ : Function.Surjective q₁) (hq₂ : Function.Surjective q₂) :
    Nonempty (((W₁ × W₂) ⧸ LinearMap.range (matchingEndpointMap e₁ e₂ q₁ q₂)) ≃ₗ[ℂ]
      (N ⧸ (endpointFixedNodeValues e₁ q₁ ⊔ endpointFixedNodeValues e₂ q₂))) := by
  obtain ⟨r₁, hr₁⟩ := q₁.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq₁)
  obtain ⟨r₂, hr₂⟩ := q₂.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq₂)
  have h₁ (w : W₁) : q₁ (r₁ w) = w := LinearMap.congr_fun hr₁ w
  have h₂ (w : W₂) : q₂ (r₂ w) = w := LinearMap.congr_fun hr₂ w
  let S := endpointFixedNodeValues e₁ q₁ ⊔ endpointFixedNodeValues e₂ q₂
  let d : (W₁ × W₂) →ₗ[ℂ] N :=
    (e₁.comp r₁).comp (LinearMap.fst ℂ W₁ W₂) -
      (e₂.comp r₂).comp (LinearMap.snd ℂ W₁ W₂)
  let delta : (W₁ × W₂) →ₗ[ℂ] (N ⧸ S) := S.mkQ.comp d
  have hd (x : V₁) (y : V₂) :
      delta (q₁ x, q₂ y) = S.mkQ (e₁ x - e₂ y) := by
    change S.mkQ (e₁ (r₁ (q₁ x)) - e₂ (r₂ (q₂ y))) = S.mkQ (e₁ x - e₂ y)
    apply (Submodule.Quotient.eq S).mpr
    have hx : e₁ (r₁ (q₁ x) - x) ∈ endpointFixedNodeValues e₁ q₁ := by
      refine ⟨r₁ (q₁ x) - x, ?_, rfl⟩
      change q₁ (r₁ (q₁ x) - x) = 0
      simp only [map_sub, h₁, sub_self]
    have hy : e₂ (r₂ (q₂ y) - y) ∈ endpointFixedNodeValues e₂ q₂ := by
      refine ⟨r₂ (q₂ y) - y, ?_, rfl⟩
      change q₂ (r₂ (q₂ y) - y) = 0
      simp only [map_sub, h₂, sub_self]
    convert Submodule.sub_mem_sup hx hy using 1 <;> simp only [map_sub] <;> abel
  have hsurj : Function.Surjective delta := by
    intro w
    obtain ⟨n, rfl⟩ := S.mkQ_surjective w
    obtain ⟨x, hx⟩ := he₁ n
    refine ⟨(q₁ x, q₂ 0), ?_⟩
    rw [hd, hx, map_zero, sub_zero]
  have hker : LinearMap.ker delta = LinearMap.range (matchingEndpointMap e₁ e₂ q₁ q₂) := by
    ext w
    constructor
    · intro hw
      change S.mkQ (e₁ (r₁ w.1) - e₂ (r₂ w.2)) = 0 at hw
      have hs : e₁ (r₁ w.1) - e₂ (r₂ w.2) ∈ S := (Submodule.Quotient.mk_eq_zero S).mp hw
      obtain ⟨m, hm, n, hn, hmn⟩ := Submodule.mem_sup.mp hs
      obtain ⟨u, hu, rfl⟩ := hm
      obtain ⟨v, hv, rfl⟩ := hn
      have hu0 : q₁ u = 0 := hu
      have hv0 : q₂ v = 0 := hv
      refine ⟨⟨(r₁ w.1 - u, r₂ w.2 + v), ?_⟩, ?_⟩
      · change e₁ (r₁ w.1 - u) = e₂ (r₂ w.2 + v)
        rw [map_sub, map_add]
        apply sub_eq_zero.mp
        calc
          (e₁ (r₁ w.1) - e₁ u) - (e₂ (r₂ w.2) + e₂ v) =
            (e₁ (r₁ w.1) - e₂ (r₂ w.2)) - (e₁ u + e₂ v) := by abel
          _ = 0 := sub_eq_zero.mpr hmn.symm
      · apply Prod.ext
        · change q₁ (r₁ w.1 - u) = w.1
          simp only [map_sub, h₁, hu0, sub_zero]
        · change q₂ (r₂ w.2 + v) = w.2
          simp only [map_add, h₂, hv0, add_zero]
    · rintro ⟨v, rfl⟩
      change delta (q₁ v.val.1, q₂ v.val.2) = 0
      rw [hd, v.property, sub_self, map_zero]
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans
    (delta.quotKerEquivOfSurjective hsurj)⟩

theorem matchingEndpoint_surjective_iff
    (e₁ : V₁ →ₗ[ℂ] N) (e₂ : V₂ →ₗ[ℂ] N)
    (q₁ : V₁ →ₗ[ℂ] W₁) (q₂ : V₂ →ₗ[ℂ] W₂)
    (he₁ : Function.Surjective e₁)
    (hq₁ : Function.Surjective q₁) (hq₂ : Function.Surjective q₂) :
    Function.Surjective (matchingEndpointMap e₁ e₂ q₁ q₂) ↔
      endpointFixedNodeValues e₁ q₁ ⊔ endpointFixedNodeValues e₂ q₂ = ⊤ := by
  obtain ⟨e⟩ := matchingEndpoint_cokernel e₁ e₂ q₁ q₂ he₁ hq₁ hq₂
  rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff,
    ← Submodule.Quotient.subsingleton_iff]
  exact e.toEquiv.subsingleton_congr

theorem matchingEndpoint_defectDimension
    [FiniteDimensional ℂ N] [FiniteDimensional ℂ W₁] [FiniteDimensional ℂ W₂]
    (e₁ : V₁ →ₗ[ℂ] N) (e₂ : V₂ →ₗ[ℂ] N)
    (q₁ : V₁ →ₗ[ℂ] W₁) (q₂ : V₂ →ₗ[ℂ] W₂)
    (he₁ : Function.Surjective e₁)
    (hq₁ : Function.Surjective q₁) (hq₂ : Function.Surjective q₂) :
    Module.finrank ℂ ((W₁ × W₂) ⧸ LinearMap.range (matchingEndpointMap e₁ e₂ q₁ q₂)) =
      Module.finrank ℂ (N ⧸
        (endpointFixedNodeValues e₁ q₁ ⊔ endpointFixedNodeValues e₂ q₂)) := by
  obtain ⟨e⟩ := matchingEndpoint_cokernel e₁ e₂ q₁ q₂ he₁ hq₁ hq₂
  exact e.finrank_eq

end Matching

section FirstOrderNode

open LeBrunSalamon.PhaseTwentyNine

abbrev NodeJetRing := MvPolynomial (Fin 2) ℂ

def nodeInfinitesimalIdeal : Ideal NodeJetRing :=
  Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1) ^ 2}

abbrev FirstOrderSmoothingNode := NodeJetRing ⧸ nodeInfinitesimalIdeal

def firstOrderParameter : FirstOrderSmoothingNode :=
  Ideal.Quotient.mk nodeInfinitesimalIdeal
    (MvPolynomial.X 0 * MvPolynomial.X 1)

theorem firstOrderParameter_square : firstOrderParameter ^ 2 = 0 := by
  rw [firstOrderParameter, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

theorem firstOrderParameter_nonzero : firstOrderParameter ≠ 0 := by
  let a : NodeJetRing := MvPolynomial.X 0 * MvPolynomial.X 1
  have ha : a ≠ 0 := mul_ne_zero (MvPolynomial.X_ne_zero 0) (MvPolynomial.X_ne_zero 1)
  intro h
  have hd : a ^ 2 ∣ a := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hunit : a ∣ (1 : NodeJetRing) :=
    (mul_dvd_mul_iff_left ha).mp (by simpa only [pow_two, mul_one] using hd)
  obtain ⟨r, hr⟩ := hunit
  have hc := congrArg MvPolynomial.constantCoeff hr
  simp [a] at hc

/-- Ann(epsilon)=(epsilon) in C[u,v]/((uv)^2). -/
theorem firstOrderParameter_annihilator (z : FirstOrderSmoothingNode) :
    firstOrderParameter * z = 0 ↔
      ∃ q : FirstOrderSmoothingNode, z = firstOrderParameter * q := by
  let a : NodeJetRing := MvPolynomial.X 0 * MvPolynomial.X 1
  have ha : a ≠ 0 := mul_ne_zero (MvPolynomial.X_ne_zero 0) (MvPolynomial.X_ne_zero 1)
  constructor
  · intro hz
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hm : a * f ∈ nodeInfinitesimalIdeal := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_mul, firstOrderParameter, a] using hz
    have hd : a ^ 2 ∣ a * f := Ideal.mem_span_singleton.mp hm
    have hf : a ∣ f := (mul_dvd_mul_iff_left ha).mp (by simpa only [pow_two] using hd)
    obtain ⟨q, hq⟩ := hf
    refine ⟨Ideal.Quotient.mk nodeInfinitesimalIdeal q, ?_⟩
    change Ideal.Quotient.mk nodeInfinitesimalIdeal f =
      Ideal.Quotient.mk nodeInfinitesimalIdeal a * Ideal.Quotient.mk nodeInfinitesimalIdeal q
    rw [hq, map_mul]
  · rintro ⟨q, rfl⟩
    rw [← mul_assoc, ← pow_two, firstOrderParameter_square, zero_mul]

/-- The common constant in the two branch expansions is independent
of the choice of a lift of the epsilon coefficient. -/
theorem firstOrderNode_sharedConstant (F G : NodeJetRing)
    (h : firstOrderParameter * Ideal.Quotient.mk nodeInfinitesimalIdeal F =
      firstOrderParameter * Ideal.Quotient.mk nodeInfinitesimalIdeal G) :
    MvPolynomial.constantCoeff F = MvPolynomial.constantCoeff G := by
  let a : NodeJetRing := MvPolynomial.X 0 * MvPolynomial.X 1
  have ha : a ≠ 0 := mul_ne_zero (MvPolynomial.X_ne_zero 0) (MvPolynomial.X_ne_zero 1)
  have he : Ideal.Quotient.mk nodeInfinitesimalIdeal (a * F) =
      Ideal.Quotient.mk nodeInfinitesimalIdeal (a * G) := by
    simpa only [map_mul, firstOrderParameter, a] using h
  have hd : a ^ 2 ∣ a * (F - G) := by
    simpa only [mul_sub] using Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  have hfg : a ∣ F - G :=
    (mul_dvd_mul_iff_left ha).mp (by simpa only [pow_two] using hd)
  obtain ⟨r, hr⟩ := hfg
  have hc := congrArg MvPolynomial.constantCoeff hr
  have hz : MvPolynomial.constantCoeff F - MvPolynomial.constantCoeff G = 0 := by
    simpa [a] using hc
  exact sub_eq_zero.mp hz

end FirstOrderNode

end LeBrunSalamon.PhaseThirtyFour

/-! Completed local algebra for sm:shared-constant. Identifying this ring with the
completed local ring of a geometric deformation germ remains a separate obligation. -/
namespace LeBrunSalamon.Construction.Smoothing.FormalNode
/-- The two-variable completed coefficient ring used in sm:shared-constant. -/
abbrev NodeSeriesRing := MvPowerSeries (Fin 2) ℂ

theorem coordinate_ne_zero (i : Fin 2) :
    (MvPowerSeries.X i : NodeSeriesRing) ≠ 0 := by
  intro h
  have hc := congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) h
  simpa using hc

def firstOrderIdeal : Ideal NodeSeriesRing :=
  Ideal.span {(MvPowerSeries.X 0 * MvPowerSeries.X 1) ^ 2}
abbrev FirstOrderNode := NodeSeriesRing ⧸ firstOrderIdeal

def epsilon : FirstOrderNode :=
  Ideal.Quotient.mk firstOrderIdeal
    (MvPowerSeries.X 0 * MvPowerSeries.X 1)

theorem epsilon_square : epsilon ^ 2 = 0 := by
  rw [epsilon, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

theorem epsilon_nonzero : epsilon ≠ 0 := by
  let a : NodeSeriesRing := MvPowerSeries.X 0 * MvPowerSeries.X 1
  have ha : a ≠ 0 := mul_ne_zero (coordinate_ne_zero 0) (coordinate_ne_zero 1)
  intro h
  have hd : a ^ 2 ∣ a := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hunit : a ∣ (1 : NodeSeriesRing) :=
    (mul_dvd_mul_iff_left ha).mp (by simpa only [pow_two, mul_one] using hd)
  obtain ⟨r, hr⟩ := hunit
  have hc := congrArg MvPowerSeries.constantCoeff hr
  simp [a] at hc

theorem epsilon_annihilator (z : FirstOrderNode) :
    epsilon * z = 0 ↔
      ∃ q : FirstOrderNode, z = epsilon * q := by
  let a : NodeSeriesRing := MvPowerSeries.X 0 * MvPowerSeries.X 1
  have ha : a ≠ 0 := mul_ne_zero (coordinate_ne_zero 0) (coordinate_ne_zero 1)
  constructor
  · intro hz
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hm : a * f ∈ firstOrderIdeal := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_mul, epsilon, a] using hz
    have hd : a ^ 2 ∣ a * f := Ideal.mem_span_singleton.mp hm
    have hf : a ∣ f := (mul_dvd_mul_iff_left ha).mp (by simpa only [pow_two] using hd)
    obtain ⟨q, hq⟩ := hf
    refine ⟨Ideal.Quotient.mk firstOrderIdeal q, ?_⟩
    change Ideal.Quotient.mk firstOrderIdeal f =
      Ideal.Quotient.mk firstOrderIdeal a * Ideal.Quotient.mk firstOrderIdeal q
    rw [hq, map_mul]
  · rintro ⟨q, rfl⟩
    rw [← mul_assoc, ← pow_two, epsilon_square, zero_mul]

theorem sharedConstant (F G : NodeSeriesRing)
    (h : epsilon * Ideal.Quotient.mk firstOrderIdeal F =
      epsilon * Ideal.Quotient.mk firstOrderIdeal G) :
    MvPowerSeries.constantCoeff F = MvPowerSeries.constantCoeff G := by
  let a : NodeSeriesRing := MvPowerSeries.X 0 * MvPowerSeries.X 1
  have ha : a ≠ 0 := mul_ne_zero (coordinate_ne_zero 0) (coordinate_ne_zero 1)
  have he : Ideal.Quotient.mk firstOrderIdeal (a * F) =
      Ideal.Quotient.mk firstOrderIdeal (a * G) := by
    simpa only [map_mul, epsilon, a] using h
  have hd : a ^ 2 ∣ a * (F - G) := by
    simpa only [mul_sub] using Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  have hfg : a ∣ F - G :=
    (mul_dvd_mul_iff_left ha).mp (by simpa only [pow_two] using hd)
  obtain ⟨r, hr⟩ := hfg
  have hc := congrArg MvPowerSeries.constantCoeff hr
  have hz : MvPowerSeries.constantCoeff F - MvPowerSeries.constantCoeff G = 0 := by
    simpa [a] using hc
  exact sub_eq_zero.mp hz

/-- For vector-valued target coordinates, every regular branch constant agrees. -/
theorem vector_sharedConstant {ι : Type*} (F G : ι → NodeSeriesRing)
    (h : ∀ i, epsilon * Ideal.Quotient.mk firstOrderIdeal (F i) =
      epsilon * Ideal.Quotient.mk firstOrderIdeal (G i)) :
    (fun i => MvPowerSeries.constantCoeff (F i)) =
      (fun i => MvPowerSeries.constantCoeff (G i)) := by
  funext i
  exact sharedConstant (F i) (G i) (h i)

end LeBrunSalamon.Construction.Smoothing.FormalNode


/-!
# Phase 35 -- migration from candidates to intrinsic proof obligations

These statements connect the old interfaces to the new intrinsic objects. A theorem with suffix `_target`
is a major PROJECT CLAIM, not a classical library lemma and not a completed proof. Nothing in this phase
turns a list of `sorry` declarations into a proof certificate.
-/

namespace LeBrunSalamon.SchemeStandardInputs

/-- Published input: a scheme smooth over a field is reduced.
This is the complex-base specialization of Stacks Project, Lemma 33.25.4,
Tag 056T. Only this standard result is admitted; all uses of it below
must supply the actual smooth structure morphism. -/
theorem smooth_complex_reduced {Y : Scheme}
    (s : Y ⟶ LeBrunSalamon.PhaseOne.ComplexBase) [Smooth s] :
    AlgebraicGeometry.IsReduced Y := by sorry

end LeBrunSalamon.SchemeStandardInputs

namespace LeBrunSalamon.PhaseThirtyFive

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseFour
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTen
open LeBrunSalamon.PhaseEighteen LeBrunSalamon.PhaseTwentyOne
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyTwo

/-- The old interface with its formerly arbitrary tangent and contact
data now instantiated by the universal cotangent construction. -/
def intrinsicAsCandidate {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) : ContactCandidate n :=
  ⟨X, intrinsicTangentBundle X, C.sequence⟩

def intrinsicHamiltonianSectionField {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X)
    (s : AlgebraicSection C.sequence.line.sheaf) :
    AlgebraicSection (tangentSheaf X.structureMap) :=
  sectionFromValue (intrinsicHamiltonianField X C (sectionValue s)).val

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTen
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight

namespace IntrinsicConsequenceProof

theorem intrinsicHamiltonianSectionField_rightInverse {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X)
    (s : AlgebraicSection C.sequence.line.sheaf) :
    intrinsicHamiltonianSectionField X C s ≫ C.sequence.form = s := by
  apply (sectionValue_bijective C.sequence.line.sheaf).injective
  simp only [intrinsicHamiltonianSectionField, sectionValue_comp, sectionFromValue_spec]
  change intrinsicHamiltonian C
    ((intrinsicHamiltonianEquiv X C).symm (sectionValue s)) = sectionValue s
  exact (intrinsicHamiltonianEquiv X C).apply_symm_apply (sectionValue s)

end IntrinsicConsequenceProof

end

theorem intrinsicHamiltonianSectionField_rightInverse {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X)
    (s : AlgebraicSection C.sequence.line.sheaf) :
    intrinsicHamiltonianSectionField X C s ≫ C.sequence.form = s := by
  exact LeBrunSalamon.PhaseThirtyFive.IntrinsicConsequenceProof.intrinsicHamiltonianSectionField_rightInverse (n := n) (X := X) (C := C) (s := s)

namespace IntrinsicJetAffineQuotientProof

/-- The actual scheme-theoretic fat point has exactly the expected affine kernel power. -/
theorem pointPower_kernel_on_affine {d : ℕ}
    {X : SmoothProperComplexVariety d} (x : ComplexPoint X)
    (U : X.scheme.Opens) (hU : IsAffineOpen U) (k : ℕ) :
    RingHom.ker ((pointPowerInclusion x k).app U).hom =
      (RingHom.ker (x.map.app U).hom) ^ k := by
  letI : IsClosedImmersion x.map :=
    FatPointOpenFactorizationProof.complexPoint_isClosedImmersion x
  change RingHom.ker (((x.map.ker ^ k).subschemeι).app U).hom = _
  rw [(x.map.ker ^ k).ker_subschemeι_app ⟨U, hU⟩]
  change (x.map.ker.ideal ⟨U, hU⟩) ^ k = _
  rw [x.map.ker_apply ⟨U, hU⟩]

/-- Every function on the actual affine piece of the fat point lifts to its ambient affine open. -/
theorem pointPower_affine_restriction_surjective {d : ℕ}
    {X : SmoothProperComplexVariety d} (x : ComplexPoint X)
    (U : X.scheme.Opens) (hU : IsAffineOpen U) (k : ℕ) :
    Function.Surjective ((pointPowerInclusion x k).app U).hom := by
  exact (x.map.ker ^ k).subschemeι_app_surjective ⟨U, hU⟩

/-- Normalized coordinate ring of the actual fat-point open, not an abstract jet-algebra label. -/
def pointPowerQuotientEquiv {d : ℕ}
    {X : SmoothProperComplexVariety d} (x : ComplexPoint X)
    (U : X.scheme.Opens) (hU : IsAffineOpen U) (k : ℕ) :
    (RingSections X.scheme U ⧸ (RingHom.ker (x.map.app U).hom) ^ k) ≃+*
      RingSections (pointPowerSubscheme x k) ((pointPowerInclusion x k) ⁻¹ᵁ U) :=
  (Ideal.quotEquivOfEq (pointPower_kernel_on_affine x U hU k).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := ((pointPowerInclusion x k).app U).hom)
      (pointPower_affine_restriction_surjective x U hU k))

/-- The quotient equivalence fixes restriction of every ambient local function. -/
theorem pointPowerQuotientEquiv_mk {d : ℕ}
    {X : SmoothProperComplexVariety d} (x : ComplexPoint X)
    (U : X.scheme.Opens) (hU : IsAffineOpen U) (k : ℕ)
    (a : RingSections X.scheme U) :
    pointPowerQuotientEquiv x U hU k
        (Ideal.Quotient.mk ((RingHom.ker (x.map.app U).hom) ^ k) a) =
      ((pointPowerInclusion x k).app U).hom a := by
  simp only [pointPowerQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- Equality after actual fat-point restriction is exactly membership in the affine kernel power. -/
theorem pointPower_restriction_eq_iff {d : ℕ}
    {X : SmoothProperComplexVariety d} (x : ComplexPoint X)
    (U : X.scheme.Opens) (hU : IsAffineOpen U) (k : ℕ)
    (a b : RingSections X.scheme U) :
    ((pointPowerInclusion x k).app U).hom a =
        ((pointPowerInclusion x k).app U).hom b ↔
      a - b ∈ (RingHom.ker (x.map.app U).hom) ^ k := by
  rw [← pointPowerQuotientEquiv_mk x U hU k a,
    ← pointPowerQuotientEquiv_mk x U hU k b,
    (pointPowerQuotientEquiv x U hU k).injective.eq_iff]
  exact Ideal.Quotient.eq

end IntrinsicJetAffineQuotientProof

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTen
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight

namespace IntrinsicConsequenceProof

end IntrinsicConsequenceProof

end

/-- Projectivity follows from the genuine anticanonical ampleness.
It is not conflated with properness in the definition. -/
theorem _root_.LeBrunSalamon.PublishedInputs.Step3e.ampleLine_hasProjectiveEmbedding
    {d : ℕ} (X : SmoothProperComplexVariety d) (L : LineBundle X.scheme)
    (hL : IsAmpleLine L) : HasProjectiveEmbedding X := by
  obtain ⟨N, i, hi, hs⟩ :=
    LeBrunSalamon.PublishedInputs.ProjectiveSpace.properAmpleClosedImmersion ℂ
      ⟨trivialLine ComplexBase,
        LeBrunSalamon.ProjectiveQuotient.trivialLine_ample ComplexBase⟩
      X.structureMap ⟨L, hL⟩
  refine ⟨{ dimension := N
            zeroDegreeIso := LeBrunSalamon.Skeleton.zeroDegreeSchemeIso N
            embedding := i
            isClosed := hi
            overComplexBase := ?_ }⟩
  simpa only [LeBrunSalamon.ProjectiveQuotient.toSpec,
    LeBrunSalamon.ProjectiveQuotient.constants_complex,
    LeBrunSalamon.Skeleton.zeroDegreeSchemeIso] using hs

/-- Projectivity of a contact Fano manifold follows from the published
projective-embedding theorem for an ample invertible sheaf, applied to its
anticanonical line. -/
theorem contactFano_hasProjectiveEmbedding {n : ℕ}
    (X : ContactFanoManifold n) : HasProjectiveEmbedding X.variety := by
  exact LeBrunSalamon.PublishedInputs.Step3e.ampleLine_hasProjectiveEmbedding
    X.variety (anticanonicalLine X.variety) X.fano

/- Exact header relocated to LSHamiltonianJets; ordinary wrapper still uses the original admitted first-jet target. -/

/-- Actual pullback bundle, not just an integer splitting profile. -/
def pullbackBundle {X Y : Scheme} (f : X ⟶ Y) {r : ℕ}
    (E : AlgebraicVectorBundle Y r) : AlgebraicVectorBundle X r :=
  ⟨pullbackModule f E.sheaf, pullback_locallyFree f E.locallyFree⟩

/- Exact declaration relocated to LSConicSplitting; see owners/root/CONIC_RELOCATION_RECORD.json. -/

/- Exact declaration relocated to LSConicSplitting; see owners/root/CONIC_RELOCATION_RECORD.json. -/

/- The exact original primitiveContactFano_veryFreeConic_target header
is relocated to LSSmoothingAssembly. Its ordinary assembly uses the
individual suitable-pair, fixed-end, and conic-extraction theorems and
actual source transport; remaining geometric obligations stay visible. -/

/-- Moving-pair lifts with ALL three bundles and quotient maps fixed by the actual intrinsic contact
structure. There are no arbitrary E12, E21, or M parameters in this stronger interface. -/
structure IntrinsicMovingPair {n : ℕ} (X : ContactFanoManifold n) where
  data : MovingPairContactValue X.variety
    (movingPairBundleLeft X.variety X.contact)
    (movingPairBundleRight X.variety X.contact)
    (externalSquareLine X.variety.structureMap X.contact.sequence.line).sheaf
  mapLeft : data.map12 = movingPairContactLeft X.variety X.contact
  mapRight : data.map21 = movingPairContactRight X.variety X.contact

/-- Extra f_*O=O hypotheses suffice for descent by projection formula. The stronger proposed contact-value
descent theorem has to establish its own existence mechanism; proper dominance alone is NOT used here. -/
theorem intrinsicMovingPair_descends_of_structureSheafDescent
    {n : ℕ} (X : ContactFanoManifold n) (D : IntrinsicMovingPair X)
    (h : HasStructureSheafDescent D.data.projection) :
    D.data.AdmitsDescent := by
  let L := externalSquareLine X.variety.structureMap X.contact.sequence.line
  let v : AlgebraicSection (pullbackModule D.data.projection L.sheaf) :=
    (unitPullbackIso D.data.projection).inv ≫ D.data.value
  obtain ⟨B, hB⟩ := (locallyFree_sections_descend D.data.projection h L).surjective v
  refine ⟨B, ?_⟩
  apply (cancel_epi (unitPullbackIso D.data.projection).inv).mp
  exact hB


theorem intrinsicMovingPair_descent_unique {n : ℕ}
    (X : ContactFanoManifold n) (D : IntrinsicMovingPair X)
    (B C : AlgebraicSection
      (externalSquareLine X.variety.structureMap X.contact.sequence.line).sheaf)
    (hB : restrictSection D.data.projection B = D.data.value)
    (hC : restrictSection D.data.projection C = D.data.value) :
    B = C := by
  let s := X.variety.structureMap
  letI : Smooth (firstProjection s ≫ s) := inferInstance
  letI : AlgebraicGeometry.IsReduced (SelfProduct s) :=
    LeBrunSalamon.SchemeStandardInputs.smooth_complex_reduced
      (firstProjection s ≫ s)
  apply dominant_pullSection_injective D.data.projection D.data.dominant
    (fun U => inferInstance)
    (externalSquareLine X.variety.structureMap X.contact.sequence.line)
  exact congrArg
    (fun v => (unitPullbackIso D.data.projection).inv ≫ v)
    (hB.trans hC.symm)


/-- Uniqueness of the normalized swap action on proper varieties,
using the finite-sum decomposition of external-product sections. -/
theorem externalExchange_independent_on_proper {d : ℕ}
    (X : SmoothProperComplexVariety d) (L : LineBundle X.scheme)
    (e f : InvolutiveExternalExchange X.structureMap L)
    (B : AlgebraicSection (externalSquareLine X.structureMap L).sheaf) :
    e.identification.swapSection B = f.identification.swapSection B := by
  obtain ⟨N, a, b, hB⟩ := externalSection_finiteSum X L L B
  let eAdd := LeBrunSalamon.PhaseTwentyEight.ExchangeAlgebraProof.swapSectionAddHom
    e.identification
  let fAdd := LeBrunSalamon.PhaseTwentyEight.ExchangeAlgebraProof.swapSectionAddHom
    f.identification
  calc
    _ = ∑ i : Fin N, e.identification.swapSection
        (externalProductSection X.structureMap (a i) (b i)) := by
      rw [hB]
      exact map_sum eAdd _ _
    _ = ∑ i : Fin N, f.identification.swapSection
        (externalProductSection X.structureMap (a i) (b i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (e.onProducts (a i) (b i)).trans (f.onProducts (a i) (b i)).symm
    _ = _ := by
      rw [hB]
      exact (map_sum fAdd _ _).symm


end LeBrunSalamon.PhaseThirtyFive

/- The generic affine derivation inputs are imported from LSAffineDerivations. -/

/-!
# Project core -- normalized kernels and the algebraic proof route

Core provides the normalized-kernel interface; the preferred end-to-end entry is
Refinement.leBrunSalamon_project. No kernel contract includes first-jet generation,
immersion, transitivity or classification. The constructions must be proved.

On an affine line frame write B=sum_i f_i boxtimes g_i. Once the value and first
symbol vanish, the UNDIVIDED second-slot Hessian is sum_i f_i*u(v(g_i)).
The manuscript's coefficient convention [B]_2=theta^2 therefore means exactly
H_B(u,v)=2*theta(u)*theta(v). The factor 2 and mixed-Hessian minus sign are essential.
The equation is tested on every affine frame and every intrinsic local field;
it does not rely on an arbitrary identification of equal-rank bundles.
Frame/decomposition independence and the ideal-adic comparison are separate
foundational obligations. Refinement.Jets connects these data to actual first
jets and actual finite global contractions without a basis of H^0(L).
-/

namespace LeBrunSalamon.Core

open LeBrunSalamon.PhaseSeven

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseTen
open LeBrunSalamon.PhaseFourteen LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFive

/-! ## A. Affine frames and finite external expansions -/

/-- A genuine frame on an AFFINE open. On an affine open, a linear isomorphism of the section module of a
locally free sheaf is a sheaf trivialization. Affineness is essential: a vector-space isomorphism H^0(L)
~= H^0(O) on an arbitrary proper open would not suffice. -/
structure AffineLineFrame {X : Scheme} (L : LineBundle X) where
  openSet : X.Opens
  isAffine : IsAffineOpen openSet
  coefficient : SectionsOn L.sheaf openSet ≃ₗ[RingSections X openSet]
    RingSections X openSet

/-- The scalar coefficient of a global section in this local frame. The sheaf morphism is evaluated on 1
on the specified OPEN, not just on global functions on the projective variety. -/
def AffineLineFrame.localCoefficient {X : Scheme} {L : LineBundle X}
    (F : AffineLineFrame L) (a : AlgebraicSection L.sheaf) :
    RingSections X F.openSet :=
  F.coefficient (Scheme.Modules.Hom.app a F.openSet (1 : RingSections X F.openSet))

/-- Local freeness supplies enough affine frames. This is a construction
obligation, not a hypothesis smuggled into normalized-kernel data. -/
theorem affineLineFrames_cover {X : Scheme} (L : LineBundle X) (x : X) :
    ∃ F : AffineLineFrame L, x ∈ F.openSet := by
  classical
  obtain ⟨q, hq, hr⟩ := L.locallyFree
  letI := hq
  obtain ⟨i, hxi⟩ :=
    ((_root_.Opens.coversTop_iff X q.X).mp q.coversTop).exists_mem x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUi⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxi (q.X i).isOpen
  let e : L.sheaf.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
    (SheafTensor.freeTrivializationRestrict (homOfLE hUi)
      (SheafTensor.localBasisTrivialization q hr i)).symm ≪≫
    coproductUniqueIso (fun _ : Fin 1 => SheafOfModules.unit (X.ringCatSheaf.over U))
  let eΓ := ((SheafOfModules.evaluation (X.ringCatSheaf.over U)
    (Opposite.op (Over.mk (𝟙 U)))).mapIso e).toLinearEquiv
  exact ⟨⟨U, hU, eΓ⟩, hxU⟩


/-- On one affine open any two line frames differ by a UNIQUE unit.
Writing the maps separately avoids transport across equality of opens. -/
theorem affineLineFrame_change_isUnit {X : Scheme} (L : LineBundle X)
    (U : X.Opens) (hU : IsAffineOpen U)
    (e f : SectionsOn L.sheaf U ≃ₗ[RingSections X U] RingSections X U) :
    ∃! q : (RingSections X U)ˣ,
      ∀ a : SectionsOn L.sheaf U, f a = (q : RingSections X U) * e a := by
  let g : RingSections X U ≃ₗ[RingSections X U] RingSections X U := e.symm.trans f
  have hg (a : RingSections X U) : g a = a * g 1 := by
    simpa only [smul_eq_mul, mul_one] using g.map_smul a (1 : RingSections X U)
  have hinv : g 1 * g.symm 1 = 1 := by
    rw [mul_comm, ← hg, g.apply_symm_apply]
  let q : (RingSections X U)ˣ :=
    ⟨g 1, g.symm 1, hinv, by simpa only [mul_comm] using hinv⟩
  refine ⟨q, ?_, ?_⟩
  · intro a
    calc
      f a = g (e a) := by simp [g]
      _ = (q : RingSections X U) * e a := by
        change g (e a) = g 1 * e a
        rw [hg, mul_comm]
  · intro q' hq'
    apply Units.ext
    have h := hq' (e.symm 1)
    simpa [q, g] using h.symm


/-- The actual space of global sections of the actual external square. -/
abbrev ExternalSquareSections {d : ℕ}
    (X : SmoothProperComplexVariety d) (L : LineBundle X.scheme) :=
  AlgebraicSection (externalSquareLine X.structureMap L).sheaf

/-- A finite tensor expansion of one FIXED global two-point section.
Neither the left nor the right family is assumed linearly independent.
It is not permissible to replace `equation` by an equality of dimensions. -/
structure ExternalExpansion {d : ℕ} (X : SmoothProperComplexVariety d)
    (L : LineBundle X.scheme) (B : ExternalSquareSections X L) where
  size : ℕ
  left : Fin size → AlgebraicSection L.sheaf
  right : Fin size → AlgebraicSection L.sheaf
  equation : B = ∑ i, externalProductSection X.structureMap (left i) (right i)

/-- Source: the finite tensor decomposition in the proof of `jet:criterion`. The proof below is just the
interface conversion; degree-zero Kunneth is the already explicit foundational admission in Phase 28. -/
theorem externalExpansion_exists {d : ℕ}
    (X : SmoothProperComplexVariety d) (L : LineBundle X.scheme)
    (B : ExternalSquareSections X L) : Nonempty (ExternalExpansion X L B) := by
  obtain ⟨N, a, b, h⟩ := externalSection_finiteSum X L L B
  exact ⟨⟨N, a, b, h⟩⟩

/-! Canonical complex-linear section tensors. The scalar structures are
induced by the supplied structure morphism and retain the actual sections. -/
section ExternalTensorCoordinatesSection

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace ExternalTensorCoordinates

def constants {Y : Scheme} (s : Y ⟶ ComplexBase) (U : Y.Opens) :
    ℂ →+* RingSections Y U :=
  ((Y.presheaf.map (homOfLE le_top).op).hom.comp s.appTop.hom).comp
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom

theorem constants_apply {Y : Scheme} (s : Y ⟶ ComplexBase)
    (U : Y.Opens) (c : ℂ) :
    constants s U c = Y.presheaf.map (homOfLE le_top).op
      (s.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) := rfl

theorem constants_top {Y : Scheme} (s : Y ⟶ ComplexBase) (c : ℂ) :
    constants s ⊤ c = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) := by
  simp [constants]

theorem constants_restrict {Y : Scheme} (s : Y ⟶ ComplexBase)
    {U V : Y.Opens} (i : V ⟶ U) (c : ℂ) :
    Y.presheaf.map i.op (constants s U c) = constants s V c := by
  rw [constants_apply, constants_apply, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp]
  rfl

theorem constants_naturality {Y Z : Scheme} (f : Y ⟶ Z)
    (sY : Y ⟶ ComplexBase) (sZ : Z ⟶ ComplexBase)
    (hf : f ≫ sZ = sY) (c : ℂ) :
    f.appTop (constants sZ ⊤ c) = constants sY ⊤ c := by
  rw [constants_top, constants_top]
  change (sZ.appTop ≫ f.appTop) ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) = _
  rw [← Scheme.Hom.comp_appTop, hf]

/-- Genuine global sections, with scalars induced by the given complex base. -/
def ComplexSections {Y : Scheme} (s : Y ⟶ ComplexBase) (E : OModule Y) : Type _ :=
  GlobalSections E

instance complexSectionsAddCommGroup {Y : Scheme} (s : Y ⟶ ComplexBase)
    (E : OModule Y) : AddCommGroup (ComplexSections s E) :=
  inferInstanceAs (AddCommGroup (GlobalSections E))

instance complexSectionsModule {Y : Scheme} (s : Y ⟶ ComplexBase)
    (E : OModule Y) : Module ℂ (ComplexSections s E) :=
  Module.compHom (GlobalSections E) (constants s ⊤)

/-- The same canonical unit and pullback comparisons as `pullSection`. -/
def pullLinear {Y Z : Scheme} (f : Y ⟶ Z)
    (sY : Y ⟶ ComplexBase) (sZ : Z ⟶ ComplexBase)
    (hf : f ≫ sZ = sY) (E : OModule Z) :
    ComplexSections sZ E →ₗ[ℂ] ComplexSections sY (pullbackModule f E) where
  toFun a := sectionValue (pullSection f (sectionFromValue a))
  map_add' := by
    intro a b
    simp only [pullSection_value, sectionFromValue_spec]
    exact map_add (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E).app ⊤).hom a b
  map_smul' := by
    intro c a
    have h := pullSectionValue_smul f E (constants sZ ⊤ c) a
    rw [constants_naturality f sY sZ hf] at h
    exact h

/-- The actual section pairing of the constructed sheaf tensor product. -/
def tensorLinear {Y : Scheme} (s : Y ⟶ ComplexBase) (E F : OModule Y) :
    ComplexSections s E →ₗ[ℂ] ComplexSections s F →ₗ[ℂ]
      ComplexSections s (tensorSheaf E F) where
  toFun a :=
    { toFun := fun b => (tensorPresentation E F).pair.apply ⊤ a b
      map_add' := by intro b c; exact map_add _ _ _
      map_smul' := by
        intro c b
        exact ((tensorPresentation E F).pair.apply ⊤ a).map_smul (constants s ⊤ c) b }
  map_add' := by
    intro a b
    ext c
    exact congrArg (fun k => k c)
      (((tensorPresentation E F).pair.apply ⊤).map_add a b)
  map_smul' := by
    intro c a
    ext b
    exact congrArg (fun k => k b)
      (((tensorPresentation E F).pair.apply ⊤).map_smul (constants s ⊤ c) a)

def productLinear {Y : Scheme} (s : Y ⟶ ComplexBase) (E F : OModule Y) :
    ComplexSections s E →ₗ[ℂ] ComplexSections s F →ₗ[ℂ]
      ComplexSections (firstProjection s ≫ s) (externalTensor s E F) :=
    (tensorLinear (firstProjection s ≫ s)
      (pullbackModule (firstProjection s) E) (pullbackModule (secondProjection s) F)
      ).compl₁₂
        (pullLinear (firstProjection s) (firstProjection s ≫ s) s rfl E)
        (pullLinear (secondProjection s) (firstProjection s ≫ s) s
          (by exact (pullback.condition (f := s) (g := s)).symm) F)

/-- The canonical external-product map, with its genuine complex scalar structures. -/
def globalTensorMap {Y : Scheme} (s : Y ⟶ ComplexBase) (E F : OModule Y) :
    (ComplexSections s E ⊗[ℂ] ComplexSections s F) →ₗ[ℂ]
      ComplexSections (firstProjection s ≫ s) (externalTensor s E F) :=
  TensorProduct.lift (productLinear s E F)

theorem globalTensorMap_tmul {Y : Scheme} (s : Y ⟶ ComplexBase) (E F : OModule Y)
    (a : ComplexSections s E) (b : ComplexSections s F) :
    globalTensorMap s E F (a ⊗ₜ[ℂ] b) =
      sectionValue (externalProductSection s (sectionFromValue a) (sectionFromValue b)) := by
  rw [globalTensorMap, TensorProduct.lift.tmul]
  simp only [externalProductSection, sectionValue_tensorSection]
  rfl

/-- The original project map is exactly the generic canonical Künneth map,
including the actual scalar structures, pullbacks and tensor pairing. -/
theorem globalTensorMap_eq_kunneth {Y : Scheme} (s : Y ⟶ ComplexBase)
    (E F : OModule Y) :
    globalTensorMap s E F =
      LeBrunSalamon.KunnethDegreeZero.canonicalMap s s E F := by
  rfl

/-- The original injectivity API is proved by specializing the single
generic degree-zero Künneth input (Stacks33.29.1, Tag0BED). The preceding
equality fixes the actual map; no project specialization is admitted. -/
theorem _root_.LeBrunSalamon.PublishedInputs.ExternalTensorDiagonal.kunneth_degreeZero_injective
    {d : ℕ} (X : SmoothProperComplexVariety d) (L M : LineBundle X.scheme) :
    Function.Injective
      (globalTensorMap X.structureMap L.sheaf M.sheaf) := by
  rw [globalTensorMap_eq_kunneth]
  exact (LeBrunSalamon.KunnethDegreeZero.lineMap_bijective X L M).injective

/-- Project API wrapper for degree-zero Künneth injectivity. -/
theorem globalTensorMap_injective {d : ℕ}
    (X : SmoothProperComplexVariety d) (L M : LineBundle X.scheme) :
    Function.Injective
      (globalTensorMap X.structureMap L.sheaf M.sheaf) :=
  LeBrunSalamon.PublishedInputs.ExternalTensorDiagonal.kunneth_degreeZero_injective X L M

/-- Coefficients on the actual open, with the actual induced scalar action. -/
def Coefficients {Y : Scheme} (s : Y ⟶ ComplexBase) (U : Y.Opens) : Type _ :=
  RingSections Y U

instance coefficientsCommRing {Y : Scheme} (s : Y ⟶ ComplexBase) (U : Y.Opens) :
    CommRing (Coefficients s U) := inferInstanceAs (CommRing (RingSections Y U))

instance coefficientsModule {Y : Scheme} (s : Y ⟶ ComplexBase) (U : Y.Opens) :
    Module ℂ (Coefficients s U) := Module.compHom (RingSections Y U) (constants s U)

instance coefficientsAlgebra {Y : Scheme} (s : Y ⟶ ComplexBase) (U : Y.Opens) :
    Algebra ℂ (Coefficients s U) :=
  Algebra.compHom (RingSections Y U) (constants s U)

theorem section_app_one {Y : Scheme} {E : OModule Y}
    (a : AlgebraicSection E) (U : Y.Opens) :
    Scheme.Modules.Hom.app a U (1 : RingSections Y U) =
      E.presheaf.map (homOfLE le_top).op (sectionValue a) := by
  have h := sheafHom_naturality a (homOfLE (show U ≤ ⊤ from le_top))
    (1 : RingSections Y ⊤)
  change E.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (sectionValue a) =
    Scheme.Modules.Hom.app a U
      (Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (1 : RingSections Y ⊤)) at h
  simpa only [map_one] using h.symm

/-- Restriction to the actual affine frame is complex-linear. -/
def coefficientLinear {Y : Scheme} (s : Y ⟶ ComplexBase)
    (L : LineBundle Y) (F : AffineLineFrame L) :
    ComplexSections s L.sheaf →ₗ[ℂ] Coefficients s F.openSet where
  toFun a := F.coefficient (L.sheaf.presheaf.map (homOfLE le_top).op a)
  map_add' := by intro a b; simp only [map_add]
  map_smul' := by
    intro c a
    change GlobalSections L.sheaf at a
    change F.coefficient (L.sheaf.val.map
        (homOfLE (show F.openSet ≤ ⊤ from le_top)).op
          (constants s ⊤ c • a)) =
      constants s F.openSet c *
        F.coefficient (L.sheaf.val.map (homOfLE le_top).op a)
    rw [L.sheaf.val.map_smul, F.coefficient.map_smul]
    change Y.presheaf.map (homOfLE (show F.openSet ≤ ⊤ from le_top)).op
        (constants s ⊤ c) *
          F.coefficient (L.sheaf.val.map (homOfLE le_top).op a) = _
    rw [constants_restrict]

theorem coefficientLinear_sectionValue {Y : Scheme} (s : Y ⟶ ComplexBase)
    (L : LineBundle Y) (F : AffineLineFrame L) (a : AlgebraicSection L.sheaf) :
    coefficientLinear s L F (sectionValue a) = F.localCoefficient a := by
  change F.coefficient (L.sheaf.presheaf.map (homOfLE le_top).op (sectionValue a)) =
    F.coefficient (Scheme.Modules.Hom.app a F.openSet (1 : RingSections Y F.openSet))
  rw [section_app_one]

/-- Restrict both genuine section factors to the specified affine frame.
The codomain is the actual coordinate ring of its affine self-product. -/
def coefficientTensorMap {Y : Scheme} (s : Y ⟶ ComplexBase)
    (L : LineBundle Y) (F : AffineLineFrame L) :
    (ComplexSections s L.sheaf ⊗[ℂ] ComplexSections s L.sheaf) →ₗ[ℂ]
      (Coefficients s F.openSet ⊗[ℂ] Coefficients s F.openSet) :=
  TensorProduct.map (coefficientLinear s L F) (coefficientLinear s L F)

theorem coefficientTensorMap_tmul {Y : Scheme} (s : Y ⟶ ComplexBase)
    (L : LineBundle Y) (F : AffineLineFrame L)
    (a b : ComplexSections s L.sheaf) :
    coefficientTensorMap s L F (a ⊗ₜ[ℂ] b) =
      coefficientLinear s L F a ⊗ₜ[ℂ] coefficientLinear s L F b := rfl

/-- Proved affine-local diagonal comparison. The actual open product ring,
diagonal kernel, pulled frame and thickened-diagonal cover are compared in
LSExternalFrameCoefficients; no project diagonal statement is admitted.
The sole geometric ring input is the generic degree-zero Künneth theorem
(Stacks 0BED). The line-bundle type inherits preservation of rank under
pullback (Stacks 01C5). The historical public name is retained. -/
theorem _root_.LeBrunSalamon.PublishedInputs.ExternalTensorDiagonal.diagonalRestriction_iff_quotientCoefficients
    {Y : Scheme}
    (s : Y ⟶ LeBrunSalamon.PhaseOne.ComplexBase) [IsSeparated s]
    (L : LeBrunSalamon.PhaseOne.LineBundle Y)
    (t : ComplexSections s L.sheaf ⊗[ℂ] ComplexSections s L.sheaf) (k : ℕ) :
    LeBrunSalamon.PhaseThree.VanishesToOrderAlongDiagonal s
      (LeBrunSalamon.PhaseTwentyEight.externalSquareLine s L).sheaf
      (LeBrunSalamon.PhaseTwentyEight.sectionFromValue
        (globalTensorMap s L.sheaf L.sheaf t)) k ↔
    ∀ F : LeBrunSalamon.Core.AffineLineFrame L,
      Ideal.Quotient.mk ((KaehlerDifferential.ideal ℂ
        (Coefficients s F.openSet)) ^ k) (coefficientTensorMap s L F t) = 0 := by
  letI : L.sheaf.IsQuasicoherent :=
    KunnethDegreeZero.quasicoherent_of_locallyFreeRank L.locallyFree
  let e (F : AffineLineFrame L) : LocalFrames.OverFrame L.sheaf F.openSet :=
    AffineFrameProof.frame F.openSet F.isAffine F.coefficient
  have hcover : (⨆ F : AffineLineFrame L, F.openSet) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨F, hxF⟩ := affineLineFrames_cover L x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨F, hxF⟩
  have hlinear (F : AffineLineFrame L) :
      ExternalFrameCoefficients.coefficientLinear s (e F) = coefficientLinear s L F := by
    ext a
    exact AffineFrameProof.frame_coordinates F.openSet F.isAffine F.coefficient _
  have htensor (F : AffineLineFrame L) :
      ExternalFrameCoefficients.coefficientTensorMap s (e F) (e F) =
        coefficientTensorMap s L F := by
    change TensorProduct.map (ExternalFrameCoefficients.coefficientLinear s (e F))
      (ExternalFrameCoefficients.coefficientLinear s (e F)) = _
    rw [hlinear]
    rfl
  have h := ExternalFrameCoefficients.vanishes_iff_cover_coefficients s
    (fun F : AffineLineFrame L => F.openSet) hcover (fun F => F.isAffine) e e t k
  have hglobal : globalTensorMap s L.sheaf L.sheaf =
      KunnethDegreeZero.canonicalMap s s L.sheaf L.sheaf := by rfl
  change VanishesToOrderAlongDiagonal s (externalTensor s L.sheaf L.sheaf)
    (sectionFromValue (globalTensorMap s L.sheaf L.sheaf t)) k ↔
      ∀ F : AffineLineFrame L,
        Ideal.Quotient.mk
          ((KaehlerDifferential.ideal ℂ (OpenProductCoordinates.Coefficients s F.openSet)) ^ k)
          (coefficientTensorMap s L F t) = 0
  rw [hglobal]
  refine h.trans ?_
  apply forall_congr'
  intro F
  rw [htensor]
  rfl

/-- Project API wrapper for affine-local diagonal-order detection. -/
theorem diagonalRestriction_iff_quotientCoefficients {Y : Scheme}
    (s : Y ⟶ LeBrunSalamon.PhaseOne.ComplexBase) [IsSeparated s]
    (L : LeBrunSalamon.PhaseOne.LineBundle Y)
    (t : ComplexSections s L.sheaf ⊗[ℂ] ComplexSections s L.sheaf) (k : ℕ) :
    LeBrunSalamon.PhaseThree.VanishesToOrderAlongDiagonal s
      (LeBrunSalamon.PhaseTwentyEight.externalSquareLine s L).sheaf
      (LeBrunSalamon.PhaseTwentyEight.sectionFromValue
        (globalTensorMap s L.sheaf L.sheaf t)) k ↔
    ∀ F : LeBrunSalamon.Core.AffineLineFrame L,
      Ideal.Quotient.mk ((KaehlerDifferential.ideal ℂ
        (Coefficients s F.openSet)) ^ k) (coefficientTensorMap s L F t) = 0 :=
  LeBrunSalamon.PublishedInputs.ExternalTensorDiagonal.diagonalRestriction_iff_quotientCoefficients
    s L t k

theorem relativeDerivation_constant {Y : Scheme} (s : Y ⟶ ComplexBase)
    {E : OModule Y} (D : RelativeSheafDerivation s E)
    (U : Y.Opens) (c : ℂ) : D.apply U (constants s U c) = 0 := by
  have hk := D.killsBase ⊤ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)
  change D.apply ⊤ (s.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) = 0 at hk
  have hn := D.naturality (homOfLE (show U ≤ ⊤ from le_top))
    (s.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))
  rw [hk, map_zero] at hn
  exact hn.symm

theorem tangentActs_constant {Y : Scheme} (s : Y ⟶ ComplexBase) (U : Y.Opens)
    (v : SectionsOn (tangentSheaf s) U) (c : ℂ) :
    tangentActs s U v (constants s U c) = 0 := by
  change (tangentCotangentPair s).apply U v
    ((cotangentPresentation s).differential.apply U (constants s U c)) = 0
  rw [relativeDerivation_constant]
  exact ((tangentCotangentPair s).apply U v).map_zero

/-- A supplied local vector field acts by a complex-linear operator. -/
def derivativeLinear {Y : Scheme} (s : Y ⟶ ComplexBase) (U : Y.Opens)
    (v : SectionsOn (tangentSheaf s) U) :
    Coefficients s U →ₗ[ℂ] Coefficients s U where
  toFun := tangentActs s U v
  map_add' := tangentActs_add_function s U v
  map_smul' := by
    intro c a
    change RingSections Y U at a
    change tangentActs s U v (constants s U c * a) =
      constants s U c * tangentActs s U v a
    rw [tangentActs_leibniz, tangentActs_constant, mul_zero, add_zero]

/-- The actual tangent action, retaining both its linear and Leibniz laws. -/
def coefficientDerivation {Y : Scheme} (s : Y ⟶ ComplexBase) (U : Y.Opens)
    (v : SectionsOn (tangentSheaf s) U) :
    Derivation ℂ (Coefficients s U) (Coefficients s U) where
  toLinearMap := derivativeLinear s U v
  map_one_eq_zero' := by
    change tangentActs s U v (1 : RingSections Y U) = 0
    simpa only [map_one] using tangentActs_constant s U v (1 : ℂ)
  leibniz' := by
    intro a b
    exact tangentActs_leibniz s U v a b

/-- Every derivation of the actual affine coefficient ring is the action
of an actual local tangent section. The only published input here is the
existing normalized affine sheaf-derivation correspondence. -/
theorem coefficientDerivation_surjective {Y : Scheme} (s : Y ⟶ ComplexBase)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (coefficientDerivation s U) := by
  intro D
  obtain ⟨δ, hδ⟩ := LeBrunSalamon.StandardInputs.affine_localDerivation_exists
    s U hU (fun a => D a) (map_zero D) (fun a b => map_add D a b)
    (fun a b => by simpa only [smul_eq_mul] using D.leibniz a b)
    (fun c => by
      change D (algebraMap ℂ (Coefficients s U) c) = 0
      exact D.map_algebraMap c)
  obtain ⟨φ, hφ⟩ := LocalDerivationProof.realize (cotangentPresentation s)
    (structureModule Y) U δ
  obtain ⟨v, hv⟩ := TangentBracketProof.localFunctional_surjective s U φ
  refine ⟨v, ?_⟩
  apply Derivation.ext
  intro a
  change tangentActs s U v a = D a
  have hlocal :
      (TangentBracketProof.localFunctional s U v).val.app (Opposite.op (Over.mk (𝟙 U)))
          ((cotangentPresentation s).differential.apply U a) =
        tangentActs s U ((tangentSheaf s).presheaf.map (𝟙 U).op v) a :=
    TangentBracketProof.localFunctional_apply s U v (Over.mk (𝟙 U)) a
  have hid : (tangentSheaf s).presheaf.map (𝟙 U).op v = v := by simp
  rw [hid, hv] at hlocal
  exact hlocal.symm.trans ((hφ (Over.mk (𝟙 U)) a).trans (hδ a))

/-- Smoothness of the coordinate algebra uses the original structure map
and the canonical complex constants on the actual affine open. -/
theorem coefficients_smooth {d : ℕ} (X : SmoothProperComplexVariety d)
    (U : X.scheme.Opens) (hU : IsAffineOpen U) :
    Algebra.Smooth ℂ (Coefficients X.structureMap U) := by
  have hf : (X.structureMap.appLE ⊤ U (by simp)).hom.Smooth :=
    X.structureMap.smooth_appLE (isAffineOpen_top ComplexBase) hU (by simp)
  have hg : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom.Smooth :=
    RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.symm.bijective
  apply RingHom.smooth_algebraMap.mp
  change ((X.structureMap.appLE ⊤ U (by simp)).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom).Smooth
  exact hg.comp hf

/-- The first-slot coefficient times a second-slot derivation annihilates
the square of the actual multiplication kernel. This is ordinary algebra. -/
theorem tensorFirst_zero_on_diagonal_square {A : Type*} [CommRing A] [Algebra ℂ A]
    (D : Derivation ℂ A A) (t : A ⊗[ℂ] A)
    (ht : t ∈ (KaehlerDifferential.ideal ℂ A) ^ 2) :
    D.tensorProductTo t = 0 := by
  rw [pow_two] at ht
  refine Submodule.mul_induction_on ht ?_ ?_
  · intro a ha b hb
    have ha' : Algebra.TensorProduct.lmul' ℂ a = 0 := ha
    have hb' : Algebra.TensorProduct.lmul' ℂ b = 0 := hb
    rw [Derivation.tensorProductTo_mul, ha', hb', zero_smul, zero_smul, zero_add]
  · intro a b ha hb
    rw [map_add, ha, hb, zero_add]

/-- The actual derivation of the second tensor factor. -/
def tensorRightDerivation {A : Type*} [CommRing A] [Algebra ℂ A]
    (D : Derivation ℂ A A) : Derivation ℂ (A ⊗[ℂ] A) (A ⊗[ℂ] A) where
  toLinearMap := TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) D.toLinearMap
  map_one_eq_zero' := by
    simp [Algebra.TensorProduct.one_def, D.map_one_eq_zero]
  leibniz' := by
    intro x y
    change TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) D.toLinearMap (x * y) =
      x * TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) D.toLinearMap y +
      y * TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) D.toLinearMap x
    refine TensorProduct.inductionOn x ?_ ?_
    · intro a b
      refine TensorProduct.inductionOn y ?_ ?_
      · intro c d
        simp [Algebra.TensorProduct.tmul_mul_tmul, Derivation.leibniz,
          smul_eq_mul, TensorProduct.tmul_add, mul_comm c a]
      · intro y z hy hz
        simp only [mul_add, add_mul, map_add, hy, hz]
        abel
    · intro x z hx hz
      simp only [mul_add, add_mul, map_add, hx, hz]
      abel

theorem tensorRightDerivation_tmul {A : Type*} [CommRing A] [Algebra ℂ A]
    (D : Derivation ℂ A A) (a b : A) :
    tensorRightDerivation D (a ⊗ₜ[ℂ] b) = a ⊗ₜ[ℂ] D b := rfl

/-- The displayed second-slot Hessian operator, with no divided factorial. -/
def tensorSecond {A : Type*} [CommRing A] [Algebra ℂ A]
    (D E : Derivation ℂ A A) : (A ⊗[ℂ] A) →ₗ[ℂ] A :=
  (D.tensorProductTo.restrictScalars ℂ).comp (tensorRightDerivation E).toLinearMap

theorem tensorSecond_tmul {A : Type*} [CommRing A] [Algebra ℂ A]
    (D E : Derivation ℂ A A) (a b : A) :
    tensorSecond D E (a ⊗ₜ[ℂ] b) = a * D (E b) := rfl

/-- A derivation lowers an arbitrary ideal power by at most one. -/
theorem derivation_mem_power {A : Type*} [CommRing A] [Algebra ℂ A]
    (D : Derivation ℂ A A) (I : Ideal A) (n : ℕ) (a : A)
    (ha : a ∈ I ^ (n + 1)) : D a ∈ I ^ n := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro x hx y hy
      rw [D.leibniz]
      change x * D y + y * D x ∈ I ^ (n + 1)
      apply Ideal.add_mem
      · exact (I ^ (n + 1)).mul_mem_right (D y) hx
      · rw [pow_succ]
        simpa only [mul_comm] using Ideal.mul_mem_mul (ih x hx) hy
    · intro x y hx hy
      rw [map_add]
      exact Ideal.add_mem _ hx hy

/-- The undivided second derivative annihilates the cube of the actual
diagonal ideal. No smoothness or nondegeneracy is used in this direction. -/
theorem tensorSecond_zero_on_diagonal_cube {A : Type*} [CommRing A] [Algebra ℂ A]
    (D E : Derivation ℂ A A) (t : A ⊗[ℂ] A)
    (ht : t ∈ (KaehlerDifferential.ideal ℂ A) ^ 3) :
    tensorSecond D E t = 0 := by
  apply tensorFirst_zero_on_diagonal_square D
  exact derivation_mem_power (tensorRightDerivation E) (KaehlerDifferential.ideal ℂ A) 2 t ht

/-- The actual tensor operator agrees with the quadratic reconstruction's
operator; the definitions use the same right-factor derivation. -/
theorem tensorSecond_eq_secondDiagonal {A : Type*} [CommRing A] [Algebra ℂ A]
    (D E : Derivation ℂ A A) :
    tensorSecond D E = LeBrunSalamon.SecondDiagonalAlgebra.second D E := rfl

/-- Second derivations separate the degree-two diagonal class by the proved
finite-projective reconstruction of I/I². The historical declaration name is
retained for compatibility; this declaration no longer contains an admission. -/
theorem _root_.LeBrunSalamon.PublishedInputs.ExternalTensorDiagonal.smooth_diagonal_secondDerivatives_detect
    {A : Type*} [CommRing A] [Algebra ℂ A] [Algebra.Smooth ℂ A]
    (t : A ⊗[ℂ] A) (ht : t ∈ (KaehlerDifferential.ideal ℂ A) ^ 2)
    (h : ∀ D E : Derivation ℂ A A, tensorSecond D E t = 0) :
    t ∈ (KaehlerDifferential.ideal ℂ A) ^ 3 := by
  exact LeBrunSalamon.SecondDiagonalAlgebra.smooth_second_derivatives_detect t ht h

/-- Project API wrapper for degree-two diagonal detection. -/
theorem smooth_diagonal_square_detected {A : Type*}
    [CommRing A] [Algebra ℂ A] [Algebra.Smooth ℂ A]
    (t : A ⊗[ℂ] A) (ht : t ∈ (KaehlerDifferential.ideal ℂ A) ^ 2)
    (h : ∀ D E : Derivation ℂ A A, tensorSecond D E t = 0) :
    t ∈ (KaehlerDifferential.ideal ℂ A) ^ 3 :=
  LeBrunSalamon.PublishedInputs.ExternalTensorDiagonal.smooth_diagonal_secondDerivatives_detect
    t ht h

def multiplyLinear {Y : Scheme} (s : Y ⟶ ComplexBase) (U : Y.Opens) :
    Coefficients s U →ₗ[ℂ] Coefficients s U →ₗ[ℂ] Coefficients s U where
  toFun a :=
    { toFun := fun b => a * b
      map_add' := by intro b c; exact mul_add _ _ _
      map_smul' := by
        intro c b
        change RingSections Y U at a b
        change a * (constants s U c * b) = constants s U c * (a * b)
        ring }
  map_add' := by
    intro a b
    ext c
    exact add_mul _ _ _
  map_smul' := by
    intro c a
    ext b
    change RingSections Y U at a b
    change (constants s U c * a) * b = constants s U c * (a * b)
    ring

/-- Any complex-linear operation in the second slot acts on the same
canonical tensor, independently of its finite presentation. -/
def localTensorMap {Y : Scheme} (s : Y ⟶ ComplexBase)
    (L : LineBundle Y) (F : AffineLineFrame L)
    (Q : ComplexSections s L.sheaf →ₗ[ℂ] Coefficients s F.openSet) :
    (ComplexSections s L.sheaf ⊗[ℂ] ComplexSections s L.sheaf) →ₗ[ℂ]
      Coefficients s F.openSet :=
  TensorProduct.lift ((multiplyLinear s F.openSet).compl₁₂ (coefficientLinear s L F) Q)

theorem localTensorMap_tmul {Y : Scheme} (s : Y ⟶ ComplexBase)
    (L : LineBundle Y) (F : AffineLineFrame L)
    (Q : ComplexSections s L.sheaf →ₗ[ℂ] Coefficients s F.openSet)
    (a b : ComplexSections s L.sheaf) :
    localTensorMap s L F Q (a ⊗ₜ[ℂ] b) = coefficientLinear s L F a * Q b := rfl

end ExternalTensorCoordinates

end ExternalTensorCoordinatesSection

namespace ExternalExpansion

open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

variable {d : ℕ} {X : SmoothProperComplexVariety d}
  {L : LineBundle X.scheme} {B : ExternalSquareSections X L}

open ExternalTensorCoordinates

/-- The actual global tensor represented by this finite expansion. -/
def tensor (E : ExternalExpansion X L B) :
    ComplexSections X.structureMap L.sheaf ⊗[ℂ] ComplexSections X.structureMap L.sheaf :=
  ∑ i, TensorProduct.tmul ℂ
    (M := ComplexSections X.structureMap L.sheaf)
    (N := ComplexSections X.structureMap L.sheaf)
    (sectionValue (E.left i)) (sectionValue (E.right i))

theorem tensor_image (E : ExternalExpansion X L B) :
    globalTensorMap X.structureMap L.sheaf L.sheaf E.tensor = sectionValue B := by
  have hB : sectionValue B = ∑ i, sectionValue
      (externalProductSection X.structureMap (E.left i) (E.right i)) := by
    calc
      sectionValue B = sectionValue
          (∑ i, externalProductSection X.structureMap (E.left i) (E.right i)) :=
        congrArg (fun a => sectionValue a) E.equation
      _ = _ := map_sum
        (sectionAddEquiv (externalSquareLine X.structureMap L).sheaf).toAddMonoidHom
        (fun i => externalProductSection X.structureMap (E.left i) (E.right i)) Finset.univ
  calc
    _ = ∑ i, sectionValue
        (externalProductSection X.structureMap (E.left i) (E.right i)) := by
      rw [tensor, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [globalTensorMap_tmul, sectionFromValue_sectionValue, sectionFromValue_sectionValue]
    _ = sectionValue B := hB.symm

theorem tensor_independent (E E' : ExternalExpansion X L B) : E.tensor = E'.tensor := by
  apply globalTensorMap_injective X L L
  rw [tensor_image, tensor_image]

theorem localTensorMap_tensor (E : ExternalExpansion X L B) (F : AffineLineFrame L)
    (Q : ComplexSections X.structureMap L.sheaf →ₗ[ℂ]
      Coefficients X.structureMap F.openSet) :
    localTensorMap X.structureMap L F Q E.tensor =
      ∑ i, multiplyLinear X.structureMap F.openSet
        (F.localCoefficient (E.left i)) (Q (sectionValue (E.right i))) := by
  rw [tensor, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [localTensorMap_tmul, coefficientLinear_sectionValue, multiplyLinear]
  rfl

theorem coefficientTensorMap_tensor (E : ExternalExpansion X L B)
    (F : AffineLineFrame L) :
    coefficientTensorMap X.structureMap L F E.tensor =
      ∑ i, TensorProduct.tmul ℂ
        (M := Coefficients X.structureMap F.openSet)
        (N := Coefficients X.structureMap F.openSet)
        (F.localCoefficient (E.left i)) (F.localCoefficient (E.right i)) := by
  rw [tensor, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coefficientTensorMap_tmul, coefficientLinear_sectionValue, coefficientLinear_sectionValue]

/-- The generic affine comparison applied to this actual finite expansion. -/
theorem coefficientTensor_mem_of_order (E : ExternalExpansion X L B) (k : ℕ)
    (h : VanishesToOrderAlongDiagonal X.structureMap
      (externalSquareLine X.structureMap L).sheaf B k) (F : AffineLineFrame L) :
    coefficientTensorMap X.structureMap L F E.tensor ∈
      (KaehlerDifferential.ideal ℂ (Coefficients X.structureMap F.openSet)) ^ k := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hB : sectionFromValue
      (globalTensorMap X.structureMap L.sheaf L.sheaf E.tensor) = B := by
    rw [E.tensor_image, sectionFromValue_sectionValue]
  exact (diagonalRestriction_iff_quotientCoefficients X.structureMap L E.tensor k).mp
    (by rw [hB]; exact h) F

/-- The scalar restriction b(x,x), in one line frame in BOTH slots. -/
def diagonalValue (E : ExternalExpansion X L B) (F : AffineLineFrame L) :
    RingSections X.scheme F.openSet :=
  ∑ i, F.localCoefficient (E.left i) * F.localCoefficient (E.right i)

/-- The first derivative in the SECOND slot, followed by restriction to the diagonal. Derivatives in the
first slot have the opposite linear-symbol sign once the diagonal value is zero. -/
def secondSlotFirst (E : ExternalExpansion X L B) (F : AffineLineFrame L)
    (v : SectionsOn (tangentSheaf X.structureMap) F.openSet) :
    RingSections X.scheme F.openSet :=
  ∑ i, F.localCoefficient (E.left i) *
    tangentActs X.structureMap F.openSet v (F.localCoefficient (E.right i))

/-- The UNDIVIDED second derivative. Lower diagonal terms have to
vanish before this expression is a tensor or a frame-independent symbol. -/
def secondSlotSecond (E : ExternalExpansion X L B) (F : AffineLineFrame L)
    (u v : SectionsOn (tangentSheaf X.structureMap) F.openSet) :
    RingSections X.scheme F.openSet :=
  ∑ i, F.localCoefficient (E.left i) *
    tangentActs X.structureMap F.openSet u
      (tangentActs X.structureMap F.openSet v (F.localCoefficient (E.right i)))

/-- One first-slot and one second-slot derivative. -/
def mixedSecond (E : ExternalExpansion X L B) (F : AffineLineFrame L)
    (u v : SectionsOn (tangentSheaf X.structureMap) F.openSet) :
    RingSections X.scheme F.openSet :=
  ∑ i, tangentActs X.structureMap F.openSet u (F.localCoefficient (E.left i)) *
    tangentActs X.structureMap F.openSet v (F.localCoefficient (E.right i))

/-- The scalar diagonal value is the image under the canonical multiplication map. -/
theorem diagonalValue_eq_multiply (E : ExternalExpansion X L B) (F : AffineLineFrame L) :
    E.diagonalValue F = Algebra.TensorProduct.lmul'
      (S := Coefficients X.structureMap F.openSet) ℂ
      (coefficientTensorMap X.structureMap L F E.tensor) := by
  rw [coefficientTensorMap_tensor, map_sum]
  rfl

/-- The displayed first derivative is the standard derivation-induced map
on the actual affine coefficient tensor. -/
theorem secondSlotFirst_eq_tensorFirst (E : ExternalExpansion X L B)
    (F : AffineLineFrame L)
    (v : SectionsOn (tangentSheaf X.structureMap) F.openSet) :
    E.secondSlotFirst F v =
      (coefficientDerivation X.structureMap F.openSet v).tensorProductTo
        (coefficientTensorMap X.structureMap L F E.tensor) := by
  rw [coefficientTensorMap_tensor, map_sum]
  rfl

theorem secondSlotSecond_eq_tensorSecond (E : ExternalExpansion X L B)
    (F : AffineLineFrame L)
    (u v : SectionsOn (tangentSheaf X.structureMap) F.openSet) :
    E.secondSlotSecond F u v =
      tensorSecond (coefficientDerivation X.structureMap F.openSet u)
        (coefficientDerivation X.structureMap F.openSet v)
        (coefficientTensorMap X.structureMap L F E.tensor) := by
  rw [coefficientTensorMap_tensor, map_sum]
  rfl

/-- Independence of a tensor decomposition is proved from its equality
as an actual section of L boxtimes L. No preferred basis of H^0(L) is used. -/
theorem diagonalValue_independent (E E' : ExternalExpansion X L B)
    (F : AffineLineFrame L) : E.diagonalValue F = E'.diagonalValue F := by
  have h := congrArg (localTensorMap X.structureMap L F
    (coefficientLinear X.structureMap L F)) (tensor_independent E E')
  simp only [localTensorMap_tensor, coefficientLinear_sectionValue] at h
  change E.diagonalValue F = E'.diagonalValue F at h
  exact h

theorem secondSlotFirst_independent (E E' : ExternalExpansion X L B)
    (F : AffineLineFrame L)
    (v : SectionsOn (tangentSheaf X.structureMap) F.openSet) :
    E.secondSlotFirst F v = E'.secondSlotFirst F v := by
  have h := congrArg (localTensorMap X.structureMap L F
    ((derivativeLinear X.structureMap F.openSet v).comp
      (coefficientLinear X.structureMap L F))) (tensor_independent E E')
  simp only [localTensorMap_tensor, LinearMap.comp_apply,
    coefficientLinear_sectionValue] at h
  change E.secondSlotFirst F v = E'.secondSlotFirst F v at h
  exact h

theorem secondSlotSecond_independent (E E' : ExternalExpansion X L B)
    (F : AffineLineFrame L)
    (u v : SectionsOn (tangentSheaf X.structureMap) F.openSet) :
    E.secondSlotSecond F u v = E'.secondSlotSecond F u v := by
  have h := congrArg (localTensorMap X.structureMap L F
    ((derivativeLinear X.structureMap F.openSet u).comp
      ((derivativeLinear X.structureMap F.openSet v).comp
        (coefficientLinear X.structureMap L F)))) (tensor_independent E E')
  simp only [localTensorMap_tensor, LinearMap.comp_apply,
    coefficientLinear_sectionValue] at h
  change E.secondSlotSecond F u v = E'.secondSlotSecond F u v at h
  exact h

/-- Quadratic diagonal vanishing kills the value term, not just its values at one chosen point. -/
theorem diagonalValue_zero_of_orderTwo (E : ExternalExpansion X L B)
    (h : VanishesQuadraticallyAlongDiagonal X.structureMap
      (externalSquareLine X.structureMap L).sheaf B)
    (F : AffineLineFrame L) : E.diagonalValue F = 0 := by
  rw [E.diagonalValue_eq_multiply F]
  have hm := E.coefficientTensor_mem_of_order 2 h F
  have hi : coefficientTensorMap X.structureMap L F E.tensor ∈
      KaehlerDifferential.ideal ℂ (Coefficients X.structureMap F.openSet) :=
    (Ideal.pow_le_self (by decide)) hm
  exact hi

/-- The full first symbol vanishes BEFORE interpreting the Hessian. -/
theorem secondSlotFirst_zero_of_orderTwo (E : ExternalExpansion X L B)
    (h : VanishesQuadraticallyAlongDiagonal X.structureMap
      (externalSquareLine X.structureMap L).sheaf B)
    (F : AffineLineFrame L)
    (v : SectionsOn (tangentSheaf X.structureMap) F.openSet) :
    E.secondSlotFirst F v = 0 := by
  rw [E.secondSlotFirst_eq_tensorFirst F v]
  exact tensorFirst_zero_on_diagonal_square
    (coefficientDerivation X.structureMap F.openSet v)
    (coefficientTensorMap X.structureMap L F E.tensor)
    (E.coefficientTensor_mem_of_order 2 h F)

/-- The commutator term is a first derivative, so the Hessian becomes
symmetric only after the lower-order symbol has vanished. -/
theorem secondSlotSecond_symmetric_of_orderTwo (E : ExternalExpansion X L B)
    (h : VanishesQuadraticallyAlongDiagonal X.structureMap
      (externalSquareLine X.structureMap L).sheaf B)
    (F : AffineLineFrame L)
    (u v : SectionsOn (tangentSheaf X.structureMap) F.openSet) :
    E.secondSlotSecond F u v = E.secondSlotSecond F v u := by
  apply sub_eq_zero.mp
  calc
    E.secondSlotSecond F u v - E.secondSlotSecond F v u =
        E.secondSlotFirst F (tangentBracket X.structureMap F.openSet u v) := by
      simp only [secondSlotSecond, secondSlotFirst, tangentBracket_spec,
        mul_sub, Finset.sum_sub_distrib]
    _ = 0 := E.secondSlotFirst_zero_of_orderTwo h F _


/-- On a quadratic-vanishing kernel mixed Hessians have the opposite sign. -/
theorem mixedSecond_eq_neg_of_orderTwo (E : ExternalExpansion X L B)
    (h : VanishesQuadraticallyAlongDiagonal X.structureMap
      (externalSquareLine X.structureMap L).sheaf B)
    (F : AffineLineFrame L)
    (u v : SectionsOn (tangentSheaf X.structureMap) F.openSet) :
    E.mixedSecond F u v = -E.secondSlotSecond F u v := by
  have hsum :
      tangentActs X.structureMap F.openSet u (E.secondSlotFirst F v) =
        E.mixedSecond F u v + E.secondSlotSecond F u v := by
    unfold secondSlotFirst
    change (TangentActionProof.functionAddHom X.structureMap F.openSet u)
        (∑ i, F.localCoefficient (E.left i) *
          tangentActs X.structureMap F.openSet v (F.localCoefficient (E.right i))) = _
    rw [map_sum]
    unfold mixedSecond secondSlotSecond
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    change tangentActs X.structureMap F.openSet u
        (F.localCoefficient (E.left i) *
          tangentActs X.structureMap F.openSet v (F.localCoefficient (E.right i))) = _
    rw [tangentActs_leibniz]
    ring
  have hz : E.mixedSecond F u v + E.secondSlotSecond F u v = 0 := by
    rw [← hsum, E.secondSlotFirst_zero_of_orderTwo h F v,
      TangentActionProof.zero_function]
  linear_combination hz


/-- Tensoriality in the first derivative argument is automatic. -/
theorem secondSlotSecond_smul_left (E : ExternalExpansion X L B)
    (F : AffineLineFrame L) (a : RingSections X.scheme F.openSet)
    (u v : SectionsOn (tangentSheaf X.structureMap) F.openSet) :
    E.secondSlotSecond F (a • u) v = a * E.secondSlotSecond F u v := by
  unfold secondSlotSecond
  simp only [TangentActionProof.smul_field]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring


/-- Tensoriality in the inner derivative argument uses vanishing of
first derivatives. Without h this assertion would generally be false. -/
theorem secondSlotSecond_smul_right_of_orderTwo (E : ExternalExpansion X L B)
    (h : VanishesQuadraticallyAlongDiagonal X.structureMap
      (externalSquareLine X.structureMap L).sheaf B)
    (F : AffineLineFrame L) (a : RingSections X.scheme F.openSet)
    (u v : SectionsOn (tangentSheaf X.structureMap) F.openSet) :
    E.secondSlotSecond F u (a • v) = a * E.secondSlotSecond F u v := by
  rw [E.secondSlotSecond_symmetric_of_orderTwo h F u (a • v),
    E.secondSlotSecond_smul_left F a v u,
    E.secondSlotSecond_symmetric_of_orderTwo h F v u]


/-- Third-order diagonal vanishing annihilates the actual undivided
second-slot Hessian. This direction only uses ideal-power calculus. -/
theorem zeroHessian_of_orderThree (E : ExternalExpansion X L B)
    (h : VanishesToOrderAlongDiagonal X.structureMap
      (externalSquareLine X.structureMap L).sheaf B 3)
    (F : AffineLineFrame L)
    (u v : SectionsOn (tangentSheaf X.structureMap) F.openSet) :
    E.secondSlotSecond F u v = 0 := by
  rw [E.secondSlotSecond_eq_tensorSecond F u v]
  exact tensorSecond_zero_on_diagonal_cube
    (coefficientDerivation X.structureMap F.openSet u)
    (coefficientDerivation X.structureMap F.openSet v)
    (coefficientTensorMap X.structureMap L F E.tensor)
    (E.coefficientTensor_mem_of_order 3 h F)

/-- On a smooth complex variety zero Hessian, after quadratic vanishing, is exactly vanishing to order at
least three. This is the bridge to I_Delta^2/I_Delta^3 and fixes the factorial convention. -/
theorem orderThree_iff_zeroHessian (E : ExternalExpansion X L B)
    (h : VanishesQuadraticallyAlongDiagonal X.structureMap
      (externalSquareLine X.structureMap L).sheaf B) :
    VanishesToOrderAlongDiagonal X.structureMap
      (externalSquareLine X.structureMap L).sheaf B 3 ↔
    ∀ (F : AffineLineFrame L)
      (u v : SectionsOn (tangentSheaf X.structureMap) F.openSet),
      E.secondSlotSecond F u v = 0 := by
  constructor
  · intro hthree
    exact E.zeroHessian_of_orderThree hthree
  · intro hz
    have hB : sectionFromValue
        (globalTensorMap X.structureMap L.sheaf L.sheaf E.tensor) = B := by
      rw [E.tensor_image, sectionFromValue_sectionValue]
    have hthree : VanishesToOrderAlongDiagonal X.structureMap
        (externalSquareLine X.structureMap L).sheaf
        (sectionFromValue
          (globalTensorMap X.structureMap L.sheaf L.sheaf E.tensor)) 3 := by
      apply (diagonalRestriction_iff_quotientCoefficients
        X.structureMap L E.tensor 3).mpr
      intro F
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      letI : Algebra.Smooth ℂ (Coefficients X.structureMap F.openSet) :=
        coefficients_smooth X F.openSet F.isAffine
      apply smooth_diagonal_square_detected
        (coefficientTensorMap X.structureMap L F E.tensor)
        (E.coefficientTensor_mem_of_order 2 h F)
      intro D D'
      obtain ⟨u, rfl⟩ := coefficientDerivation_surjective
        X.structureMap F.openSet F.isAffine D
      obtain ⟨v, rfl⟩ := coefficientDerivation_surjective
        X.structureMap F.openSet F.isAffine D'
      rw [← E.secondSlotSecond_eq_tensorSecond F u v]
      exact hz F u v
    simpa only [hB] using hthree

end ExternalExpansion

/-! ## B. The normalized global contact-kernel contract -/

/-- The contact form in a local scalar frame, evaluated on an ACTUAL
section of the intrinsic tangent sheaf. -/
def localContactValue {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X) (F : AffineLineFrame C.sequence.line)
    (v : SectionsOn (tangentSheaf X.structureMap) F.openSet) :
    RingSections X.scheme F.openSet :=
  F.coefficient (C.sequence.form.app F.openSet v)

/-- Equality with the manuscript's normalized quadratic contact symbol. This alone does NOT assert lower-
order vanishing; those hypotheses are separately required by `NormalizedContactKernel` below. -/
def ExpansionHasContactHessian {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X)
    {B : ExternalSquareSections X C.sequence.line}
    (E : ExternalExpansion X C.sequence.line B) : Prop :=
  ∀ (F : AffineLineFrame C.sequence.line)
    (u v : SectionsOn (tangentSheaf X.structureMap) F.openSet),
    E.secondSlotSecond F u v =
      (2 : RingSections X.scheme F.openSet) *
        localContactValue C F u * localContactValue C F v

/-- A representation-independent formulation of [B]_2 = theta^2, provided the lower diagonal symbols
vanish. The existence of a finite expansion uses properness, but the equation is tested on every affine
frame rather than on global functions alone. -/
def HasNormalizedContactSymbol {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X)
    (B : ExternalSquareSections X C.sequence.line) : Prop :=
  ∃ E : ExternalExpansion X C.sequence.line B, ExpansionHasContactHessian C E

/-- Independence is derived, not simply included as a field of an
abstract symbol-identification certificate. -/
theorem contactHessian_independent {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X)
    {B : ExternalSquareSections X C.sequence.line}
    (E E' : ExternalExpansion X C.sequence.line B) :
    ExpansionHasContactHessian C E ↔ ExpansionHasContactHessian C E' := by
  constructor
  · intro h F u v
    rw [← ExternalExpansion.secondSlotSecond_independent E E' F u v]
    exact h F u v
  · intro h F u v
    rw [ExternalExpansion.secondSlotSecond_independent E E' F u v]
    exact h F u v

/-- Any expansion may be used after the normalization has been checked on one. In particular no choice of
a tensor decomposition can change which sections satisfy the normalized-symbol condition. -/
theorem normalizedSymbol_on_any_expansion {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactStructure X)
    {B : ExternalSquareSections X C.sequence.line}
    (h : HasNormalizedContactSymbol C B)
    (E : ExternalExpansion X C.sequence.line B) :
    ExpansionHasContactHessian C E := by
  obtain ⟨E', hE'⟩ := h
  exact (contactHessian_independent C E' E).mp hE'

/-- SOURCE CONTRACT: jets.tex, Proposition jet:diagonal and the
hypotheses of Theorem jet:criterion.

Nothing in this structure asserts first-jet generation, immersion,
transitivity, or classification. Fano positivity is NOT needed for
the symmetric-jet criterion, so this structure is over a smooth proper
contact variety, not specifically a contact Fano manifold. -/
structure NormalizedContactKernel {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) where
  twoPointSection : ExternalSquareSections X C.sequence.line
  symmetric : IsSymmetricExternalSection X.structureMap C.sequence.line twoPointSection
  orderTwo : VanishesQuadraticallyAlongDiagonal X.structureMap
    (externalSquareLine X.structureMap C.sequence.line).sheaf twoPointSection
  normalized : HasNormalizedContactSymbol C twoPointSection

namespace NormalizedContactKernel

variable {n : ℕ} {X : SmoothProperComplexVariety (2 * n + 1)}
  {C : IntrinsicContactStructure X}

/-- There is no unspecified auxiliary section space in this contract. -/
def expansion (K : NormalizedContactKernel X C) :
    ExternalExpansion X C.sequence.line K.twoPointSection :=
  Classical.choose K.normalized

theorem expansion_normalized (K : NormalizedContactKernel X C) :
    ExpansionHasContactHessian C K.expansion :=
  Classical.choose_spec K.normalized

/-- Exactness of the contact quotient gives a unit contact value on a nonempty affine frame. -/
theorem contactValue_unit_witness :
    ∃ (F : AffineLineFrame C.sequence.line)
      (v : SectionsOn (tangentSheaf X.structureMap) F.openSet),
      localContactValue C F v = 1 ∧
        (2 : RingSections X.scheme F.openSet) ≠ 0 := by
  classical
  let z : X.scheme := Classical.choice X.nonempty
  obtain ⟨F, hz⟩ := affineLineFrames_cover C.sequence.line z
  letI : Nonempty F.openSet := ⟨⟨z, hz⟩⟩
  letI : Nontrivial (RingSections X.scheme F.openSet) := inferInstance
  let scalar : ℂ →+* RingSections X.scheme F.openSet :=
    (X.structureMap.appLE ⊤ F.openSet (by simp)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  letI : CharZero (RingSections X.scheme F.openSet) :=
    charZero_of_injective_ringHom scalar.injective
  letI : (intrinsicTangentBundle X).sheaf.IsQuasicoherent :=
    LocalExtensionSplitting.quasicoherent_of_locallyFreeRank
      (intrinsicTangentBundle X).locallyFree
  letI : C.sequence.line.sheaf.IsQuasicoherent :=
    LocalExtensionSplitting.quasicoherent_of_locallyFreeRank C.sequence.line.locallyFree
  letI : Epi C.sequence.form := C.sequence.shortExact.epi_g
  obtain ⟨v, hv⟩ := LocalExtensionSplitting.affine_sectionMap_surjective C.sequence.form
    F.openSet F.isAffine (F.coefficient.symm 1)
  refine ⟨F, v, ?_, by norm_num⟩
  unfold localContactValue
  rw [hv, F.coefficient.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Source: jet:second-symbol. A contact form is a quotient onto a line, so its square is nonzero on a
nonempty contact variety. Unlike the old local certificate, nonvanishing is a CONSEQUENCE here. -/
theorem section_nonzero (K : NormalizedContactKernel X C) :
    K.twoPointSection ≠ 0 := by
  intro h
  let E₀ : ExternalExpansion X C.sequence.line K.twoPointSection :=
    { size := 0
      left := fun i => Fin.elim0 i
      right := fun i => Fin.elim0 i
      equation := by simpa using h }
  obtain ⟨F, v, hv, htwo⟩ := contactValue_unit_witness (X := X) (C := C)
  have hnorm := normalizedSymbol_on_any_expansion C K.normalized E₀ F v v
  have hz : E₀.secondSlotSecond F v v = 0 := by
    simp [ExternalExpansion.secondSlotSecond, E₀]
  rw [hz, hv, mul_one, mul_one] at hnorm
  exact htwo hnorm.symm


/-- Exactness of order two is proved rather than required as an extra
hypothesis. Higher-order vanishing contradicts the normalized Hessian. -/
theorem exact_order_two (K : NormalizedContactKernel X C) :
    HasExactDiagonalOrder X.structureMap
      (externalSquareLine X.structureMap C.sequence.line).sheaf K.twoPointSection 2 := by
  refine ⟨K.orderTwo, ?_⟩
  intro hthree
  have hz := ExternalExpansion.zeroHessian_of_orderThree K.expansion hthree
  obtain ⟨F, v, hv, htwo⟩ := contactValue_unit_witness (X := X) (C := C)
  have hnorm := K.expansion_normalized F v v
  rw [hz F v v, hv, mul_one, mul_one] at hnorm
  exact htwo hnorm.symm


/- The original slice_nonzero is proved in LSHamiltonianJets using the actual point frame. -/

set_option backward.isDefEq.respectTransparency false in
/-- Finite expansions of a normalized kernel cannot be empty. -/
theorem expansion_size_positive (K : NormalizedContactKernel X C)
    (E : ExternalExpansion X C.sequence.line K.twoPointSection) : 0 < E.size := by
  by_contra h
  have hs : E.size = 0 := Nat.eq_zero_of_not_pos h
  apply K.section_nonzero
  rw [E.equation]
  letI : IsEmpty (Fin E.size) := by
    rw [hs]
    infer_instance
  simp






end NormalizedContactKernel

/-! ## C. The local algebra the manuscript uses inside jet:criterion -/

namespace LocalJet

open LeBrunSalamon.PhaseNineteen LeBrunSalamon.PhaseTwentyTwo
open LeBrunSalamon.PhaseSeventeen

variable (V S : Type*) [AddCommGroup V] [Module ℂ V]
  [AddCommGroup S] [Module ℂ S]

/-- The literal coefficient conditions obtained from D_v^(1) b = k b. Keeping the entire quadratic
expression visible avoids silently discarding -alpha(v) * A(s,s) before horizontality is proved. -/
def IsProjectiveKernelDirection (J : ContactOneJet V) (v : V) (k : ℂ) : Prop :=
  (∀ s : V, J.firstSlotLinear v s = 0) ∧
    ∀ s : V, J.firstSlotQuadratic v s = k * J.quadratic s

/-- SOURCE: jets.tex, jet:local-calculation followed by jet:kernel. This is exactly the local injectivity
inference, now with the full linear and quadratic coefficients as hypotheses. -/
theorem projectiveKernelDirection_zero (J : ContactOneJet V)
    (v : V) (k : ℂ) (h : IsProjectiveKernelDirection V J v k) :
    v = 0 := by
  have hlin : ∀ s : V, J.theta s * J.theta v = 0 := by
    intro s
    have hs := h.1 s
    unfold ContactOneJet.firstSlotLinear at hs
    linear_combination (-1 / 2 : ℂ) * hs
  have hv : J.theta v = 0 :=
    contactJet_linearTerm_forces_horizontal V J v hlin
  have hquad : ∀ s : V,
      J.theta s * (J.exteriorValue v s - k * J.theta s) = 0 := by
    intro s
    have hs := h.2 s
    unfold ContactOneJet.firstSlotQuadratic ContactOneJet.quadratic at hs
    rw [hv] at hs
    linear_combination hs
  exact contactJet_noProjectiveKernel V J v k hlin hquad

/-- Literal bridge to the old finite-dimensional jet lemma. The proportionality test uses a vector-space
equality, not pointwise proportionality with a scalar depending on the SECOND point. -/
structure KernelTaylorData where
  contact : ContactOneJet V
  jet : SectionValuedFirstJet V S
  value_nonzero : jet.value ≠ 0
  coefficients : ∀ v k, jet.derivative v = k • jet.value →
    IsProjectiveKernelDirection V contact v k

/-- No new geometric assumptions are introduced in this deduction. -/
theorem KernelTaylorData.immersive (D : KernelTaylorData V S) :
    D.jet.IsProjectivelyImmersive := by
  refine ⟨D.value_nonzero, ?_⟩
  intro v k h
  exact projectiveKernelDirection_zero V D.contact v k (D.coefficients v k h)

/-- Dualizing the immersive kernel gives ALL first jets, not just the Reeb/contact-normal direction. -/
theorem KernelTaylorData.firstJets [FiniteDimensional ℂ V]
    (D : KernelTaylorData V S) : D.jet.SeparatesFirstJets :=
  immersiveKernel_separatesFirstJets V S D.jet (KernelTaylorData.immersive V S D)

/- This identifies the exact remaining geometric cut in the proof: construct these data from the genuine
global kernel and identify its contractions with actual global sections of L. Do NOT assert that arbitrary
data D arise from geometry, and do NOT use the old admitted `contactFano_firstJetGeneration_target` to
establish this cut. -/
end LocalJet

/-! ## D. Actual curves and a noncircular manuscript proof route -/

/-- The output of sm:very-free, with honest curve degree and honest pullback tangent-bundle positivity. A
numerical splitting profile alone is not accepted. -/
structure VeryFreeContactConic (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {n : ℕ} (X : ContactFanoManifold n) where
  curve : RationalCurve P X.variety
  contactDegreeTwo : IsIntrinsicContactConic P p X.contact curve
  veryFree : IsVeryFreeRationalCurve P X.variety
    (intrinsicTangentBundle X.variety) curve

/- The actual splitting is a consequence of degree and very-freeness,
not assumed as an unrelated integer profile. -/
/- Exact declaration relocated to LSConicSplitting; see owners/root/CONIC_RELOCATION_RECORD.json. -/

/-- Interface conversion only: the old smoothing target has the same output geometry as this new package.
This equivalence is NOT a proof that a conic exists. -/
theorem veryFreeConic_nonempty_iff (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {n : ℕ} (X : ContactFanoManifold n) :
    Nonempty (VeryFreeContactConic P p X) ↔
    ∃ g : RationalCurve P X.variety,
      IsIntrinsicContactConic P p X.contact g ∧
      IsVeryFreeRationalCurve P X.variety (intrinsicTangentBundle X.variety) g := by
  constructor
  · rintro ⟨g⟩
    exact ⟨g.curve, g.contactDegreeTwo, g.veryFree⟩
  · rintro ⟨g, hd, hf⟩
    exact ⟨⟨g, hd, hf⟩⟩

/-- Classical branches of red:alternatives, after proving first-jet separation for the standard incidence
and contact-projective models. The construction of those models is NOT included in this proposition. -/
def NonprimitiveBranch : Prop :=
  ∀ (n : ℕ) (X : ContactFanoManifold n),
    ¬ HasPrimitiveContactPicard X.contact →
      SeparatesFirstJets X.variety X.contact.sequence.line

/-- Manuscript lines:suitable-pair + sm:very-free. -/
def PrimitiveSmoothing (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) : Prop :=
  ∀ (n : ℕ) (X : ContactFanoManifold n),
    HasPrimitiveContactPicard X.contact → Nonempty (VeryFreeContactConic P p X)

/-- The precise OUTPUT needed from extension.tex, descent.tex and
jet:diagonal. It is still one large construction cut, deliberately NOT
weakened to 'some proper moving-pair tensor exists': zero lifts would
satisfy that weaker assertion and give no information.

Implementation must retain the FULL neighborhood of the map in Hom_2,
both moving source points, the intrinsic invariant source tensor, and
the contact-value identity, before deriving the normalized symbol.
The coarse source in the manuscript is an ALGEBRAIC SPACE. Either
formalize that category or justify a proper scheme cover and transport
all data; the older scheme-only interface is not silently identical. -/
def ConicToNormalizedKernel (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) : Prop :=
  ∀ (n : ℕ) (X : ContactFanoManifold n),
    HasPrimitiveContactPicard X.contact →
      VeryFreeContactConic P p X →
        Nonempty (NormalizedContactKernel X.variety X.contact)

/-- These are explicit INPUT THEOREMS to the manuscript proof route. There is intentionally no global
instance and no admitted declaration constructing this package. In particular, providing a list of final
conclusions is not advertised as a proof of the manuscript. -/
structure ManuscriptCoreInputs (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) : Prop where
  nonprimitive : NonprimitiveBranch
  smoothing : PrimitiveSmoothing P p
  kernelConstruction : ConicToNormalizedKernel P p





/-- A zero section cannot be used to fill the normalized-kernel cut,
even though it gives zero lifts with a common contact value. -/
theorem zero_not_normalizedKernel {n : ℕ}
    (X : SmoothProperComplexVariety (2 * n + 1))
    (C : IntrinsicContactStructure X) (K : NormalizedContactKernel X C) :
    K.twoPointSection ≠ 0 := K.section_nonzero

end LeBrunSalamon.Core

/-!
# Manuscript skeleton: geometric outputs and end-to-end assembly

Preferred entry point: `LeBrunSalamon.Skeleton.leBrunSalamon_project`. The interfaces below are theorem
obligations, NOT evidence of their truth. They refine the large cuts in Core and connect them to actual
algebraic embeddings and smooth metric homotheties. No package of input proofs is constructed by an
admission, and no legacy `*_target` theorem is used.

The construction order follows reduction -> lines -> smoothing -> extension
-> descent -> diagonal -> symmetric jets -> homogeneous -> twistor.
Foundations can be proved in parallel; source labels refer to the pinned
manuscript recorded in Project. Only proof fields may be admitted.
-/
namespace LeBrunSalamon.Skeleton

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseFour
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTen
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFive LeBrunSalamon.Core

/-! ## A. Canonical comparisons, not arbitrary bundle isomorphisms -/

/-- The ordinary evaluation pairing E^vee x E -> O, on every open. -/
def dualEvaluation {X : Scheme} (E : OModule X) :
    SheafBilinearMap (dualSheaf E) E (structureModule X) :=
  (tensorPresentation (dualSheaf E) E).pair.postcompose
    (internalHomPresentation E (structureModule X)).evaluate

/-- Canonical f*(E^vee) -> (f*E)^vee, normalized by evaluation.
Choosing an arbitrary isomorphism of these bundles would corrupt df. -/
def dualBaseChange {X Y : Scheme} (f : X ⟶ Y) (E : OModule Y) :
    pullbackModule f (dualSheaf E) ⟶ dualSheaf (pullbackModule f E) :=
  currySheaf (tensorLift
    ((pullbackPair f (dualEvaluation E)).postcompose (unitPullbackMap f)))

/-- **Published input (exact).** EGA I (1960), chapitre 0, (5.4.5),
states for every morphism of ringed spaces that the canonical comparison
f*(Eᵛ) → (f*E)ᵛ is an isomorphism when E is locally free of finite rank.
Finite rank is the standing convention at the end of (5.4.1).
The canonical map is that of (4.4.6); `dualBaseChange_pullLocalSection`
below proves its evaluation normalization on every pair of pulled local
sections, so the particular map in this statement is fixed.
Primary source: Grothendieck, Publications Mathématiques de l'IHÉS 4
(1960), chapitre 0, (5.4.5), DOI 10.1007/BF02684778:
https://numdam.org/item/PMIHES_1960__4__5_0/ . -/
theorem _root_.LeBrunSalamon.PublishedInputs.BaseChangeFibers.dualBaseChange_isIso
    {X Y : Scheme} (f : X ⟶ Y) {E : OModule Y} {r : ℕ}
    (h : IsLocallyFreeOfRank E r) :
    IsIso (LeBrunSalamon.Skeleton.dualBaseChange f E) := by
  sorry

/-- Project API wrapper for finite-locally-free dual base change. -/
theorem dualBaseChange_isIso {X Y : Scheme} (f : X ⟶ Y)
    {E : OModule Y} {r : ℕ} (h : IsLocallyFreeOfRank E r) :
    IsIso (dualBaseChange f E) :=
  LeBrunSalamon.PublishedInputs.BaseChangeFibers.dualBaseChange_isIso f h

/-- The canonical derivative TX -> f*TY, for maps of smooth C-varieties.
Its only transport is the specified equality of structure maps. -/
def differentialOver {d e : ℕ} (X : SmoothProperComplexVariety d)
    (Y : SmoothProperComplexVariety e) (f : X.scheme ⟶ Y.scheme)
    (hf : f ≫ Y.structureMap = X.structureMap) :
    tangentSheaf X.structureMap ⟶ pullbackModule f (tangentSheaf Y.structureMap) := by
  letI := dualBaseChange_isIso f (smooth_cotangent_rank Y.structureMap e Y.smooth)
  exact eqToHom (congrArg tangentSheaf hf.symm) ≫ tangentMapRaw f Y.structureMap ≫
    (asIso (dualBaseChange f (cotangentSheaf Y.structureMap))).inv

section ContactDerivativeIsoSection

set_option backward.isDefEq.respectTransparency false

namespace ContactDerivativeIsoProof

open LeBrunSalamon.Refinement

private theorem relativeDerivation_ext {X S : Scheme} {s : X ⟶ S}
    {E : OModule X} {D₁ D₂ : RelativeSheafDerivation s E}
    (h : ∀ U a, D₁.apply U a = D₂.apply U a) : D₁ = D₂ := by
  cases D₁ with
  | mk d₁ z₁ a₁ l₁ n₁ b₁ =>
    cases D₂ with
    | mk d₂ z₂ a₂ l₂ n₂ b₂ =>
      have hd : d₁ = d₂ := funext (fun U => funext (fun a => h U a))
      subst d₂
      rfl

/-- Normalization on the genuine universal differential. -/
theorem cotangentMap_differential {Y Z S : Scheme}
    (f : Y ⟶ Z) (s : Z ⟶ S) (U : Z.Opens) (a : RingSections Z U) :
    (cotangentMap f s).app (f ⁻¹ᵁ U)
      (pullLocalSection f (cotangentSheaf s) U
        ((cotangentPresentation s).differential.apply U a)) =
      (cotangentPresentation (f ≫ s)).differential.apply (f ⁻¹ᵁ U) (f.app U a) := by
  have h := congrArg (fun D : RelativeSheafDerivation s
      ((Scheme.Modules.pushforward f).obj (cotangentSheaf (f ≫ s))) => D.apply U a)
    (differentialLift_spec (pulledFunctionDifferential f s))
  rw [← cotangentMap_adjoint f s] at h
  exact h

theorem differential_transport {Y S : Scheme} (s t : Y ⟶ S) (h : s = t)
    (U : Y.Opens) (a : RingSections Y U) :
    (eqToHom (congrArg cotangentSheaf h)).app U
        ((cotangentPresentation s).differential.apply U a) =
      (cotangentPresentation t).differential.apply U a := by
  subst t
  rfl

theorem dualEvaluation_transport {Y S : Scheme} (s t : Y ⟶ S) (h : s = t)
    (U : Y.Opens) (v : SectionsOn (tangentSheaf s) U)
    (a : SectionsOn (cotangentSheaf t) U) :
    (dualEvaluation (cotangentSheaf t)).apply U
        ((eqToHom (congrArg tangentSheaf h)).app U v) a =
      (dualEvaluation (cotangentSheaf s)).apply U v
        ((eqToHom (congrArg cotangentSheaf h.symm)).app U a) := by
  subst t
  rfl

theorem tangentMapRaw_evaluate {Y Z S : Scheme} (f : Y ⟶ Z) (s : Z ⟶ S)
    (U : Y.Opens) (v : SectionsOn (tangentSheaf (f ≫ s)) U)
    (a : SectionsOn (pullbackModule f (cotangentSheaf s)) U) :
    (dualEvaluation (pullbackModule f (cotangentSheaf s))).apply U
        ((tangentMapRaw f s).app U v) a =
      (dualEvaluation (cotangentSheaf (f ≫ s))).apply U v
        ((cotangentMap f s).app U a) := by
  let k := tensorMap (𝟙 (tangentSheaf (f ≫ s))) (cotangentMap f s) ≫
    (internalHomPresentation (cotangentSheaf (f ≫ s)) (structureModule Y)).evaluate
  have h := congrArg (fun m :
      tensorSheaf (tangentSheaf (f ≫ s)) (pullbackModule f (cotangentSheaf s)) ⟶
        structureModule Y => m.app U
      ((tensorPresentation (tangentSheaf (f ≫ s))
        (pullbackModule f (cotangentSheaf s))).pair.apply U v a))
    (currySheaf_evaluate k)
  change (internalHomPresentation (pullbackModule f (cotangentSheaf s))
      (structureModule Y)).evaluate.app U
    ((tensorMap (currySheaf k) (𝟙 _)).app U
      ((tensorPresentation (tangentSheaf (f ≫ s))
        (pullbackModule f (cotangentSheaf s))).pair.apply U v a)) =
    (internalHomPresentation (cotangentSheaf (f ≫ s)) (structureModule Y)).evaluate.app U
      ((tensorMap (𝟙 (tangentSheaf (f ≫ s))) (cotangentMap f s)).app U
        ((tensorPresentation (tangentSheaf (f ≫ s))
          (pullbackModule f (cotangentSheaf s))).pair.apply U v a)) at h
  rw [tensorMap_apply, tensorMap_apply] at h
  exact h

theorem unitPullbackMap_pullLocalSection {Y Z : Scheme} (f : Y ⟶ Z)
    (U : Z.Opens) (a : RingSections Z U) :
    (unitPullbackMap f).app (f ⁻¹ᵁ U)
      (pullLocalSection f (structureModule Z) U a) = f.app U a := by
  exact congrArg (fun h : structureModule Z ⟶
    (Scheme.Modules.pushforward f).obj (structureModule Y) => h.app U a)
      (unitPullbackMap_adjoint f)

theorem dualBaseChange_evaluate {Y Z : Scheme} (f : Y ⟶ Z)
    (E : OModule Z) (U : Y.Opens)
    (v : SectionsOn (pullbackModule f (dualSheaf E)) U)
    (a : SectionsOn (pullbackModule f E) U) :
    (dualEvaluation (pullbackModule f E)).apply U
        ((dualBaseChange f E).app U v) a =
      (unitPullbackMap f).app U ((pullbackPair f (dualEvaluation E)).apply U v a) := by
  let b := (pullbackPair f (dualEvaluation E)).postcompose (unitPullbackMap f)
  have h := congrArg (fun k :
      tensorSheaf (pullbackModule f (dualSheaf E)) (pullbackModule f E) ⟶
        structureModule Y => k.app U
      ((tensorPresentation (pullbackModule f (dualSheaf E))
        (pullbackModule f E)).pair.apply U v a))
    (currySheaf_evaluate (tensorLift b))
  change (internalHomPresentation (pullbackModule f E) (structureModule Y)).evaluate.app U
      ((tensorMap (currySheaf (tensorLift b)) (𝟙 (pullbackModule f E))).app U
        ((tensorPresentation (pullbackModule f (dualSheaf E))
          (pullbackModule f E)).pair.apply U v a)) = _ at h
  rw [tensorMap_apply] at h
  have hb := congrArg (fun q :
      SheafBilinearMap (pullbackModule f (dualSheaf E)) (pullbackModule f E)
        (structureModule Y) => q.apply U v a) (tensorLift_pair b)
  exact h.trans hb

/-- The canonical dual comparison evaluated on actual pulled local sections. -/
theorem dualBaseChange_pullLocalSection {Y Z : Scheme} (f : Y ⟶ Z)
    (E : OModule Z) (U : Z.Opens)
    (v : SectionsOn (dualSheaf E) U) (a : SectionsOn E U) :
    (dualEvaluation (pullbackModule f E)).apply (f ⁻¹ᵁ U)
        ((dualBaseChange f E).app (f ⁻¹ᵁ U)
          (pullLocalSection f (dualSheaf E) U v))
        (pullLocalSection f E U a) =
      f.app U ((dualEvaluation E).apply U v a) := by
  calc
    _ = (unitPullbackMap f).app (f ⁻¹ᵁ U)
        ((pullbackPair f (dualEvaluation E)).apply (f ⁻¹ᵁ U)
          (pullLocalSection f (dualSheaf E) U v) (pullLocalSection f E U a)) :=
      dualBaseChange_evaluate f E (f ⁻¹ᵁ U)
        (pullLocalSection f (dualSheaf E) U v) (pullLocalSection f E U a)
    _ = (unitPullbackMap f).app (f ⁻¹ᵁ U)
        (pullLocalSection f (structureModule Z) U ((dualEvaluation E).apply U v a)) :=
      congrArg (fun z : SectionsOn (pullbackModule f (structureModule Z)) (f ⁻¹ᵁ U) =>
        (unitPullbackMap f).app (f ⁻¹ᵁ U) z)
        (pullbackPair_normalized f (dualEvaluation E) U v a)
    _ = _ := unitPullbackMap_pullLocalSection f U ((dualEvaluation E).apply U v a)

/-- The derivative of the identity uses the canonical pullback identity
comparison, as follows from its action on the universal differentials. -/
theorem cotangentMap_id {Y S : Scheme} (s : Y ⟶ S) :
    cotangentMap (𝟙 Y) s ≫
        eqToHom (congrArg cotangentSheaf (Category.id_comp s)) =
      (Scheme.Modules.pullbackId Y).hom.app (cotangentSheaf s) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 Y)).homEquiv _ _).injective
  apply ((cotangentPresentation s).universal _).1
  apply relativeDerivation_ext
  intro U a
  change (eqToHom (congrArg cotangentSheaf (Category.id_comp s))).app ((𝟙 Y) ⁻¹ᵁ U)
      ((cotangentMap (𝟙 Y) s).app ((𝟙 Y) ⁻¹ᵁ U)
        (pullLocalSection (𝟙 Y) (cotangentSheaf s) U
          ((cotangentPresentation s).differential.apply U a))) =
    ((Scheme.Modules.pullbackId Y).hom.app (cotangentSheaf s)).app ((𝟙 Y) ⁻¹ᵁ U)
      (pullLocalSection (𝟙 Y) (cotangentSheaf s) U
        ((cotangentPresentation s).differential.apply U a))
  rw [cotangentMap_differential,
    differential_transport ((𝟙 Y) ≫ s) s (Category.id_comp s)]
  exact (ExternalExchangeCoherenceProof.pullLocalSection_id (cotangentSheaf s) U
    ((cotangentPresentation s).differential.apply U a)).symm

theorem dual_uncurry_apply {Y : Scheme} {E F : OModule Y}
    (a : E ⟶ dualSheaf F) (U : Y.Opens)
    (v : SectionsOn E U) (w : SectionsOn F U) :
    (tensorMap a (𝟙 F) ≫ (internalHomPresentation F (structureModule Y)).evaluate).app U
        ((tensorPresentation E F).pair.apply U v w) =
      (dualEvaluation F).apply U (a.app U v) w := by
  change (internalHomPresentation F (structureModule Y)).evaluate.app U
    ((tensorMap a (𝟙 F)).app U ((tensorPresentation E F).pair.apply U v w)) = _
  rw [tensorMap_apply]
  rfl

theorem dual_hom_ext {Y : Scheme} {E F : OModule Y}
    (a b : E ⟶ dualSheaf F)
    (h : ∀ U v w, (dualEvaluation F).apply U (a.app U v) w =
      (dualEvaluation F).apply U (b.app U v) w) : a = b := by
  apply (internalHomPresentation F (structureModule Y)).hom_ext
  apply ((tensorPresentation E F).universal _).1
  apply sheafBilinearMap_ext
  intro U v w
  change (tensorMap a (𝟙 F) ≫ (internalHomPresentation F (structureModule Y)).evaluate).app U
      ((tensorPresentation E F).pair.apply U v w) =
    (tensorMap b (𝟙 F) ≫ (internalHomPresentation F (structureModule Y)).evaluate).app U
      ((tensorPresentation E F).pair.apply U v w)
  rw [dual_uncurry_apply, dual_uncurry_apply]
  exact h U v w

theorem dual_pullback_hom_ext {Y Z : Scheme} (f : Y ⟶ Z)
    (E F : OModule Z)
    (a b : pullbackModule f E ⟶ dualSheaf (pullbackModule f F))
    (h : ∀ U v w,
      (dualEvaluation (pullbackModule f F)).apply (f ⁻¹ᵁ U)
        (a.app (f ⁻¹ᵁ U) (pullLocalSection f E U v)) (pullLocalSection f F U w) =
      (dualEvaluation (pullbackModule f F)).apply (f ⁻¹ᵁ U)
        (b.app (f ⁻¹ᵁ U) (pullLocalSection f E U v)) (pullLocalSection f F U w)) : a = b := by
  apply (internalHomPresentation (pullbackModule f F) (structureModule Y)).hom_ext
  apply ((tensorPresentation (pullbackModule f E) (pullbackModule f F)).universal _).1
  apply TensorPullbackComparisonProof.bilinear_pullback_ext f
  intro U v w
  change (tensorMap a (𝟙 (pullbackModule f F)) ≫
      (internalHomPresentation (pullbackModule f F) (structureModule Y)).evaluate).app (f ⁻¹ᵁ U)
      ((tensorPresentation (pullbackModule f E) (pullbackModule f F)).pair.apply (f ⁻¹ᵁ U)
        (pullLocalSection f E U v) (pullLocalSection f F U w)) =
    (tensorMap b (𝟙 (pullbackModule f F)) ≫
      (internalHomPresentation (pullbackModule f F) (structureModule Y)).evaluate).app (f ⁻¹ᵁ U)
      ((tensorPresentation (pullbackModule f E) (pullbackModule f F)).pair.apply (f ⁻¹ᵁ U)
        (pullLocalSection f E U v) (pullLocalSection f F U w))
  rw [dual_uncurry_apply, dual_uncurry_apply]
  exact h U v w

theorem tangentMapRaw_id_baseChange {Y S : Scheme} (s : Y ⟶ S) :
    (Scheme.Modules.pullbackId Y).hom.app (tangentSheaf s) ≫
        eqToHom (congrArg tangentSheaf (Category.id_comp s).symm) ≫
        tangentMapRaw (𝟙 Y) s =
      dualBaseChange (𝟙 Y) (cotangentSheaf s) := by
  apply dual_pullback_hom_ext (𝟙 Y) (tangentSheaf s) (cotangentSheaf s)
  intro U v a
  let V : Y.Opens := (𝟙 Y) ⁻¹ᵁ U
  let pv : SectionsOn (pullbackModule (𝟙 Y) (tangentSheaf s)) V :=
    pullLocalSection (𝟙 Y) (tangentSheaf s) U v
  let pa : SectionsOn (pullbackModule (𝟙 Y) (cotangentSheaf s)) V :=
    pullLocalSection (𝟙 Y) (cotangentSheaf s) U a
  have hv : ((Scheme.Modules.pullbackId Y).hom.app (tangentSheaf s)).app V pv = v :=
    ExternalExchangeCoherenceProof.pullLocalSection_id (tangentSheaf s) U v
  have ha : ((Scheme.Modules.pullbackId Y).hom.app (cotangentSheaf s)).app V pa = a :=
    ExternalExchangeCoherenceProof.pullLocalSection_id (cotangentSheaf s) U a
  have hc : (eqToHom (congrArg cotangentSheaf (Category.id_comp s))).app V
      ((cotangentMap (𝟙 Y) s).app V pa) = a := by
    have h := congrArg (fun k : pullbackModule (𝟙 Y) (cotangentSheaf s) ⟶
        cotangentSheaf s => k.app V pa) (cotangentMap_id s)
    exact h.trans ha
  change (dualEvaluation (pullbackModule (𝟙 Y) (cotangentSheaf s))).apply V
      ((tangentMapRaw (𝟙 Y) s).app V
        ((eqToHom (congrArg tangentSheaf (Category.id_comp s).symm)).app V
          (((Scheme.Modules.pullbackId Y).hom.app (tangentSheaf s)).app V pv))) pa =
    (dualEvaluation (pullbackModule (𝟙 Y) (cotangentSheaf s))).apply V
      ((dualBaseChange (𝟙 Y) (cotangentSheaf s)).app V pv) pa
  calc
    _ = (dualEvaluation (cotangentSheaf ((𝟙 Y) ≫ s))).apply V
        ((eqToHom (congrArg tangentSheaf (Category.id_comp s).symm)).app V
          (((Scheme.Modules.pullbackId Y).hom.app (tangentSheaf s)).app V pv))
        ((cotangentMap (𝟙 Y) s).app V pa) :=
      tangentMapRaw_evaluate (𝟙 Y) s V
        ((eqToHom (congrArg tangentSheaf (Category.id_comp s).symm)).app V
          (((Scheme.Modules.pullbackId Y).hom.app (tangentSheaf s)).app V pv)) pa
    _ = (dualEvaluation (cotangentSheaf s)).apply V
        (((Scheme.Modules.pullbackId Y).hom.app (tangentSheaf s)).app V pv)
        ((eqToHom (congrArg cotangentSheaf (Category.id_comp s))).app V
          ((cotangentMap (𝟙 Y) s).app V pa)) :=
      dualEvaluation_transport s ((𝟙 Y) ≫ s) (Category.id_comp s).symm V
        (((Scheme.Modules.pullbackId Y).hom.app (tangentSheaf s)).app V pv)
        ((cotangentMap (𝟙 Y) s).app V pa)
    _ = (dualEvaluation (cotangentSheaf s)).apply U v a :=
      congrArg₂ (fun (v' : SectionsOn (tangentSheaf s) V)
        (a' : SectionsOn (cotangentSheaf s) V) =>
          (dualEvaluation (cotangentSheaf s)).apply V v' a') hv hc
    _ = _ := (dualBaseChange_pullLocalSection (𝟙 Y) (cotangentSheaf s) U v a).symm

/-- Dualizing the actual invertible cotangent map gives the actual raw
derivative. The internal-Hom comparison is normalized by evaluation. -/
theorem tangentMapRaw_isIso {X Y S : Scheme} (f : X ⟶ Y) [IsIso f]
    (s : Y ⟶ S) : IsIso (tangentMapRaw f s) := by
  letI := openImmersion_cotangentMap_isIso f s
  let H := internalHomPresentation (cotangentSheaf (f ≫ s)) (structureModule X)
  let K := internalHomPresentation (pullbackModule f (cotangentSheaf s))
    (structureModule X)
  let e := H.mapIso K (asIso (cotangentMap f s)).symm (Iso.refl (structureModule X))
  have he : tangentMapRaw f s = e.hom := by
    change currySheaf
        (tensorMap (𝟙 (tangentSheaf (f ≫ s))) (cotangentMap f s) ≫ H.evaluate) =
      K.curry (tensorMap (𝟙 (tangentSheaf (f ≫ s))) (cotangentMap f s) ≫
        H.evaluate ≫ 𝟙 (structureModule X))
    rw [Category.comp_id]
    rfl
  rw [he]
  infer_instance

/-- The supplied equality over the base changes only the source object;
all three factors of the derivative of an isomorphism are invertible. -/
theorem differentialOver_isIso {d e : ℕ} (X : SmoothProperComplexVariety d)
    (Y : SmoothProperComplexVariety e) (f : X.scheme ⟶ Y.scheme) [IsIso f]
    (hf : f ≫ Y.structureMap = X.structureMap) :
    IsIso (differentialOver X Y f hf) := by
  letI := dualBaseChange_isIso f (smooth_cotangent_rank Y.structureMap e Y.smooth)
  letI := tangentMapRaw_isIso f Y.structureMap
  unfold differentialOver
  infer_instance

/-- The identity law for the original derivative, including its specified
unit-pullback and dual-base-change comparisons. -/
theorem differentialOver_id {d : ℕ} (X : SmoothProperComplexVariety d) :
    differentialOver X X (𝟙 X.scheme) (Category.id_comp X.structureMap) =
      (Scheme.Modules.pullbackId X.scheme).inv.app (tangentSheaf X.structureMap) := by
  letI := dualBaseChange_isIso (𝟙 X.scheme)
    (smooth_cotangent_rank X.structureMap d X.smooth)
  apply (cancel_mono (dualBaseChange (𝟙 X.scheme)
    (cotangentSheaf X.structureMap))).1
  simp only [differentialOver, Category.assoc, asIso_inv, IsIso.inv_hom_id,
    Category.comp_id]
  rw [← tangentMapRaw_id_baseChange X.structureMap]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Functor.id_obj, Category.id_comp]

/-- The contravariant map on actual dual sheaves, fixed by evaluation. -/
def dualMap {Y : Scheme} {E F : OModule Y} (a : E ⟶ F) :
    dualSheaf F ⟶ dualSheaf E :=
  currySheaf (tensorMap (𝟙 (dualSheaf F)) a ≫
    (internalHomPresentation F (structureModule Y)).evaluate)

theorem dualMap_evaluate {Y : Scheme} {E F : OModule Y} (a : E ⟶ F)
    (U : Y.Opens) (v : SectionsOn (dualSheaf F) U) (w : SectionsOn E U) :
    (dualEvaluation E).apply U ((dualMap a).app U v) w =
      (dualEvaluation F).apply U v (a.app U w) := by
  let k := tensorMap (𝟙 (dualSheaf F)) a ≫
    (internalHomPresentation F (structureModule Y)).evaluate
  have h := congrArg (fun q : tensorSheaf (dualSheaf F) E ⟶ structureModule Y =>
      q.app U ((tensorPresentation (dualSheaf F) E).pair.apply U v w))
    (currySheaf_evaluate k)
  rw [dual_uncurry_apply] at h
  change (dualEvaluation E).apply U ((dualMap a).app U v) w =
    (internalHomPresentation F (structureModule Y)).evaluate.app U
      ((tensorMap (𝟙 (dualSheaf F)) a).app U
        ((tensorPresentation (dualSheaf F) E).pair.apply U v w)) at h
  rw [tensorMap_apply] at h
  exact h

theorem dualMap_id {Y : Scheme} (E : OModule Y) :
    dualMap (𝟙 E) = 𝟙 (dualSheaf E) := by
  apply dual_hom_ext
  intro U v w
  rw [dualMap_evaluate]
  rfl

theorem dualMap_comp {Y : Scheme} {E F G : OModule Y}
    (a : E ⟶ F) (b : F ⟶ G) : dualMap (a ≫ b) = dualMap b ≫ dualMap a := by
  apply dual_hom_ext
  intro U v w
  change (dualEvaluation E).apply U ((dualMap (a ≫ b)).app U v) w =
    (dualEvaluation E).apply U ((dualMap a).app U ((dualMap b).app U v)) w
  rw [dualMap_evaluate, dualMap_evaluate, dualMap_evaluate]
  rfl

theorem dualMap_eqToHom {Y : Scheme} {E F : OModule Y} (h : E = F) :
    dualMap (eqToHom h) = eqToHom (congrArg dualSheaf h.symm) := by
  subst F
  exact dualMap_id E

/-- Dual base change is natural in the actual sheaf map. -/
@[reassoc]
theorem dualBaseChange_naturality {Y Z : Scheme} (f : Y ⟶ Z)
    {E F : OModule Z} (a : E ⟶ F) :
    (Scheme.Modules.pullback f).map (dualMap a) ≫ dualBaseChange f E =
      dualBaseChange f F ≫ dualMap ((Scheme.Modules.pullback f).map a) := by
  apply dual_pullback_hom_ext f (dualSheaf F) E
  intro U v w
  change (dualEvaluation (pullbackModule f E)).apply (f ⁻¹ᵁ U)
      ((dualBaseChange f E).app (f ⁻¹ᵁ U)
        (((Scheme.Modules.pullback f).map (dualMap a)).app (f ⁻¹ᵁ U)
          (pullLocalSection f (dualSheaf F) U v))) (pullLocalSection f E U w) =
    (dualEvaluation (pullbackModule f E)).apply (f ⁻¹ᵁ U)
      ((dualMap ((Scheme.Modules.pullback f).map a)).app (f ⁻¹ᵁ U)
        ((dualBaseChange f F).app (f ⁻¹ᵁ U) (pullLocalSection f (dualSheaf F) U v)))
      (pullLocalSection f E U w)
  rw [ExternalExchangeCoherenceProof.pullLocalSection_map, dualBaseChange_evaluate,
    pullbackPair_normalized, unitPullbackMap_pullLocalSection, dualMap_evaluate,
    dualMap_evaluate, ExternalExchangeCoherenceProof.pullLocalSection_map,
    dualBaseChange_evaluate, pullbackPair_normalized, unitPullbackMap_pullLocalSection]

/-- The canonical dual comparison respects composition of actual pullbacks. -/
@[reassoc]
theorem dualBaseChange_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (E : OModule Z) :
    (Scheme.Modules.pullbackComp f g).hom.app (dualSheaf E) ≫
        dualBaseChange (f ≫ g) E =
      (Scheme.Modules.pullback f).map (dualBaseChange g E) ≫
        dualBaseChange f (pullbackModule g E) ≫
          dualMap ((Scheme.Modules.pullbackComp f g).inv.app E) := by
  apply (cancel_epi ((Scheme.Modules.pullbackComp f g).inv.app (dualSheaf E))).1
  apply dual_pullback_hom_ext (f ≫ g) (dualSheaf E) E
  intro U v w
  let V : Y.Opens := g ⁻¹ᵁ U
  let W : X.Opens := (f ≫ g) ⁻¹ᵁ U
  let vY : SectionsOn (pullbackModule g (dualSheaf E)) V :=
    pullLocalSection g (dualSheaf E) U v
  let wY : SectionsOn (pullbackModule g E) V := pullLocalSection g E U w
  let vX : SectionsOn (pullbackModule (f ≫ g) (dualSheaf E)) W :=
    pullLocalSection (f ≫ g) (dualSheaf E) U v
  let wX : SectionsOn (pullbackModule (f ≫ g) E) W :=
    pullLocalSection (f ≫ g) E U w
  let vv : SectionsOn (pullbackModule f (pullbackModule g (dualSheaf E))) W :=
    pullLocalSection f (pullbackModule g (dualSheaf E)) V vY
  let ww : SectionsOn (pullbackModule f (pullbackModule g E)) W :=
    pullLocalSection f (pullbackModule g E) V wY
  have hv : ((Scheme.Modules.pullbackComp f g).inv.app (dualSheaf E)).app W vX = vv :=
    ExternalExchangeCoherenceProof.pullLocalSection_comp_inv f g (dualSheaf E) U v
  have hw : ((Scheme.Modules.pullbackComp f g).inv.app E).app W wX = ww :=
    ExternalExchangeCoherenceProof.pullLocalSection_comp_inv f g E U w
  have hcancel : ((Scheme.Modules.pullbackComp f g).hom.app (dualSheaf E)).app W
      (((Scheme.Modules.pullbackComp f g).inv.app (dualSheaf E)).app W vX) = vX :=
    ExternalExchangeCoherenceProof.iso_hom_inv_app
      ((Scheme.Modules.pullbackComp f g).app (dualSheaf E)) W vX
  have hmap : ((Scheme.Modules.pullback f).map (dualBaseChange g E)).app W vv =
      pullLocalSection f (dualSheaf (pullbackModule g E)) V
        ((dualBaseChange g E).app V vY) :=
    ExternalExchangeCoherenceProof.pullLocalSection_map f (dualBaseChange g E) V vY
  have hleft : (dualEvaluation (pullbackModule (f ≫ g) E)).apply W
      ((dualBaseChange (f ≫ g) E).app W
        (((Scheme.Modules.pullbackComp f g).hom.app (dualSheaf E)).app W
          (((Scheme.Modules.pullbackComp f g).inv.app (dualSheaf E)).app W vX))) wX =
      (f ≫ g).app U ((dualEvaluation E).apply U v w) :=
    (congrArg (fun z : SectionsOn (pullbackModule (f ≫ g) (dualSheaf E)) W =>
      (dualEvaluation (pullbackModule (f ≫ g) E)).apply W
        ((dualBaseChange (f ≫ g) E).app W z) wX) hcancel).trans
      (dualBaseChange_pullLocalSection (f ≫ g) E U v w)
  have hright : (dualEvaluation (pullbackModule (f ≫ g) E)).apply W
      ((dualMap ((Scheme.Modules.pullbackComp f g).inv.app E)).app W
        ((dualBaseChange f (pullbackModule g E)).app W
          (((Scheme.Modules.pullback f).map (dualBaseChange g E)).app W
            (((Scheme.Modules.pullbackComp f g).inv.app (dualSheaf E)).app W vX)))) wX =
      (f ≫ g).app U ((dualEvaluation E).apply U v w) := by
    calc
      _ = (dualEvaluation (pullbackModule f (pullbackModule g E))).apply W
          ((dualBaseChange f (pullbackModule g E)).app W
            (((Scheme.Modules.pullback f).map (dualBaseChange g E)).app W
              (((Scheme.Modules.pullbackComp f g).inv.app (dualSheaf E)).app W vX)))
          (((Scheme.Modules.pullbackComp f g).inv.app E).app W wX) :=
        dualMap_evaluate ((Scheme.Modules.pullbackComp f g).inv.app E) W
          ((dualBaseChange f (pullbackModule g E)).app W
            (((Scheme.Modules.pullback f).map (dualBaseChange g E)).app W
              (((Scheme.Modules.pullbackComp f g).inv.app (dualSheaf E)).app W vX))) wX
      _ = (dualEvaluation (pullbackModule f (pullbackModule g E))).apply W
          ((dualBaseChange f (pullbackModule g E)).app W
            (((Scheme.Modules.pullback f).map (dualBaseChange g E)).app W vv)) ww :=
        congrArg₂ (fun (z : SectionsOn (pullbackModule f (pullbackModule g (dualSheaf E))) W)
          (a : SectionsOn (pullbackModule f (pullbackModule g E)) W) =>
            (dualEvaluation (pullbackModule f (pullbackModule g E))).apply W
              ((dualBaseChange f (pullbackModule g E)).app W
                (((Scheme.Modules.pullback f).map (dualBaseChange g E)).app W z)) a) hv hw
      _ = (dualEvaluation (pullbackModule f (pullbackModule g E))).apply W
          ((dualBaseChange f (pullbackModule g E)).app W
            (pullLocalSection f (dualSheaf (pullbackModule g E)) V
              ((dualBaseChange g E).app V vY))) ww :=
        congrArg (fun z : SectionsOn (pullbackModule f (dualSheaf (pullbackModule g E))) W =>
          (dualEvaluation (pullbackModule f (pullbackModule g E))).apply W
            ((dualBaseChange f (pullbackModule g E)).app W z) ww) hmap
      _ = f.app V ((dualEvaluation (pullbackModule g E)).apply V
          ((dualBaseChange g E).app V vY) wY) :=
        dualBaseChange_pullLocalSection f (pullbackModule g E) V
          ((dualBaseChange g E).app V vY) wY
      _ = f.app V (g.app U ((dualEvaluation E).apply U v w)) :=
        congrArg (fun a : RingSections Y V => f.app V a)
          (dualBaseChange_pullLocalSection g E U v w)
      _ = _ := rfl
  change (dualEvaluation (pullbackModule (f ≫ g) E)).apply W
      ((dualBaseChange (f ≫ g) E).app W
        (((Scheme.Modules.pullbackComp f g).hom.app (dualSheaf E)).app W
          (((Scheme.Modules.pullbackComp f g).inv.app (dualSheaf E)).app W vX))) wX =
    (dualEvaluation (pullbackModule (f ≫ g) E)).apply W
      ((dualMap ((Scheme.Modules.pullbackComp f g).inv.app E)).app W
        ((dualBaseChange f (pullbackModule g E)).app W
          (((Scheme.Modules.pullback f).map (dualBaseChange g E)).app W
            (((Scheme.Modules.pullbackComp f g).inv.app (dualSheaf E)).app W vX)))) wX
  exact hleft.trans hright.symm

/-- The actual cotangent map with precisely the supplied base equality. -/
def cotangentOver {d e : ℕ} (X : SmoothProperComplexVariety d)
    (Y : SmoothProperComplexVariety e) (f : X.scheme ⟶ Y.scheme)
    (hf : f ≫ Y.structureMap = X.structureMap) :
    pullbackModule f (cotangentSheaf Y.structureMap) ⟶ cotangentSheaf X.structureMap :=
  cotangentMap f Y.structureMap ≫ eqToHom (congrArg cotangentSheaf hf)

theorem cotangentOver_differential {d e : ℕ} (X : SmoothProperComplexVariety d)
    (Y : SmoothProperComplexVariety e) (f : X.scheme ⟶ Y.scheme)
    (hf : f ≫ Y.structureMap = X.structureMap)
    (U : Y.scheme.Opens) (a : RingSections Y.scheme U) :
    (cotangentOver X Y f hf).app (f ⁻¹ᵁ U)
        (pullLocalSection f (cotangentSheaf Y.structureMap) U
          ((cotangentPresentation Y.structureMap).differential.apply U a)) =
      (cotangentPresentation X.structureMap).differential.apply (f ⁻¹ᵁ U) (f.app U a) := by
  change (eqToHom (congrArg cotangentSheaf hf)).app (f ⁻¹ᵁ U)
    ((cotangentMap f Y.structureMap).app (f ⁻¹ᵁ U)
      (pullLocalSection f (cotangentSheaf Y.structureMap) U
        ((cotangentPresentation Y.structureMap).differential.apply U a))) = _
  rw [cotangentMap_differential]
  exact differential_transport (f ≫ Y.structureMap) X.structureMap hf
    (f ⁻¹ᵁ U) (f.app U a)

theorem cotangentOver_comp {d e k : ℕ} (X : SmoothProperComplexVariety d)
    (Y : SmoothProperComplexVariety e) (Z : SmoothProperComplexVariety k)
    (f : X.scheme ⟶ Y.scheme) (g : Y.scheme ⟶ Z.scheme)
    (hf : f ≫ Y.structureMap = X.structureMap)
    (hg : g ≫ Z.structureMap = Y.structureMap)
    (hfg : (f ≫ g) ≫ Z.structureMap = X.structureMap) :
    (Scheme.Modules.pullbackComp f g).hom.app (cotangentSheaf Z.structureMap) ≫
        cotangentOver X Z (f ≫ g) hfg =
      (Scheme.Modules.pullback f).map (cotangentOver Y Z g hg) ≫
        cotangentOver X Y f hf := by
  apply (cancel_epi ((Scheme.Modules.pullbackComp f g).inv.app
    (cotangentSheaf Z.structureMap))).1
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  apply ((cotangentPresentation Z.structureMap).universal _).1
  apply relativeDerivation_ext
  intro U a
  change (cotangentOver X Z (f ≫ g) hfg).app ((f ≫ g) ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackComp f g).hom.app (cotangentSheaf Z.structureMap)).app
        ((f ≫ g) ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackComp f g).inv.app (cotangentSheaf Z.structureMap)).app
          ((f ≫ g) ⁻¹ᵁ U)
          (pullLocalSection (f ≫ g) (cotangentSheaf Z.structureMap) U
            ((cotangentPresentation Z.structureMap).differential.apply U a)))) =
    (cotangentOver X Y f hf).app ((f ≫ g) ⁻¹ᵁ U)
      (((Scheme.Modules.pullback f).map (cotangentOver Y Z g hg)).app ((f ≫ g) ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackComp f g).inv.app (cotangentSheaf Z.structureMap)).app
          ((f ≫ g) ⁻¹ᵁ U)
          (pullLocalSection (f ≫ g) (cotangentSheaf Z.structureMap) U
            ((cotangentPresentation Z.structureMap).differential.apply U a))))
  have hcancel := ExternalExchangeCoherenceProof.iso_hom_inv_app
    ((Scheme.Modules.pullbackComp f g).app (cotangentSheaf Z.structureMap))
    ((f ≫ g) ⁻¹ᵁ U)
    (pullLocalSection (f ≫ g) (cotangentSheaf Z.structureMap) U
      ((cotangentPresentation Z.structureMap).differential.apply U a))
  simp only [Iso.app_hom, Iso.app_inv] at hcancel
  rw [hcancel, cotangentOver_differential,
    ExternalExchangeCoherenceProof.pullLocalSection_comp_inv]
  simp only [Scheme.Hom.comp_preimage]
  erw [ExternalExchangeCoherenceProof.pullLocalSection_map, cotangentOver_differential,
    cotangentOver_differential] <;> rfl

theorem differentialOver_dual {d e : ℕ} (X : SmoothProperComplexVariety d)
    (Y : SmoothProperComplexVariety e) (f : X.scheme ⟶ Y.scheme)
    (hf : f ≫ Y.structureMap = X.structureMap)
    [IsIso (dualBaseChange f (cotangentSheaf Y.structureMap))] :
    differentialOver X Y f hf =
      dualMap (cotangentOver X Y f hf) ≫ inv (dualBaseChange f (cotangentSheaf Y.structureMap)) := by
  rw [cotangentOver, dualMap_comp, dualMap_eqToHom, Category.assoc]
  rfl

/-- Chain rule for the original derivative, retaining the canonical
composition comparison of the pullback functors. -/
theorem differentialOver_comp {d e k : ℕ} (X : SmoothProperComplexVariety d)
    (Y : SmoothProperComplexVariety e) (Z : SmoothProperComplexVariety k)
    (f : X.scheme ⟶ Y.scheme) (g : Y.scheme ⟶ Z.scheme)
    (hf : f ≫ Y.structureMap = X.structureMap)
    (hg : g ≫ Z.structureMap = Y.structureMap)
    (hfg : (f ≫ g) ≫ Z.structureMap = X.structureMap) :
    differentialOver X Y f hf ≫
        (Scheme.Modules.pullback f).map (differentialOver Y Z g hg) ≫
        (Scheme.Modules.pullbackComp f g).hom.app (tangentSheaf Z.structureMap) =
      differentialOver X Z (f ≫ g) hfg := by
  letI := dualBaseChange_isIso f (smooth_cotangent_rank Y.structureMap e Y.smooth)
  letI := dualBaseChange_isIso g (smooth_cotangent_rank Z.structureMap k Z.smooth)
  letI := dualBaseChange_isIso (f ≫ g) (smooth_cotangent_rank Z.structureMap k Z.smooth)
  apply (cancel_mono (dualBaseChange (f ≫ g) (cotangentSheaf Z.structureMap))).1
  rw [differentialOver_dual X Y f hf, differentialOver_dual Y Z g hg,
    differentialOver_dual X Z (f ≫ g) hfg]
  simp only [Functor.map_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [dualBaseChange_comp]
  simp only [Functor.map_inv, Category.assoc, IsIso.inv_hom_id_assoc]
  rw [dualBaseChange_naturality_assoc]
  simp only [IsIso.inv_hom_id_assoc]
  rw [← dualMap_comp, ← dualMap_comp]
  have hc := congrArg (fun q =>
      (Scheme.Modules.pullbackComp f g).inv.app (cotangentSheaf Z.structureMap) ≫ q)
    (cotangentOver_comp X Y Z f g hf hg hfg)
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at hc
  exact congrArg dualMap hc.symm

/-- Equality of the underlying morphism changes the derivative only by
the specified equality comparison on its actual pullback. -/
theorem differentialOver_congr {d e : ℕ} (X : SmoothProperComplexVariety d)
    (Y : SmoothProperComplexVariety e) {f g : X.scheme ⟶ Y.scheme} (h : f = g)
    (hf : f ≫ Y.structureMap = X.structureMap)
    (hg : g ≫ Y.structureMap = X.structureMap) :
    differentialOver X Y f hf ≫
        (Scheme.Modules.pullbackCongr h).hom.app (tangentSheaf Y.structureMap) =
      differentialOver X Y g hg := by
  subst g
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id]

end ContactDerivativeIsoProof

end ContactDerivativeIsoSection

/-- Contact isomorphism with the ACTUAL derivative, not a chosen tangent
isomorphism. The line quotient is induced later by exactness. -/
structure ContactIso {n : ℕ} (X Y : SmoothProperComplexVariety (2*n+1))
    (C : IntrinsicContactStructure X) (D : IntrinsicContactStructure Y) where
  schemeIso : X.scheme ≅ Y.scheme
  overC : schemeIso.hom ≫ Y.structureMap = X.structureMap
  distributionIso : C.sequence.distribution.sheaf ≅
    pullbackModule schemeIso.hom D.sequence.distribution.sheaf
  preserves : C.sequence.inclusion ≫ differentialOver X Y schemeIso.hom overC =
    distributionIso.hom ≫ (Scheme.Modules.pullback schemeIso.hom).map D.sequence.inclusion

theorem contactIso_refl {n : ℕ} (X : SmoothProperComplexVariety (2*n+1))
    (C : IntrinsicContactStructure X) : Nonempty (ContactIso X X C C) := by
  refine ⟨{ schemeIso := Iso.refl X.scheme
            overC := Category.id_comp X.structureMap
            distributionIso := ((Scheme.Modules.pullbackId X.scheme).app
              C.sequence.distribution.sheaf).symm
            preserves := ?_ }⟩
  change C.sequence.inclusion ≫
      differentialOver X X (𝟙 X.scheme) (Category.id_comp X.structureMap) =
    (Scheme.Modules.pullbackId X.scheme).inv.app C.sequence.distribution.sheaf ≫
      (Scheme.Modules.pullback (𝟙 X.scheme)).map C.sequence.inclusion
  rw [ContactDerivativeIsoProof.differentialOver_id]
  exact (Scheme.Modules.pullbackId X.scheme).inv.naturality C.sequence.inclusion

set_option backward.isDefEq.respectTransparency false in
theorem contactIso_symm {n : ℕ} {X Y : SmoothProperComplexVariety (2*n+1)}
    {C : IntrinsicContactStructure X} {D : IntrinsicContactStructure Y}
    (f : ContactIso X Y C D) : Nonempty (ContactIso Y X D C) := by
  let G := Scheme.Modules.pullback f.schemeIso.inv
  let F := Scheme.Modules.pullback f.schemeIso.hom
  let e : F ⋙ G ≅ 𝟭 Y.scheme.Modules :=
    Scheme.Modules.pullbackComp f.schemeIso.inv f.schemeIso.hom ≪≫
      Scheme.Modules.pullbackCongr f.schemeIso.inv_hom_id ≪≫
        Scheme.Modules.pullbackId Y.scheme
  have hg : f.schemeIso.inv ≫ X.structureMap = Y.structureMap := by
    rw [← f.overC, ← Category.assoc, f.schemeIso.inv_hom_id, Category.id_comp]
  have hgf : (f.schemeIso.inv ≫ f.schemeIso.hom) ≫ Y.structureMap = Y.structureMap := by
    rw [f.schemeIso.inv_hom_id, Category.id_comp]
  have hcomp : differentialOver Y X f.schemeIso.inv hg ≫
      G.map (differentialOver X Y f.schemeIso.hom f.overC) ≫
        e.hom.app (tangentSheaf Y.structureMap) = 𝟙 (tangentSheaf Y.structureMap) := by
    calc
      _ = (differentialOver Y X f.schemeIso.inv hg ≫
          G.map (differentialOver X Y f.schemeIso.hom f.overC) ≫
          (Scheme.Modules.pullbackComp f.schemeIso.inv f.schemeIso.hom).hom.app
            (tangentSheaf Y.structureMap)) ≫
          (Scheme.Modules.pullbackCongr f.schemeIso.inv_hom_id).hom.app
            (tangentSheaf Y.structureMap) ≫
          (Scheme.Modules.pullbackId Y.scheme).hom.app (tangentSheaf Y.structureMap) := by
        simp only [e, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
      _ = differentialOver Y Y (f.schemeIso.inv ≫ f.schemeIso.hom) hgf ≫
          (Scheme.Modules.pullbackCongr f.schemeIso.inv_hom_id).hom.app
            (tangentSheaf Y.structureMap) ≫
          (Scheme.Modules.pullbackId Y.scheme).hom.app (tangentSheaf Y.structureMap) := by
        rw [ContactDerivativeIsoProof.differentialOver_comp Y X Y
          f.schemeIso.inv f.schemeIso.hom hg f.overC hgf]
      _ = differentialOver Y Y (𝟙 Y.scheme) (Category.id_comp Y.structureMap) ≫
          (Scheme.Modules.pullbackId Y.scheme).hom.app (tangentSheaf Y.structureMap) := by
        rw [← Category.assoc, ContactDerivativeIsoProof.differentialOver_congr
          Y Y f.schemeIso.inv_hom_id hgf (Category.id_comp Y.structureMap)]
      _ = 𝟙 (tangentSheaf Y.structureMap) := by
        rw [ContactDerivativeIsoProof.differentialOver_id]
        exact Iso.inv_hom_id_app _ _
  have hd : differentialOver Y X f.schemeIso.inv hg ≫
      G.map (differentialOver X Y f.schemeIso.hom f.overC) =
        e.inv.app (tangentSheaf Y.structureMap) := by
    apply (cancel_mono (e.hom.app (tangentSheaf Y.structureMap))).1
    simpa only [Category.assoc, Iso.inv_hom_id_app, Functor.id_obj] using hcomp
  have hc : f.distributionIso.inv ≫ C.sequence.inclusion ≫
      differentialOver X Y f.schemeIso.hom f.overC = F.map D.sequence.inclusion := by
    rw [f.preserves, ← Category.assoc, f.distributionIso.inv_hom_id, Category.id_comp]
  letI := ContactDerivativeIsoProof.differentialOver_isIso X Y f.schemeIso.hom f.overC
  refine ⟨{ schemeIso := f.schemeIso.symm
            overC := hg
            distributionIso := (e.app D.sequence.distribution.sheaf).symm ≪≫
              G.mapIso f.distributionIso.symm
            preserves := ?_ }⟩
  change D.sequence.inclusion ≫ differentialOver Y X f.schemeIso.inv hg =
    (e.inv.app D.sequence.distribution.sheaf ≫ G.map f.distributionIso.inv) ≫
      G.map C.sequence.inclusion
  apply (cancel_mono (G.map (differentialOver X Y f.schemeIso.hom f.overC))).1
  calc
    _ = D.sequence.inclusion ≫ e.inv.app (tangentSheaf Y.structureMap) := by
      rw [Category.assoc, hd]
    _ = e.inv.app D.sequence.distribution.sheaf ≫ G.map (F.map D.sequence.inclusion) :=
      e.inv.naturality D.sequence.inclusion
    _ = e.inv.app D.sequence.distribution.sheaf ≫
        G.map (f.distributionIso.inv ≫ C.sequence.inclusion ≫
          differentialOver X Y f.schemeIso.hom f.overC) := by rw [hc]
    _ = _ := by simp only [Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem contactIso_trans {n : ℕ} {X Y Z : SmoothProperComplexVariety (2*n+1)}
    {C : IntrinsicContactStructure X} {D : IntrinsicContactStructure Y}
    {E : IntrinsicContactStructure Z}
    (f : ContactIso X Y C D) (g : ContactIso Y Z D E) :
    Nonempty (ContactIso X Z C E) := by
  have hfg : (f.schemeIso.hom ≫ g.schemeIso.hom) ≫ Z.structureMap = X.structureMap := by
    rw [Category.assoc, g.overC, f.overC]
  refine ⟨{ schemeIso := f.schemeIso ≪≫ g.schemeIso
            overC := hfg
            distributionIso := f.distributionIso ≪≫
              (Scheme.Modules.pullback f.schemeIso.hom).mapIso g.distributionIso ≪≫
              (Scheme.Modules.pullbackComp f.schemeIso.hom g.schemeIso.hom).app
                E.sequence.distribution.sheaf
            preserves := ?_ }⟩
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  calc
    _ = (C.sequence.inclusion ≫ differentialOver X Y f.schemeIso.hom f.overC) ≫
        (Scheme.Modules.pullback f.schemeIso.hom).map
          (differentialOver Y Z g.schemeIso.hom g.overC) ≫
        (Scheme.Modules.pullbackComp f.schemeIso.hom g.schemeIso.hom).hom.app
          (tangentSheaf Z.structureMap) := by
      rw [← ContactDerivativeIsoProof.differentialOver_comp X Y Z
        f.schemeIso.hom g.schemeIso.hom f.overC g.overC hfg]
      simp only [Category.assoc]
    _ = f.distributionIso.hom ≫
        (Scheme.Modules.pullback f.schemeIso.hom).map
          (D.sequence.inclusion ≫ differentialOver Y Z g.schemeIso.hom g.overC) ≫
        (Scheme.Modules.pullbackComp f.schemeIso.hom g.schemeIso.hom).hom.app
          (tangentSheaf Z.structureMap) := by
      rw [f.preserves, Functor.map_comp]
      simp only [Category.assoc]
    _ = f.distributionIso.hom ≫
        (Scheme.Modules.pullback f.schemeIso.hom).map
          (g.distributionIso.hom ≫ (Scheme.Modules.pullback g.schemeIso.hom).map
            E.sequence.inclusion) ≫
        (Scheme.Modules.pullbackComp f.schemeIso.hom g.schemeIso.hom).hom.app
          (tangentSheaf Z.structureMap) := by rw [g.preserves]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      simpa only [Category.assoc, Functor.comp_map, Functor.comp_obj,
        pullbackModule, intrinsicTangentBundle] using
        congrArg (fun k => f.distributionIso.hom ≫
          (Scheme.Modules.pullback f.schemeIso.hom).map g.distributionIso.hom ≫ k)
          ((Scheme.Modules.pullbackComp f.schemeIso.hom g.schemeIso.hom).hom.naturality
            E.sequence.inclusion)

set_option backward.isDefEq.respectTransparency false in
theorem contactIso_quotientLine {n : ℕ} {X Y : SmoothProperComplexVariety (2*n+1)}
    {C : IntrinsicContactStructure X} {D : IntrinsicContactStructure Y}
    (f : ContactIso X Y C D) :
    ∃ q : C.sequence.line.sheaf ≅ pullbackModule f.schemeIso.hom D.sequence.line.sheaf,
      C.sequence.form ≫ q.hom = differentialOver X Y f.schemeIso.hom f.overC ≫
        (Scheme.Modules.pullback f.schemeIso.hom).map D.sequence.form := by
  letI := ContactDerivativeIsoProof.differentialOver_isIso X Y f.schemeIso.hom f.overC
  let G := Scheme.Modules.pullback f.schemeIso.hom
  let cc := CokernelCofork.ofπ C.sequence.form C.sequence.comp_zero
  let dd := CokernelCofork.ofπ D.sequence.form D.sequence.comp_zero
  let a : Arrow.mk C.sequence.inclusion ≅ Arrow.mk (G.map D.sequence.inclusion) :=
    Arrow.isoMk f.distributionIso
      (asIso (differentialOver X Y f.schemeIso.hom f.overC)) f.preserves.symm
  let hcc : IsColimit cc := C.sequence.shortExact.gIsCokernel
  let hdd : IsColimit (dd.map G) := dd.mapIsColimit D.sequence.shortExact.gIsCokernel G
  let q := CokernelCofork.mapIsoOfIsColimit hcc hdd a
  refine ⟨q, ?_⟩
  exact CokernelCofork.π_mapOfIsColimit hcc (dd.map G) a.hom

/-! ## B. Test schemes and a genuine relative Hom-space contract -/

/-- A T-valued point over C. ALL schemes are allowed, including nonreduced Artinian tests; C-valued points
alone do not specify a group law, a representing functor, or a deformation space. -/
abbrev PointsOver (T : Scheme) (sT : T ⟶ ComplexBase)
    (X : Scheme) (sX : X ⟶ ComplexBase) :=
  {f : T ⟶ X // f ≫ sX = sT}

def pairOver {T X Y : Scheme} {sT : T ⟶ ComplexBase}
    {sX : X ⟶ ComplexBase} {sY : Y ⟶ ComplexBase}
    (x : PointsOver T sT X sX) (y : PointsOver T sT Y sY) : T ⟶ pullback sX sY :=
  pullback.lift x.val y.val (x.property.trans y.property.symm)

abbrev RationalSourceOver (P : ProjectiveLineOverC) (T : Scheme)
    (sT : T ⟶ ComplexBase) := pullback P.structureMap sT

/-- Base change of a family parameter, with the P1 coordinate fixed. -/
def rationalSourceMap (P : ProjectiveLineOverC)
    {T H : Scheme} {sT : T ⟶ ComplexBase} {sH : H ⟶ ComplexBase}
    (h : PointsOver T sT H sH) :
    RationalSourceOver P T sT ⟶ RationalSourceOver P H sH :=
  pullback.lift (pullback.fst P.structureMap sT)
    (pullback.snd P.structureMap sT ≫ h.val) (by
      simpa [Category.assoc, h.property] using (pullback.condition (f := P.structureMap) (g := sT)))

/-- Represents the entire parametrized Hom functor, not a selected
family of conics. Fixing an open neighborhood is a separate operation. -/
structure HomSpacePresentation (P : ProjectiveLineOverC)
    {d : ℕ} (X : SmoothProperComplexVariety d) where
  parameter : Scheme
  toC : parameter ⟶ ComplexBase
  evaluation : RationalSourceOver P parameter toC ⟶ X.scheme
  overC : evaluation ≫ X.structureMap = pullback.fst P.structureMap toC ≫ P.structureMap
  universal : ∀ (T : Scheme) (sT : T ⟶ ComplexBase),
    Function.Bijective (fun h : PointsOver T sT parameter toC =>
      (⟨rationalSourceMap P h ≫ evaluation, by
        rw [Category.assoc, overC, ← Category.assoc]
        congr 1
        exact pullback.lift_fst _ _ _⟩ :
        PointsOver (RationalSourceOver P T sT)
          (pullback.fst P.structureMap sT ≫ P.structureMap) X.scheme X.structureMap))

/-- Classical representability; projectivity is explicitly required.
Source: sm:relative-hom and standard Hom-scheme representability. -/
theorem homSpacePresentation_exists (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) (hX : HasProjectiveEmbedding X) :
    Nonempty (HomSpacePresentation P X) := by sorry

def HomSpacePresentation.mapAt (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H : HomSpacePresentation P X)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC) :
    ProjectiveLine ⟶ X.scheme :=
  pullback.lift (𝟙 ProjectiveLine) (P.structureMap ≫ t.val) (by
    simp [Category.assoc, t.property]) ≫ H.evaluation

/-- The full neighborhood of sm:full-germ. Its universal parameter
space prevents a one-dimensional subfamily from impersonating Hom_2. -/
structure FullConicNeighborhood (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {n : ℕ} (X : ContactFanoManifold n)
    (g : VeryFreeContactConic P p X) where
  homSpace : HomSpacePresentation P X.variety
  neighborhood : homSpace.parameter.Opens
  marked : PointsOver ComplexBase (𝟙 ComplexBase) neighborhood.toScheme
    (neighborhood.ι ≫ homSpace.toC)
  center : homSpace.mapAt P
    ⟨marked.val ≫ neighborhood.ι, by simpa [Category.assoc] using marked.property⟩ = g.curve.map
  smooth : Smooth (neighborhood.ι ≫ homSpace.toC)
  curveAt : ∀ t : PointsOver ComplexBase (𝟙 ComplexBase) neighborhood.toScheme
    (neighborhood.ι ≫ homSpace.toC), RationalCurve P X.variety
  curveAt_spec : ∀ t, (curveAt t).map = homSpace.mapAt P
    ⟨t.val ≫ neighborhood.ι, by simpa [Category.assoc] using t.property⟩
  degreeTwo : ∀ t, IsIntrinsicContactConic P p X.contact (curveAt t)
  veryFree : ∀ t, IsVeryFreeRationalCurve P X.variety
    (intrinsicTangentBundle X.variety) (curveAt t)

/-! ## C. A normalized source tensor and the full family identity -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.P1Charts
attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjectiveLineProof

/-- The actual change from canonical constants to the supplied base map. -/
def baseChangeIso (P : ProjectiveLineOverC) : ComplexBase ≅ ComplexBase :=
  (zeroDegreeSchemeIso 1).symm ≪≫ P.zeroDegreeIso

theorem baseMap_factor (P : ProjectiveLineOverC) :
    canonicalBaseMap ≫ (baseChangeIso P).hom = P.structureMap := by
  change (Proj.toSpecZero grading ≫ (zeroDegreeSchemeIso 1).hom) ≫
      ((zeroDegreeSchemeIso 1).inv ≫ P.zeroDegreeIso.hom) =
    Proj.toSpecZero grading ≫ P.zeroDegreeIso.hom
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The actual polynomial coefficient morphism is smooth of dimension one. -/
theorem polynomialC_smooth : SmoothOfRelativeDimension 1
    (Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ))) := by
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1 ℂ (Polynomial ℂ) :=
    Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
      (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1))
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  change RingHom.IsStandardSmoothOfRelativeDimension 1 (algebraMap ℂ (Polynomial ℂ))
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr inferInstance

/-- Source locality glues the two actual polynomial charts. -/
theorem canonicalBaseMap_smooth : SmoothOfRelativeDimension 1 canonicalBaseMap := by
  apply IsZariskiLocalAtSource.of_iSup_eq_top chartOpen chartOpen_cover
  intro i
  apply (MorphismProperty.cancel_left_of_respectsIso
    (@SmoothOfRelativeDimension 1) (polynomialChartIso i).inv
    ((chartOpen i).ι ≫ canonicalBaseMap)).mp
  rw [← Category.assoc]
  change SmoothOfRelativeDimension 1 (polynomialChartInclusion i ≫ canonicalBaseMap)
  rw [polynomialChartInclusion_baseMap]
  exact polynomialC_smooth

/-- The supplied base isomorphism preserves relative dimension one. -/
theorem structureMap_smooth (P : ProjectiveLineOverC) :
    SmoothOfRelativeDimension 1 P.structureMap := by
  rw [← baseMap_factor P]
  exact (MorphismProperty.cancel_right_of_respectsIso
    (@SmoothOfRelativeDimension 1) canonicalBaseMap (baseChangeIso P).hom).mpr
      canonicalBaseMap_smooth

/-- Proj properness is applied over the actual degree-zero coefficient ring. -/
theorem structureMap_proper (P : ProjectiveLineOverC) : IsProper P.structureMap := by
  letI : IsScalarTower ℂ (grading 0) Binary :=
    IsScalarTower.of_algebraMap_eq (R := ℂ) (S := ↥(grading 0)) (A := Binary) (fun _ => rfl)
  letI : Algebra.FiniteType (grading 0) Binary :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ (grading 0) Binary
  change IsProper (Proj.toSpecZero grading ≫ P.zeroDegreeIso.hom)
  infer_instance

/-- Each open chart is the connected image of Spec C[t]. -/
theorem chartOpen_connected (i : Fin 2) :
    _root_.IsConnected (chartOpen i : Set lineScheme) := by
  have h : _root_.IsConnected (Set.range (polynomialChartInclusion i)) :=
    isConnected_range (polynomialChartInclusion i).continuous
  change _root_.IsConnected ((polynomialChartInclusion i).opensRange : Set lineScheme) at h
  rw [polynomialChartInclusion_range] at h
  exact h

/-- The actual affine coordinate value one belongs to both charts. -/
theorem coordinateOne_mem_chart (i : Fin 2) :
    pointMap 0 1 (default : PrimeSpectrum ℂ) ∈ chartOpen i := by
  change (default : PrimeSpectrum ℂ) ∈ pointMap 0 1 ⁻¹ᵁ chartOpen i
  rw [pointMap_preimage_chart]
  simp only [ite_self, PrimeSpectrum.basicOpen_one, TopologicalSpace.Opens.mem_top]

/-- The two connected chart opens meet and cover the actual Proj space. -/
theorem projectiveLine_connected : ConnectedSpace ProjectiveLine := by
  have hcover : (chartOpen 0 : Set lineScheme) ∪ (chartOpen 1 : Set lineScheme) =
      Set.univ := by
    change ((chartOpen 0 ⊔ chartOpen 1 : lineScheme.Opens) : Set lineScheme) = Set.univ
    rw [chartOpen_zero_sup_one]
    rfl
  apply connectedSpace_iff_univ.mpr
  rw [← hcover]
  exact _root_.IsConnected.union
    ⟨pointMap 0 1 (default : PrimeSpectrum ℂ),
      coordinateOne_mem_chart 0, coordinateOne_mem_chart 1⟩
    (chartOpen_connected 0) (chartOpen_connected 1)

theorem projectiveLine_nonempty : Nonempty ProjectiveLine :=
  ⟨pointMap 0 0 (default : PrimeSpectrum ℂ)⟩

/-- The exact original conjunction, for every permitted base isomorphism. -/
theorem projectiveLine_smoothProper (P : ProjectiveLineOverC) :
    SmoothOfRelativeDimension 1 P.structureMap ∧ IsProper P.structureMap ∧
      ConnectedSpace ProjectiveLine ∧ Nonempty ProjectiveLine := by
  exact ⟨structureMap_smooth P, structureMap_proper P,
    projectiveLine_connected, projectiveLine_nonempty⟩

end ProjectiveLineProof

end

/-- Classical structure on the actual Proj projective line. -/
theorem projectiveLine_smoothProper (P : ProjectiveLineOverC) :
    SmoothOfRelativeDimension 1 P.structureMap ∧ IsProper P.structureMap ∧
      ConnectedSpace ProjectiveLine ∧ Nonempty ProjectiveLine := by
  exact ProjectiveLineProof.projectiveLine_smoothProper P

def projectiveLineVariety (P : ProjectiveLineOverC) : SmoothProperComplexVariety 1 where
  scheme := ProjectiveLine
  structureMap := P.structureMap
  smooth := (projectiveLine_smoothProper P).1
  proper := (projectiveLine_smoothProper P).2.1
  connected := (projectiveLine_smoothProper P).2.2.1
  nonempty := (projectiveLine_smoothProper P).2.2.2

section IdentityCurveContactProofSection

set_option backward.isDefEq.respectTransparency false

namespace IdentityCurveContactProof

/-- The empty free sheaf is a zero object in the actual module-sheaf category. -/
theorem emptyFree_isZero (X : Scheme) :
    IsZero (SheafOfModules.free (R := X.ringCatSheaf) (Fin 0)) := by
  apply (IsZero.iff_id_eq_zero _).2
  change (𝟙 (∐ (fun _ : Fin 0 => SheafOfModules.unit X.ringCatSheaf))) = 0
  apply Sigma.hom_ext
  intro i
  exact Fin.elim0 i

/-- A zero object satisfies the original local-generator predicate of rank zero. -/
theorem locallyFreeOfRank_zero_of_isZero {X : Scheme} {E : OModule X}
    (hE : IsZero E) : IsLocallyFreeOfRank E 0 :=
  LeBrunSalamon.PhaseTwentySix.locallyFreeOfRank_iso
    ((emptyFree_isZero X).iso hE)
    (LeBrunSalamon.PhaseTwentySix.freeSheaf_rank X 0)

/-- The existing internal Hom from a zero sheaf is a zero object. -/
theorem isZero_internalHom_of_isZero {X : Scheme} {E : OModule X}
    (hE : IsZero E) (L : OModule X) : IsZero (internalHomSheaf E L) := by
  let Z : OModule X := SheafOfModules.free (R := X.ringCatSheaf) (Fin 0)
  have hZ : IsZero Z := emptyFree_isZero X
  let e : E ≅ Z := hE.iso hZ
  let eHom : internalHomSheaf E L ≅ ∏ᶜ (fun _ : Fin 0 => L) :=
    (internalHomPresentation E L).mapIso (internalHomPresentation Z L)
        e (Iso.refl L) ≪≫
      InternalHomPresentation.freeSourceIso
        (fun A B : OModule X => internalHomPresentation A B)
        L (Fin 0) (internalHomPresentation Z L)
  have hProd : IsZero (∏ᶜ (fun _ : Fin 0 => L)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply Pi.hom_ext
    intro i
    exact Fin.elim0 i
  exact hProd.of_iso eHom

/-- The specified intrinsic Levi curry is invertible when its distribution is zero. -/
theorem intrinsicContact_of_isZero {n : ℕ}
    {X : SmoothProperComplexVariety (2 * n + 1)}
    (C : IntrinsicContactSequence X) (hC : IsZero C.distribution.sheaf) :
    IsIntrinsicContact C :=
  hC.isIso (isZero_internalHom_of_isZero hC C.line.sheaf)
    (currySheaf (intrinsicLeviMorphism C))

end IdentityCurveContactProof

end IdentityCurveContactProofSection

set_option backward.isDefEq.respectTransparency false in
/-- Rank-zero contact plane on a curve. Used ONLY to normalize the
source tensor, never as a contact Fano case of the classification. -/
def identityCurveContact (P : ProjectiveLineOverC) :
    IntrinsicContactStructure (n := 0) (projectiveLineVariety P) where
  sequence :=
    { distribution := ⟨kernel (𝟙 (tangentSheaf P.structureMap)), by
        exact IdentityCurveContactProof.locallyFreeOfRank_zero_of_isZero
          (isZero_kernel_of_mono (𝟙 (tangentSheaf P.structureMap)))⟩
      line := intrinsicTangentBundle (projectiveLineVariety P)
      inclusion := kernel.ι (𝟙 (tangentSheaf P.structureMap))
      form := 𝟙 _
      comp_zero := kernel.condition (𝟙 (tangentSheaf P.structureMap))
      shortExact := by
        change (ShortComplex.kernelSequence
          (𝟙 (tangentSheaf P.structureMap))).ShortExact
        exact ShortComplex.ShortExact.mk'
          (ShortComplex.kernelSequence_exact (𝟙 (tangentSheaf P.structureMap)))
          inferInstance (by
            change Epi (𝟙 (tangentSheaf P.structureMap))
            infer_instance) }
  nondegenerate := by
    exact IdentityCurveContactProof.intrinsicContact_of_isZero _
      (isZero_kernel_of_mono (𝟙 (tangentSheaf P.structureMap)))

end LeBrunSalamon.Skeleton

/- BEGIN checked source-bivector proof: LSP1BivectorConstruction -/

/-! Construction of the actual source bivector from three global vector
fields. The vanishing and symbol proofs are developed separately. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Core LeBrunSalamon.Skeleton
open LeBrunSalamon.P1TangentSections
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety

namespace LeBrunSalamon.P1BivectorConstruction

theorem externalProduct_neg_left {X : Scheme} (s : X ⟶ ComplexBase)
    {E F : X.Modules} (a : AlgebraicSection E) (b : AlgebraicSection F) :
    externalProductSection s (-a) b = -externalProductSection s a b := by
  have h : pullSection (firstProjection s) (-a) =
      -pullSection (firstProjection s) a := by
    simp only [pullSection, restrictSection, Functor.map_neg, Preadditive.comp_neg]
  rw [externalProductSection, h, tensorSection_neg_left]
  rfl

def pair (P : ProjectiveLineOverC) (i j : Fin 3) :
    ExternalSquareSections (projectiveLineVariety P) (identityCurveContact P).sequence.line :=
  externalProductSection P.structureMap (polynomialField P i) (polynomialField P j)

/-- The four-term additive form avoids any unproved scalar convention in
the external product. Its coefficient is z²+w²−zw−zw. -/
def bivector (P : ProjectiveLineOverC) :
    ExternalSquareSections (projectiveLineVariety P) (identityCurveContact P).sequence.line :=
  pair P 2 0 + pair P 0 2 - pair P 1 1 - pair P 1 1

theorem symmetric (P : ProjectiveLineOverC) :
    IsSymmetricExternalSection P.structureMap (identityCurveContact P).sequence.line
      (bivector P) := by
  let S := ExchangeAlgebraProof.swapSectionAddHom
    (chosenExternalExchange P.structureMap (identityCurveContact P).sequence.line).identification
  have hs (i j : Fin 3) : S (pair P i j) = pair P j i :=
    (chosenExternalExchange P.structureMap (identityCurveContact P).sequence.line).onProducts
      (polynomialField P i) (polynomialField P j)
  change S (pair P 2 0 + pair P 0 2 - pair P 1 1 - pair P 1 1) = _
  rw [map_sub, map_sub, map_add, hs, hs, hs]
  dsimp only [bivector]
  abel

def left (P : ProjectiveLineOverC) : Fin 4 →
    AlgebraicSection (tangentSheaf P.structureMap) :=
  Fin.cases (polynomialField P 2)
    (Fin.cases (polynomialField P 0) (fun _ => -polynomialField P 1))

def right (P : ProjectiveLineOverC) : Fin 4 →
    AlgebraicSection (tangentSheaf P.structureMap) :=
  Fin.cases (polynomialField P 0)
    (Fin.cases (polynomialField P 2) (fun _ => polynomialField P 1))

def expansion (P : ProjectiveLineOverC) :
    ExternalExpansion (projectiveLineVariety P) (identityCurveContact P).sequence.line
      (bivector P) where
  size := 4
  left := left P
  right := right P
  equation := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, left, right,
      Fin.cases_zero, Fin.cases_succ, add_zero]
    rw [externalProduct_neg_left]
    change pair P 2 0 + pair P 0 2 - pair P 1 1 - pair P 1 1 =
      pair P 2 0 + (pair P 0 2 + (-pair P 1 1 + -pair P 1 1))
    simp only [sub_eq_add_neg, add_assoc]

end LeBrunSalamon.P1BivectorConstruction

end
/- END LSP1BivectorConstruction -/

/- BEGIN checked source-bivector proof: LSP1CoordinatePolynomials -/

/-! Genuine polynomial coordinates of global tangent sections. The supplied
complex-base automorphism is explicitly undone, so the final map is complex
linear for every ProjectiveLineOverC, not only the canonical one. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Core LeBrunSalamon.Core.ExternalTensorCoordinates
open LeBrunSalamon.Skeleton LeBrunSalamon.P1Charts LeBrunSalamon.P1TwistFrames
open LeBrunSalamon.LocalFrames LeBrunSalamon.P1TangentTranslation
open scoped TensorProduct
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety

namespace LeBrunSalamon.P1CoordinatePolynomials

def baseFieldIso (P : ProjectiveLineOverC) : CommRingCat.of ℂ ≅ CommRingCat.of ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm ≪≫
    Scheme.Γ.mapIso (CotangentTwistProof.baseChangeIso P).op ≪≫
    Scheme.ΓSpecIso (CommRingCat.of ℂ)

def baseFieldAuto (P : ProjectiveLineOverC) : ℂ ≃+* ℂ :=
  (baseFieldIso P).commRingCatIsoToRingEquiv

theorem chart_constant (P : ProjectiveLineOverC) (i : Fin 2) (c : ℂ) :
    polynomialChartRingEquiv i (constants P.structureMap (chartOpen i) c) =
      Polynomial.C (baseFieldAuto P c) := by
  let A := CotangentTwistProof.baseChangeIso P
  let d := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    (A.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))
  change polynomialChartRingEquiv i
    (complexConstant P.structureMap (chartOpen i) c) = Polynomial.C d
  have hd : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv d =
      A.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) :=
    Iso.hom_inv_id_apply _ _
  rw [complexConstant, ← CotangentTwistProof.baseMap_factor P,
    Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, ← hd]
  exact polynomialChartRingEquiv_canonical_constant i d

def chartAlgebraEquiv (P : ProjectiveLineOverC) (i : Fin 2) :
    Coefficients P.structureMap (chartOpen i) ≃ₐ[ℂ] Polynomial ℂ :=
  { (polynomialChartRingEquiv i).trans (Polynomial.mapEquiv (baseFieldAuto P).symm) with
    commutes' c := by
      change Polynomial.mapEquiv (baseFieldAuto P).symm
        (polynomialChartRingEquiv i (constants P.structureMap (chartOpen i) c)) =
          Polynomial.C c
      rw [chart_constant]
      change Polynomial.map (baseFieldAuto P).symm.toRingHom
        (Polynomial.C (baseFieldAuto P c)) = Polynomial.C c
      rw [Polynomial.map_C]
      exact congrArg Polynomial.C ((baseFieldAuto P).symm_apply_apply c) }

theorem chartAlgebraEquiv_coordinate (P : ProjectiveLineOverC) (i : Fin 2) :
    chartAlgebraEquiv P i (coordinate i) = Polynomial.X := by
  change Polynomial.mapEquiv (baseFieldAuto P).symm
    (polynomialChartRingEquiv i ((polynomialChartRingEquiv i).symm Polynomial.X)) = _
  rw [RingEquiv.apply_symm_apply]
  exact Polynomial.map_X _

def frame (P : ProjectiveLineOverC) (i : Fin 2) :
    AffineLineFrame (identityCurveContact P).sequence.line where
  openSet := chartOpen i
  isAffine := chartOpen_affine i
  coefficient := coordinates (derivativeFrame P i)

theorem action_coordinate (P : ProjectiveLineOverC) (i : Fin 2)
    (v : SectionsOn (tangentSheaf P.structureMap) (chartOpen i)) :
    tangentActs P.structureMap (chartOpen i) v (coordinate i) =
      (frame P i).coefficient v := by
  have h := congrArg (fun w => tangentActs P.structureMap (chartOpen i) w (coordinate i))
    (reconstruct (derivativeFrame P i) v)
  rw [TangentActionProof.smul_field, derivativeFrame_coordinate, mul_one] at h
  exact h.symm

def polynomialAction (P : ProjectiveLineOverC) (i : Fin 2)
    (v : SectionsOn (tangentSheaf P.structureMap) (chartOpen i)) :
    Derivation ℂ (Polynomial ℂ) (Polynomial ℂ) where
  toLinearMap := (chartAlgebraEquiv P i).toLinearMap.comp
    ((coefficientDerivation P.structureMap (chartOpen i) v).toLinearMap.comp
      (chartAlgebraEquiv P i).symm.toLinearMap)
  map_one_eq_zero' := by
    change chartAlgebraEquiv P i
      ((coefficientDerivation P.structureMap (chartOpen i) v)
        ((chartAlgebraEquiv P i).symm 1)) = 0
    simp
  leibniz' := by
    intro a b
    change chartAlgebraEquiv P i
      ((coefficientDerivation P.structureMap (chartOpen i) v)
        ((chartAlgebraEquiv P i).symm (a * b))) =
      a * chartAlgebraEquiv P i
        ((coefficientDerivation P.structureMap (chartOpen i) v)
          ((chartAlgebraEquiv P i).symm b)) +
      b * chartAlgebraEquiv P i
        ((coefficientDerivation P.structureMap (chartOpen i) v)
          ((chartAlgebraEquiv P i).symm a))
    rw [map_mul, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, AlgEquiv.apply_symm_apply]

theorem action_polynomial (P : ProjectiveLineOverC) (i : Fin 2)
    (v : SectionsOn (tangentSheaf P.structureMap) (chartOpen i))
    (a : RingSections ProjectiveLine (chartOpen i)) :
    chartAlgebraEquiv P i (tangentActs P.structureMap (chartOpen i) v a) =
      (chartAlgebraEquiv P i a).derivative *
        chartAlgebraEquiv P i ((frame P i).coefficient v) := by
  have h := (polynomialAction P i v).map_aeval
    (chartAlgebraEquiv P i a) Polynomial.X
  have hx : (chartAlgebraEquiv P i).symm Polynomial.X = coordinate i := by
    apply (chartAlgebraEquiv P i).injective
    rw [AlgEquiv.apply_symm_apply, chartAlgebraEquiv_coordinate]
  simp only [Polynomial.aeval_X_left_apply, smul_eq_mul] at h
  have ha : polynomialAction P i v (chartAlgebraEquiv P i a) =
      chartAlgebraEquiv P i (tangentActs P.structureMap (chartOpen i) v a) := by
    change chartAlgebraEquiv P i
      (tangentActs P.structureMap (chartOpen i) v
        ((chartAlgebraEquiv P i).symm (chartAlgebraEquiv P i a))) = _
    rw [AlgEquiv.symm_apply_apply]
  have hX : polynomialAction P i v Polynomial.X =
      chartAlgebraEquiv P i ((frame P i).coefficient v) := by
    change chartAlgebraEquiv P i
      (tangentActs P.structureMap (chartOpen i) v
        ((chartAlgebraEquiv P i).symm Polynomial.X)) = _
    rw [hx, action_coordinate]
  rw [ha, hX] at h
  exact h

theorem generator_action (P : ProjectiveLineOverC) (i : Fin 2)
    (a : RingSections ProjectiveLine (chartOpen i)) :
    chartAlgebraEquiv P i
      (tangentActs P.structureMap (chartOpen i) (generator (derivativeFrame P i)) a) =
        (chartAlgebraEquiv P i a).derivative := by
  rw [action_polynomial]
  change _ * chartAlgebraEquiv P i (coordinates _ (generator _)) = _
  rw [coordinates_generator, map_one, mul_one]

def polynomial (P : ProjectiveLineOverC) (a : AlgebraicSection (tangentSheaf P.structureMap)) :
    Polynomial ℂ := chartAlgebraEquiv P 0 ((frame P 0).localCoefficient a)

theorem polynomial_eq_matching (P : ProjectiveLineOverC)
    (a : AlgebraicSection (tangentSheaf P.structureMap)) :
    polynomial P a = Polynomial.mapEquiv (baseFieldAuto P).symm
      (P1TangentSections.matchingEquiv P a).val.1 := by
  rw [P1TangentSections.matchingEquiv_zero]
  change Polynomial.mapEquiv (baseFieldAuto P).symm
    (polynomialChartRingEquiv 0 (coordinates (derivativeFrame P 0)
      (Scheme.Modules.Hom.app a (chartOpen 0) (1 : RingSections ProjectiveLine (chartOpen 0))))) = _
  exact congrArg (fun v : SectionsOn (tangentSheaf P.structureMap) (chartOpen 0) =>
    Polynomial.mapEquiv (baseFieldAuto P).symm
      (polynomialChartRingEquiv 0 (coordinates (derivativeFrame P 0) v)))
    (section_app_one a (chartOpen 0))

theorem polynomial_injective (P : ProjectiveLineOverC) : Function.Injective (polynomial P) := by
  intro a b hab
  rw [polynomial_eq_matching, polynomial_eq_matching] at hab
  apply (P1TangentSections.matchingEquiv P).injective
  apply P1Overlap.matchingSpace_ext
  exact (Polynomial.mapEquiv (baseFieldAuto P).symm).injective hab

theorem polynomial_natDegree_le (P : ProjectiveLineOverC)
    (a : AlgebraicSection (tangentSheaf P.structureMap)) :
    (polynomial P a).natDegree ≤ 2 := by
  rw [polynomial_eq_matching, Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [P1Overlap.polynomialCoefficientEquiv_coeff,
    Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (P1Overlap.matching_degree_le
        (P1TangentSections.matchingEquiv P a).property) hn), map_zero]

def polynomialLinear (P : ProjectiveLineOverC) :
    ComplexSections P.structureMap (tangentSheaf P.structureMap) →ₗ[ℂ] Polynomial ℂ :=
  (chartAlgebraEquiv P 0).toLinearMap.comp
    (coefficientLinear P.structureMap (identityCurveContact P).sequence.line (frame P 0))

theorem polynomialLinear_sectionValue (P : ProjectiveLineOverC)
    (a : AlgebraicSection (tangentSheaf P.structureMap)) :
    polynomialLinear P (sectionValue a) = polynomial P a := by
  change chartAlgebraEquiv P 0
    (coefficientLinear P.structureMap (identityCurveContact P).sequence.line (frame P 0)
      (sectionValue a)) = _
  rw [coefficientLinear_sectionValue]
  rfl

theorem polynomialLinear_injective (P : ProjectiveLineOverC) :
    Function.Injective (polynomialLinear P) := by
  intro a b h
  have hab : sectionFromValue a = sectionFromValue b := by
    apply polynomial_injective P
    rw [← polynomialLinear_sectionValue, ← polynomialLinear_sectionValue,
      sectionFromValue_spec, sectionFromValue_spec]
    exact h
  simpa only [sectionFromValue_spec] using congrArg (fun a => sectionValue a) hab

def polynomialTensor (P : ProjectiveLineOverC) :=
  TensorProduct.map (polynomialLinear P) (polynomialLinear P)

theorem polynomialTensor_injective (P : ProjectiveLineOverC) :
    Function.Injective (polynomialTensor P) := by
  let V := ComplexSections P.structureMap (tangentSheaf P.structureMap)
  let f := polynomialLinear P
  have he : polynomialTensor P =
      (f.lTensor (Polynomial ℂ)).comp (f.rTensor V) := by
    ext a b
    rfl
  rw [he]
  exact (Module.Flat.lTensor_preserves_injective_linearMap f (polynomialLinear_injective P)).comp
    (Module.Flat.rTensor_preserves_injective_linearMap f (polynomialLinear_injective P))

end LeBrunSalamon.P1CoordinatePolynomials

end
/- END LSP1CoordinatePolynomials -/

/- BEGIN checked source-bivector proof: LSP1BivectorUniqueness -/

/-! Uniqueness of the source bivector from the actual finite expansion,
the degree bound, and its three diagonal symbols. No source-bivector
existence or uniqueness theorem is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Core LeBrunSalamon.Core.ExternalTensorCoordinates
open LeBrunSalamon.Skeleton LeBrunSalamon.P1Charts LeBrunSalamon.LocalFrames
open LeBrunSalamon.P1TangentTranslation LeBrunSalamon.P1CoordinatePolynomials
open scoped TensorProduct
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety frame

namespace LeBrunSalamon.P1BivectorUniqueness

variable (P : ProjectiveLineOverC)
variable {B : ExternalSquareSections (projectiveLineVariety P)
  (identityCurveContact P).sequence.line}
variable (E : ExternalExpansion (projectiveLineVariety P)
  (identityCurveContact P).sequence.line B)

def left (i : Fin E.size) : Polynomial ℂ := polynomial P (E.left i)
def right (i : Fin E.size) : Polynomial ℂ := polynomial P (E.right i)

theorem polynomial_value
    (ho : VanishesQuadraticallyAlongDiagonal P.structureMap
      (externalSquareLine P.structureMap (identityCurveContact P).sequence.line).sheaf B) :
    ∑ i, left P E i * right P E i = 0 := by
  have h := congrArg (chartAlgebraEquiv P 0)
    (E.diagonalValue_zero_of_orderTwo ho (frame P 0))
  simpa only [ExternalExpansion.diagonalValue, map_sum, map_mul, map_zero,
    left, right, polynomial] using h

theorem polynomial_first
    (ho : VanishesQuadraticallyAlongDiagonal P.structureMap
      (externalSquareLine P.structureMap (identityCurveContact P).sequence.line).sheaf B) :
    ∑ i, left P E i * (right P E i).derivative = 0 := by
  have h := congrArg (chartAlgebraEquiv P 0)
    (E.secondSlotFirst_zero_of_orderTwo ho (frame P 0) (generator (derivativeFrame P 0)))
  simpa only [ExternalExpansion.secondSlotFirst, map_sum, map_mul, map_zero,
    generator_action, left, right, polynomial] using h

theorem polynomial_second
    (hn : ExpansionHasContactHessian (identityCurveContact P) E) :
    ∑ i, left P E i * (right P E i).derivative.derivative = 2 := by
  have h := congrArg (chartAlgebraEquiv P 0)
    (hn (frame P 0) (generator (derivativeFrame P 0)) (generator (derivativeFrame P 0)))
  change chartAlgebraEquiv P 0
      (∑ i, (frame P 0).localCoefficient (E.left i) *
        tangentActs P.structureMap (chartOpen 0) (generator (derivativeFrame P 0))
          (tangentActs P.structureMap (chartOpen 0) (generator (derivativeFrame P 0))
            ((frame P 0).localCoefficient (E.right i)))) =
    chartAlgebraEquiv P 0
      ((2 : RingSections ProjectiveLine (chartOpen 0)) * coordinates (derivativeFrame P 0) (generator (derivativeFrame P 0)) *
        coordinates (derivativeFrame P 0) (generator (derivativeFrame P 0))) at h
  simpa only [map_sum, map_mul, generator_action, coordinates_generator,
    map_one, map_ofNat, mul_one, left, right, polynomial] using h

/-- The image of the actual expansion tensor is the coefficient-one square. -/
theorem tensor_formula
    (ho : VanishesQuadraticallyAlongDiagonal P.structureMap
      (externalSquareLine P.structureMap (identityCurveContact P).sequence.line).sheaf B)
    (hn : ExpansionHasContactHessian (identityCurveContact P) E) :
    polynomialTensor P E.tensor = (P1SourceAlgebra.leftX - P1SourceAlgebra.rightX)^2 := by
  change TensorProduct.map (polynomialLinear P) (polynomialLinear P)
    (∑ i, sectionValue (E.left i) ⊗ₜ[ℂ] sectionValue (E.right i)) = _
  rw [map_sum]
  simp only [TensorProduct.map_tmul, polynomialLinear_sectionValue]
  exact P1SourceAlgebra.tensor_formula (left P E) (right P E)
    (fun i => polynomial_natDegree_le P (E.right i))
    (polynomial_value P E ho) (polynomial_first P E ho) (polynomial_second P E hn)

/-- Two sections with the required order and symbol are equal. Symmetry
is not needed for uniqueness. -/
theorem unique
    (C : ExternalSquareSections (projectiveLineVariety P)
      (identityCurveContact P).sequence.line)
    (hB : VanishesQuadraticallyAlongDiagonal P.structureMap
      (externalSquareLine P.structureMap (identityCurveContact P).sequence.line).sheaf B)
    (nB : HasNormalizedContactSymbol (identityCurveContact P) B)
    (hC : VanishesQuadraticallyAlongDiagonal P.structureMap
      (externalSquareLine P.structureMap (identityCurveContact P).sequence.line).sheaf C)
    (nC : HasNormalizedContactSymbol (identityCurveContact P) C) : B = C := by
  obtain ⟨E, hnE⟩ := nB
  obtain ⟨F, hnF⟩ := nC
  have hEF : E.tensor = F.tensor := by
    apply polynomialTensor_injective P
    rw [tensor_formula P E hB hnE, tensor_formula P F hC hnF]
  apply (sectionValue_bijective _).injective
  rw [← E.tensor_image, ← F.tensor_image, hEF]

end LeBrunSalamon.P1BivectorUniqueness

end
/- END LSP1BivectorUniqueness -/

/- BEGIN checked source-bivector proof: LSP1BivectorNormalization -/

/-! The normalized Hessian is proved in every supplied affine frame by
restricting its actual sheaf trivialization to the two polynomial charts.
The gauge terms cancel in the explicit four-term global expansion. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Core LeBrunSalamon.Core.ExternalTensorCoordinates
open LeBrunSalamon.Skeleton LeBrunSalamon.P1Charts LeBrunSalamon.P1TwistFrames
open LeBrunSalamon.LocalFrames LeBrunSalamon.P1TangentTranslation
open LeBrunSalamon.P1TangentSections
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety

namespace LeBrunSalamon.P1BivectorNormalization

def localCoefficient {X : Scheme} {E : X.Modules} {U : X.Opens}
    (e : OverFrame E U) (a : AlgebraicSection E) : RingSections X U :=
  coordinates e (Scheme.Modules.Hom.app a U (1 : RingSections X U))

theorem localCoefficient_restrict {X : Scheme} {E : X.Modules} {U V : X.Opens}
    (i : V ⟶ U) (e : OverFrame E U) (a : AlgebraicSection E) :
    X.presheaf.map i.op (localCoefficient e a) =
      localCoefficient (restrict i e) a := by
  have h := coordinates_restrict i e (Scheme.Modules.Hom.app a U (1 : RingSections X U))
  rw [sheafHom_naturality a i] at h
  change coordinates (restrict i e)
      (Scheme.Modules.Hom.app a V (X.presheaf.map i.op (1 : RingSections X U))) =
    X.presheaf.map i.op
      (coordinates e (Scheme.Modules.Hom.app a U (1 : RingSections X U))) at h
  rw [map_one] at h
  exact h.symm

theorem localCoefficient_change {X : Scheme} {E : X.Modules} {U : X.Opens}
    (e f : OverFrame E U) (a : AlgebraicSection E) :
    localCoefficient e a = localCoefficient f a * coordinates e (generator f) :=
  coordinates_change e f (Scheme.Modules.Hom.app a U (1 : RingSections X U))

variable (P : ProjectiveLineOverC)

abbrev TangentLine := (identityCurveContact P).sequence.line

instance tangentQuasicoherent : (tangentSheaf P.structureMap).IsQuasicoherent :=
  KunnethDegreeZero.quasicoherent_of_locallyFreeRank (tangentLine P).locallyFree

instance tangentLineQuasicoherent : ((TangentLine P).sheaf).IsQuasicoherent :=
  KunnethDegreeZero.quasicoherent_of_locallyFreeRank (TangentLine P).locallyFree

def actualFrame (F : AffineLineFrame (TangentLine P)) :
    OverFrame (tangentSheaf P.structureMap) F.openSet :=
  AffineFrameProof.frame F.openSet F.isAffine F.coefficient

theorem actualFrame_coordinates (F : AffineLineFrame (TangentLine P))
    (v : SectionsOn (tangentSheaf P.structureMap) F.openSet) :
    coordinates (actualFrame P F) v = F.coefficient v :=
  AffineFrameProof.frame_coordinates F.openSet F.isAffine F.coefficient v

def localCoefficientAddHom (F : AffineLineFrame (TangentLine P)) :
    AlgebraicSection (tangentSheaf P.structureMap) →+ RingSections ProjectiveLine F.openSet where
  toFun := F.localCoefficient
  map_zero' := by change F.coefficient 0 = 0; exact map_zero F.coefficient
  map_add' a b := by
    change F.coefficient (Scheme.Modules.Hom.app a F.openSet (1 : RingSections ProjectiveLine F.openSet) +
      Scheme.Modules.Hom.app b F.openSet (1 : RingSections ProjectiveLine F.openSet)) = _
    exact map_add F.coefficient _ _

theorem coefficient_neg (F : AffineLineFrame (TangentLine P))
    (a : AlgebraicSection (tangentSheaf P.structureMap)) :
    F.localCoefficient (-a) = -F.localCoefficient a :=
  (localCoefficientAddHom P F).map_neg a

theorem coefficientDerivation_apply (U : ProjectiveLine.Opens)
    (u : SectionsOn (tangentSheaf P.structureMap) U)
    (a : Coefficients P.structureMap U) :
    coefficientDerivation P.structureMap U u a = tangentActs P.structureMap U u a := rfl

theorem expansion_hessian_formula (F : AffineLineFrame (TangentLine P))
    (u v : SectionsOn (tangentSheaf P.structureMap) F.openSet) :
    (P1BivectorConstruction.expansion P).secondSlotSecond F u v =
      P1SourceAlgebra.fourHessian
        (coefficientDerivation P.structureMap F.openSet u)
        (coefficientDerivation P.structureMap F.openSet v)
        (F.localCoefficient (polynomialField P 0))
        (F.localCoefficient (polynomialField P 1))
        (F.localCoefficient (polynomialField P 2)) := by
  simp only [ExternalExpansion.secondSlotSecond, P1BivectorConstruction.expansion,
    P1BivectorConstruction.left, P1BivectorConstruction.right,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cases_zero, Fin.cases_succ, add_zero,
    coefficient_neg, P1SourceAlgebra.fourHessian, coefficientDerivation_apply]
  ring

abbrev chart (F : AffineLineFrame (TangentLine P)) (i : Fin 2) : ProjectiveLine.Opens :=
  F.openSet ⊓ chartOpen i

abbrev frameOn (F : AffineLineFrame (TangentLine P)) (i : Fin 2) :
    OverFrame (tangentSheaf P.structureMap) (chart P F i) :=
  restrict (homOfLE inf_le_left) (actualFrame P F)

abbrev derivativeOn (F : AffineLineFrame (TangentLine P)) (i : Fin 2) :
    OverFrame (tangentSheaf P.structureMap) (chart P F i) :=
  restrict (homOfLE inf_le_right) (derivativeFrame P i)

abbrev coordinateOn (F : AffineLineFrame (TangentLine P)) (i : Fin 2) :
    RingSections ProjectiveLine (chart P F i) :=
  ProjectiveLine.presheaf.map (homOfLE inf_le_right).op (coordinate i)

def gauge (F : AffineLineFrame (TangentLine P)) (i : Fin 2) :
    RingSections ProjectiveLine (chart P F i) :=
  coordinates (frameOn P F i) (generator (derivativeOn P F i))

theorem derivativeOn_coordinate (F : AffineLineFrame (TangentLine P)) (i : Fin 2) :
    tangentActs P.structureMap (chart P F i) (generator (derivativeOn P F i))
      (coordinateOn P F i) = 1 := by
  rw [derivativeOn, ← generator_restrict, coordinateOn,
    ← TangentActionProof.naturality, derivativeFrame_coordinate, map_one]

theorem coordinates_action (F : AffineLineFrame (TangentLine P)) (i : Fin 2)
    (u : SectionsOn (tangentSheaf P.structureMap) (chart P F i)) :
    coordinates (frameOn P F i) u = gauge P F i *
      tangentActs P.structureMap (chart P F i) u (coordinateOn P F i) := by
  have h := congrArg
    (fun v => tangentActs P.structureMap (chart P F i) v (coordinateOn P F i))
    (reconstruct (derivativeOn P F i) u)
  rw [TangentActionProof.smul_field, derivativeOn_coordinate, mul_one] at h
  rw [coordinates_change (frameOn P F i) (derivativeOn P F i), h]
  exact mul_comm _ _

theorem field_chart_zero (k : Fin 3) :
    localCoefficient (derivativeFrame P 0) (polynomialField P k) =
      coordinate 0 ^ k.val := by
  apply (polynomialChartRingEquiv 0).injective
  rw [map_pow]
  change polynomialChartRingEquiv 0
      (coordinates (derivativeFrame P 0) (Scheme.Modules.Hom.app (polynomialField P k) (chartOpen 0) (1 : RingSections ProjectiveLine (chartOpen 0)))) =
    (polynomialChartRingEquiv 0 ((polynomialChartRingEquiv 0).symm Polynomial.X)) ^ k.val
  rw [RingEquiv.apply_symm_apply, section_app_one]
  exact polynomialField_zero P k

theorem field_chart_one (k : Fin 3) :
    localCoefficient (derivativeFrame P 1) (polynomialField P k) =
      -(coordinate 1 ^ (2-k.val)) := by
  apply (polynomialChartRingEquiv 1).injective
  rw [map_neg, map_pow]
  change polynomialChartRingEquiv 1
      (coordinates (derivativeFrame P 1) (Scheme.Modules.Hom.app (polynomialField P k) (chartOpen 1) (1 : RingSections ProjectiveLine (chartOpen 1)))) =
    -((polynomialChartRingEquiv 1 ((polynomialChartRingEquiv 1).symm Polynomial.X)) ^ (2-k.val))
  rw [RingEquiv.apply_symm_apply, section_app_one]
  exact polynomialField_one P k

theorem coefficient_on_zero (F : AffineLineFrame (TangentLine P)) (k : Fin 3) :
    localCoefficient (frameOn P F 0) (polynomialField P k) =
      gauge P F 0 * coordinateOn P F 0 ^ k.val := by
  rw [localCoefficient_change (frameOn P F 0) (derivativeOn P F 0)]
  change localCoefficient (restrict (homOfLE inf_le_right) (derivativeFrame P 0))
    (polynomialField P k) * gauge P F 0 = _
  rw [← localCoefficient_restrict, field_chart_zero, map_pow]
  exact mul_comm _ _

theorem coefficient_on_one (F : AffineLineFrame (TangentLine P)) (k : Fin 3) :
    localCoefficient (frameOn P F 1) (polynomialField P k) =
      -(gauge P F 1 * coordinateOn P F 1 ^ (2-k.val)) := by
  rw [localCoefficient_change (frameOn P F 1) (derivativeOn P F 1)]
  change localCoefficient (restrict (homOfLE inf_le_right) (derivativeFrame P 1))
    (polynomialField P k) * gauge P F 1 = _
  rw [← localCoefficient_restrict, field_chart_one, map_neg, map_pow]
  ring

theorem restricted_coefficient (F : AffineLineFrame (TangentLine P)) (i : Fin 2)
    (a : AlgebraicSection (tangentSheaf P.structureMap)) :
    ProjectiveLine.presheaf.map (homOfLE (show chart P F i ≤ F.openSet from inf_le_left)).op
      (F.localCoefficient a) = localCoefficient (frameOn P F i) a := by
  change ProjectiveLine.presheaf.map
      (homOfLE (show chart P F i ≤ F.openSet from inf_le_left)).op
      (F.coefficient (Scheme.Modules.Hom.app a F.openSet (1 : RingSections ProjectiveLine F.openSet))) = _
  rw [← actualFrame_coordinates P F]
  exact localCoefficient_restrict (homOfLE inf_le_left) (actualFrame P F) a

theorem restricted_vector_coefficient (F : AffineLineFrame (TangentLine P)) (i : Fin 2)
    (u : SectionsOn (tangentSheaf P.structureMap) F.openSet) :
    ProjectiveLine.presheaf.map (homOfLE (show chart P F i ≤ F.openSet from inf_le_left)).op
      (F.coefficient u) = coordinates (frameOn P F i)
        ((tangentSheaf P.structureMap).presheaf.map (homOfLE inf_le_left).op u) := by
  rw [← actualFrame_coordinates P F]
  exact (coordinates_restrict (homOfLE inf_le_left) (actualFrame P F) u).symm

/-- The local identity after restriction to either genuine polynomial chart. -/
theorem local_hessian (F : AffineLineFrame (TangentLine P)) (i : Fin 2)
    (u v : SectionsOn (tangentSheaf P.structureMap) (chart P F i)) :
    P1SourceAlgebra.fourHessian
      (coefficientDerivation P.structureMap (chart P F i) u)
      (coefficientDerivation P.structureMap (chart P F i) v)
      (localCoefficient (frameOn P F i) (polynomialField P 0))
      (localCoefficient (frameOn P F i) (polynomialField P 1))
      (localCoefficient (frameOn P F i) (polynomialField P 2)) =
        (2 : RingSections ProjectiveLine (chart P F i)) *
          coordinates (frameOn P F i) u * coordinates (frameOn P F i) v := by
  rw [coordinates_action, coordinates_action]
  have htwo : (2 : Fin 3).val = 2 := rfl
  fin_cases i
  · simp only [coefficient_on_zero, Fin.val_zero, Fin.val_one, htwo, Fin.reduceFinMk,
      pow_zero, pow_one, mul_one]
    erw [P1SourceAlgebra.fourHessian_gauge_zero]
    have hring : (2 : RingSections ProjectiveLine (chart P F 0)) * gauge P F 0 ^ 2 *
      tangentActs P.structureMap (chart P F 0) u (coordinateOn P F 0) *
      tangentActs P.structureMap (chart P F 0) v (coordinateOn P F 0) =
        (2 : RingSections ProjectiveLine (chart P F 0)) *
          (gauge P F 0 * tangentActs P.structureMap (chart P F 0) u (coordinateOn P F 0)) *
          (gauge P F 0 * tangentActs P.structureMap (chart P F 0) v (coordinateOn P F 0)) := by ring
    exact hring
  · simp only [coefficient_on_one, Fin.val_zero, Fin.val_one, htwo, Fin.reduceFinMk,
      Nat.reduceSub, pow_zero, pow_one, mul_one]
    erw [P1SourceAlgebra.fourHessian_gauge_one]
    have hring : (2 : RingSections ProjectiveLine (chart P F 1)) * gauge P F 1 ^ 2 *
      tangentActs P.structureMap (chart P F 1) u (coordinateOn P F 1) *
      tangentActs P.structureMap (chart P F 1) v (coordinateOn P F 1) =
        (2 : RingSections ProjectiveLine (chart P F 1)) *
          (gauge P F 1 * tangentActs P.structureMap (chart P F 1) u (coordinateOn P F 1)) *
          (gauge P F 1 * tangentActs P.structureMap (chart P F 1) v (coordinateOn P F 1)) := by ring
    exact hring

/-- The coordinate calculation glues on the supplied affine open. -/
theorem normalized : HasNormalizedContactSymbol (identityCurveContact P)
    (P1BivectorConstruction.bivector P) := by
  refine ⟨P1BivectorConstruction.expansion P, ?_⟩
  intro F u v
  change (P1BivectorConstruction.expansion P).secondSlotSecond F u v =
    2 * F.coefficient u * F.coefficient v
  rw [expansion_hessian_formula]
  have hloc (i : Fin 2) :
      ProjectiveLine.presheaf.map
        (homOfLE (show chart P F i ≤ F.openSet from inf_le_left)).op
          (P1SourceAlgebra.fourHessian (R := Coefficients P.structureMap F.openSet)
            (coefficientDerivation P.structureMap F.openSet u)
            (coefficientDerivation P.structureMap F.openSet v)
            (F.localCoefficient (polynomialField P 0))
            (F.localCoefficient (polynomialField P 1))
            (F.localCoefficient (polynomialField P 2))) =
      ProjectiveLine.presheaf.map
        (homOfLE (show chart P F i ≤ F.openSet from inf_le_left)).op
          (2 * F.coefficient u * F.coefficient v) := by
    simp only [P1SourceAlgebra.fourHessian, coefficientDerivation_apply,
      map_sub, map_add, map_mul, map_ofNat, TangentActionProof.naturality,
      restricted_coefficient, restricted_vector_coefficient P F i u,
      restricted_vector_coefficient P F i v]
    simpa only [P1SourceAlgebra.fourHessian, coefficientDerivation_apply] using local_hessian P F i
      ((tangentSheaf P.structureMap).presheaf.map (homOfLE inf_le_left).op u)
      ((tangentSheaf P.structureMap).presheaf.map (homOfLE inf_le_left).op v)
  have hcover : chart P F 0 ⊔ chart P F 1 = F.openSet := by
    simp only [chart, ← inf_sup_left, chartOpen_zero_sup_one, inf_top_eq]
  exact (TwoChartSections.sectionSheaf (structureModule ProjectiveLine)).eq_of_locally_eq₂
    (homOfLE (show chart P F 0 ≤ F.openSet from inf_le_left))
    (homOfLE (show chart P F 1 ≤ F.openSet from inf_le_left)) hcover.ge _ _
    (hloc 0) (hloc 1)

end LeBrunSalamon.P1BivectorNormalization

end
/- END LSP1BivectorNormalization -/

/- BEGIN checked source-bivector proof: LSP1BivectorVanishing -/

/-! Order-two vanishing of the actual four-term source bivector. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Core LeBrunSalamon.Skeleton
open LeBrunSalamon.LocalFrames LeBrunSalamon.P1Charts LeBrunSalamon.P1TwistFrames
open LeBrunSalamon.P1TangentTranslation LeBrunSalamon.P1TangentSections
open LeBrunSalamon.ExternalFrameCoefficients
open scoped TensorProduct
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety

namespace LeBrunSalamon.P1BivectorVanishing

variable (P : ProjectiveLineOverC)

def coordinateFunction (i : Fin 2) :
    OpenProductCoordinates.Coefficients P.structureMap (chartOpen i) := coordinate i

theorem coefficient_zero (k : Fin 3) :
    coefficientLinear P.structureMap (derivativeFrame P 0)
      (sectionValue (polynomialField P k)) = coordinateFunction P 0 ^ k.val := by
  rw [coefficientLinear_sectionValue]
  apply (polynomialChartRingEquiv 0).injective
  rw [map_pow]
  change polynomialChartRingEquiv 0
      (coordinates (derivativeFrame P 0) (Scheme.Modules.Hom.app (polynomialField P k) (chartOpen 0) (1 : RingSections ProjectiveLine (chartOpen 0)))) =
    (polynomialChartRingEquiv 0 ((polynomialChartRingEquiv 0).symm Polynomial.X)) ^ k.val
  rw [RingEquiv.apply_symm_apply, ExternalFrameCoefficients.section_app_one]
  exact polynomialField_zero P k

theorem coefficient_one (k : Fin 3) :
    coefficientLinear P.structureMap (derivativeFrame P 1)
      (sectionValue (polynomialField P k)) = -(coordinateFunction P 1 ^ (2 - k.val)) := by
  rw [coefficientLinear_sectionValue]
  apply (polynomialChartRingEquiv 1).injective
  rw [map_neg, map_pow]
  change polynomialChartRingEquiv 1
      (coordinates (derivativeFrame P 1) (Scheme.Modules.Hom.app (polynomialField P k) (chartOpen 1) (1 : RingSections ProjectiveLine (chartOpen 1)))) =
    -((polynomialChartRingEquiv 1 ((polynomialChartRingEquiv 1).symm Polynomial.X)) ^
      (2 - k.val))
  rw [RingEquiv.apply_symm_apply, ExternalFrameCoefficients.section_app_one]
  exact polynomialField_one P k

theorem coefficient_tensor (i : Fin 2) :
    coefficientTensorMap P.structureMap (derivativeFrame P i) (derivativeFrame P i)
      (P1BivectorConstruction.expansion P).tensor =
      (coordinateFunction P i ^ 2) ⊗ₜ[ℂ] (1 : OpenProductCoordinates.Coefficients P.structureMap (chartOpen i)) +
      (1 : OpenProductCoordinates.Coefficients P.structureMap (chartOpen i)) ⊗ₜ[ℂ] (coordinateFunction P i ^ 2) -
      coordinateFunction P i ⊗ₜ[ℂ] coordinateFunction P i - coordinateFunction P i ⊗ₜ[ℂ] coordinateFunction P i := by
  have htwo : (2 : Fin 3).val = 2 := rfl
  fin_cases i
  · change coefficientTensorMap P.structureMap (derivativeFrame P 0) (derivativeFrame P 0)
      (∑ j : Fin 4, (sectionValue (P1BivectorConstruction.left P j) :
        KunnethDegreeZero.Sections P.structureMap (tangentSheaf P.structureMap)) ⊗ₜ[ℂ]
        (sectionValue (P1BivectorConstruction.right P j) :
        KunnethDegreeZero.Sections P.structureMap (tangentSheaf P.structureMap))) = _
    rw [map_sum]
    simp only [coefficientTensorMap_tmul, Fin.sum_univ_succ,
      Fin.sum_univ_zero, P1BivectorConstruction.left, P1BivectorConstruction.right,
      Fin.cases_zero, Fin.cases_succ, sectionValue_neg, map_neg, coefficient_zero,
      Fin.val_zero, Fin.val_one, htwo, Fin.reduceFinMk, pow_zero, pow_one, add_zero,
      TensorProduct.neg_tmul]
    abel
  · change coefficientTensorMap P.structureMap (derivativeFrame P 1) (derivativeFrame P 1)
      (∑ j : Fin 4, (sectionValue (P1BivectorConstruction.left P j) :
        KunnethDegreeZero.Sections P.structureMap (tangentSheaf P.structureMap)) ⊗ₜ[ℂ]
        (sectionValue (P1BivectorConstruction.right P j) :
        KunnethDegreeZero.Sections P.structureMap (tangentSheaf P.structureMap))) = _
    rw [map_sum]
    simp only [coefficientTensorMap_tmul, Fin.sum_univ_succ,
      Fin.sum_univ_zero, P1BivectorConstruction.left, P1BivectorConstruction.right,
      Fin.cases_zero, Fin.cases_succ, sectionValue_neg, map_neg, coefficient_one,
      Fin.val_zero, Fin.val_one, htwo, Fin.reduceFinMk, Nat.reduceSub,
      pow_zero, pow_one, add_zero, TensorProduct.neg_tmul, TensorProduct.tmul_neg,
      neg_neg]
    abel

theorem order_two :
    VanishesQuadraticallyAlongDiagonal P.structureMap
      (externalSquareLine P.structureMap (identityCurveContact P).sequence.line).sheaf
      (P1BivectorConstruction.bivector P) := by
  apply section_vanishes_of_cover_coefficients_mem P.structureMap chartOpen
    chartOpen_cover chartOpen_affine (derivativeFrame P) (derivativeFrame P)
    (P1BivectorConstruction.bivector P) (P1BivectorConstruction.expansion P).tensor
    (P1BivectorConstruction.expansion P).tensor_image.symm 2
  intro i
  rw [coefficient_tensor]
  exact P1SourceAlgebra.tensor_square_mem (K := ℂ)
    (coordinateFunction P i)

end LeBrunSalamon.P1BivectorVanishing

end
/- END LSP1BivectorVanishing -/

/- BEGIN checked source-bivector proof: LSP1BivectorAssembly -/

/-! Assembly of the actual, uniquely normalized source tensor. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Core LeBrunSalamon.Skeleton

namespace LeBrunSalamon.P1BivectorAssembly

theorem existsUnique (P : ProjectiveLineOverC) :
    ∃! B : ExternalSquareSections (projectiveLineVariety P)
        (identityCurveContact P).sequence.line,
      IsSymmetricExternalSection P.structureMap (identityCurveContact P).sequence.line B ∧
      VanishesQuadraticallyAlongDiagonal P.structureMap
        (externalSquareLine P.structureMap (identityCurveContact P).sequence.line).sheaf B ∧
      HasNormalizedContactSymbol (identityCurveContact P) B := by
  refine ⟨P1BivectorConstruction.bivector P,
    ⟨P1BivectorConstruction.symmetric P, P1BivectorVanishing.order_two P,
      P1BivectorNormalization.normalized P⟩, ?_⟩
  intro B hB
  exact P1BivectorUniqueness.unique P (P1BivectorConstruction.bivector P)
    hB.2.1 hB.2.2 (P1BivectorVanishing.order_two P)
    (P1BivectorNormalization.normalized P)

end LeBrunSalamon.P1BivectorAssembly

end
/- END LSP1BivectorAssembly -/

namespace LeBrunSalamon.Skeleton

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseFour
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTen
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFive LeBrunSalamon.Core

/-- The uniquely normalized diagonal tensor on the actual tangent line of `P¹`.
The four global vector-field terms are constructed explicitly; vanishing,
symbol normalization and uniqueness are proved in the preceding sections. -/
theorem _root_.LeBrunSalamon.PublishedInputs.ProjectiveLineGeometry.normalizedSourceBivector
    (P : ProjectiveLineOverC) :
    ∃! B : ExternalSquareSections (projectiveLineVariety P)
        (identityCurveContact P).sequence.line,
      IsSymmetricExternalSection P.structureMap (identityCurveContact P).sequence.line B ∧
      VanishesQuadraticallyAlongDiagonal P.structureMap
        (externalSquareLine P.structureMap (identityCurveContact P).sequence.line).sheaf B ∧
      HasNormalizedContactSymbol (identityCurveContact P) B := by
  exact P1BivectorAssembly.existsUnique P

/-- Project wrapper for the normalized source bivector. -/
theorem sourceBivector_existsUnique (P : ProjectiveLineOverC) :
    ∃! B : ExternalSquareSections (projectiveLineVariety P)
        (identityCurveContact P).sequence.line,
      IsSymmetricExternalSection P.structureMap (identityCurveContact P).sequence.line B ∧
      VanishesQuadraticallyAlongDiagonal P.structureMap
        (externalSquareLine P.structureMap (identityCurveContact P).sequence.line).sheaf B ∧
      HasNormalizedContactSymbol (identityCurveContact P) B :=
  LeBrunSalamon.PublishedInputs.ProjectiveLineGeometry.normalizedSourceBivector P

def sourceBivector (P : ProjectiveLineOverC) :=
  Classical.choose (sourceBivector_existsUnique P)

/-- The canonical contact velocity; no chosen normal sequence occurs. -/
def curveContactVelocity (P : ProjectiveLineOverC) {n : ℕ}
    {X : SmoothProperComplexVariety (2*n+1)} (C : IntrinsicContactStructure X)
    (f : RationalCurve P X) :
    tangentSheaf P.structureMap ⟶ pullbackModule f.map C.sequence.line.sheaf :=
  differentialOver (projectiveLineVariety P) X f.map f.overC ≫
    (Scheme.Modules.pullback f.map).map C.sequence.form

/-- The manuscript's full-family formula, as equality of actual sheaf sections on P1 x P1. A finite
expansion avoids arbitrary tensor-pullback isomorphisms. Existence of an expansion rules out vacuity. -/
def CurveKernelIdentity (P : ProjectiveLineOverC) {n : ℕ}
    {X : SmoothProperComplexVariety (2*n+1)} (C : IntrinsicContactStructure X)
    (f : RationalCurve P X) (B : ExternalSquareSections X C.sequence.line) : Prop :=
  ∃ E : ExternalExpansion X C.sequence.line B,
    (∑ i, externalProductSection P.structureMap
      (pullSection f.map (E.left i)) (pullSection f.map (E.right i))) =
    sourceBivector P ≫ externalTensorMap P.structureMap
      (curveContactVelocity P C f) (curveContactVelocity P C f)

/-- Source des:family. This is the OUTPUT of extension and descent, not a definition of their proper
algebraic-space source. It has no normalized-symbol or jet-generation field. -/
structure FullFamilyKernel (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X) where
  family : FullConicNeighborhood P p X g
  kernel : ExternalSquareSections X.variety X.contact.sequence.line
  symmetry : IsSymmetricExternalSection X.variety.structureMap X.contact.sequence.line kernel
  fullIdentity : ∀ t, CurveKernelIdentity P X.contact (family.curveAt t) kernel



/-- The requested PROOF cut comprises ext:moving-pair and des:family. It must be implemented using the
manuscript's proper algebraic space, OR a justified proper scheme-cover correspondence. A full Hom-family
need not lift to a chosen proper scheme cover: one must pull back that cover to the family and descend the
identity. Never assume such a lift. -/
def MovingPairAndDescent (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) : Prop :=
  ∀ (n : ℕ) (X : ContactFanoManifold n), HasPrimitiveContactPicard X.contact →
    ∀ g : VeryFreeContactConic P p X, Nonempty (FullFamilyKernel P p X g)

/-- A separate proof obligation, not an axiom hidden in FullFamilyKernel. -/
def FamilyToDiagonal (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) : Prop :=
  ∀ (n : ℕ) (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X)
    (D : FullFamilyKernel P p X g),
    ∃ K : NormalizedContactKernel X.variety X.contact, K.twoPointSection = D.kernel

/-- The analytic/algebraic global symmetric-jet theorem is exposed as
an input. Assembly need not call an untracked admitted target. -/
def SymmetricJetCriterion : Prop :=
  ∀ (n : ℕ) (X : SmoothProperComplexVariety (2*n+1))
    (C : IntrinsicContactStructure X) (K : NormalizedContactKernel X C),
      SeparatesFirstJets X C.sequence.line

/-! ## D. A regular connected algebraic contact action -/

structure GroupSchemeData where
  scheme : Scheme
  toC : scheme ⟶ ComplexBase
  unit : ComplexBase ⟶ scheme
  multiply : pullback toC toC ⟶ scheme
  inverse : scheme ⟶ scheme
  unit_over : unit ≫ toC = 𝟙 ComplexBase
  multiply_over : multiply ≫ toC = pullback.fst toC toC ≫ toC
  inverse_over : inverse ≫ toC = toC

namespace GroupSchemeData

def oneAt (G : GroupSchemeData) (T : Scheme) (sT : T ⟶ ComplexBase) :
    PointsOver T sT G.scheme G.toC :=
  ⟨sT ≫ G.unit, by simp [Category.assoc, G.unit_over]⟩

def mulAt (G : GroupSchemeData) {T : Scheme} {sT : T ⟶ ComplexBase}
    (g h : PointsOver T sT G.scheme G.toC) : PointsOver T sT G.scheme G.toC :=
  ⟨pairOver g h ≫ G.multiply, by
    simp [Category.assoc, G.multiply_over, pairOver, g.property]⟩

def invAt (G : GroupSchemeData) {T : Scheme} {sT : T ⟶ ComplexBase}
    (g : PointsOver T sT G.scheme G.toC) : PointsOver T sT G.scheme G.toC :=
  ⟨g.val ≫ G.inverse, by simp [Category.assoc, G.inverse_over, g.property]⟩

end GroupSchemeData

/-- Smooth affine group over C. Smoothness plus affineness makes the
structure map finite type here. Identities hold on ALL test schemes. -/
structure ConnectedAlgebraicGroup where
  data : GroupSchemeData
  smooth : Smooth data.toC
  affine : IsAffine data.scheme
  connected : ConnectedSpace data.scheme
  associative : ∀ (T : Scheme) (sT : T ⟶ ComplexBase)
    (a b c : PointsOver T sT data.scheme data.toC),
    data.mulAt (data.mulAt a b) c = data.mulAt a (data.mulAt b c)
  one_mul : ∀ (T : Scheme) (sT : T ⟶ ComplexBase)
    (g : PointsOver T sT data.scheme data.toC), data.mulAt (data.oneAt T sT) g = g
  mul_one : ∀ (T : Scheme) (sT : T ⟶ ComplexBase)
    (g : PointsOver T sT data.scheme data.toC), data.mulAt g (data.oneAt T sT) = g
  inv_mul : ∀ (T : Scheme) (sT : T ⟶ ComplexBase)
    (g : PointsOver T sT data.scheme data.toC), data.mulAt (data.invAt g) g = data.oneAt T sT
  mul_inv : ∀ (T : Scheme) (sT : T ⟶ ComplexBase)
    (g : PointsOver T sT data.scheme data.toC), data.mulAt g (data.invAt g) = data.oneAt T sT

structure RegularActionData (G : ConnectedAlgebraicGroup) {d : ℕ}
    (X : SmoothProperComplexVariety d) where
  action : pullback G.data.toC X.structureMap ⟶ X.scheme
  overC : action ≫ X.structureMap = pullback.snd G.data.toC X.structureMap ≫ X.structureMap

def RegularActionData.applyPoint {G : ConnectedAlgebraicGroup} {d : ℕ}
    {X : SmoothProperComplexVariety d} (A : RegularActionData G X)
    {T : Scheme} {sT : T ⟶ ComplexBase}
    (g : PointsOver T sT G.data.scheme G.data.toC)
    (x : PointsOver T sT X.scheme X.structureMap) : PointsOver T sT X.scheme X.structureMap :=
  ⟨pairOver g x ≫ A.action, by
    simp [Category.assoc, A.overC, pairOver, x.property]⟩

def RegularActionData.translation {G : ConnectedAlgebraicGroup} {d : ℕ}
    {X : SmoothProperComplexVariety d} (A : RegularActionData G X)
    (g : PointsOver ComplexBase (𝟙 ComplexBase) G.data.scheme G.data.toC) :
    X.scheme ⟶ X.scheme :=
  pullback.lift (X.structureMap ≫ g.val) (𝟙 X.scheme) (by
    simp [Category.assoc, g.property]) ≫ A.action

/-- This is genuinely algebraic in the GROUP parameter, unlike the
legacy action of an abstract group through scheme automorphisms. -/
structure AlgebraicContactAction {n : ℕ} (X : ContactFanoManifold n) where
  group : ConnectedAlgebraicGroup
  data : RegularActionData group X.variety
  unitLaw : ∀ (T : Scheme) (sT : T ⟶ ComplexBase)
    (x : PointsOver T sT X.variety.scheme X.variety.structureMap),
    data.applyPoint (group.data.oneAt T sT) x = x
  actionLaw : ∀ (T : Scheme) (sT : T ⟶ ComplexBase)
    (g h : PointsOver T sT group.data.scheme group.data.toC)
    (x : PointsOver T sT X.variety.scheme X.variety.structureMap),
    data.applyPoint (group.data.mulAt g h) x = data.applyPoint g (data.applyPoint h x)
  contact : ∀ g : PointsOver ComplexBase (𝟙 ComplexBase) group.data.scheme group.data.toC,
    ∃ e : ContactIso X.variety X.variety X.contact X.contact,
      e.schemeIso.hom = data.translation g
  effective : ∀ g : PointsOver ComplexBase (𝟙 ComplexBase) group.data.scheme group.data.toC,
    (∀ x : PointsOver ComplexBase (𝟙 ComplexBase) X.variety.scheme X.variety.structureMap,
      data.applyPoint g x = x) → g = group.data.oneAt ComplexBase (𝟙 ComplexBase)
  transitive : ∀ x y : PointsOver ComplexBase (𝟙 ComplexBase)
      X.variety.scheme X.variety.structureMap,
    ∃ g, data.applyPoint g x = y

/-- Values of ACTUAL global Hamiltonian fields, not fields on affine charts. -/
def HamiltoniansSpan {n : ℕ} (X : ContactFanoManifold n) : Prop :=
  ∀ (x : ComplexPoint X.variety)
    (v : TangentEvaluationAt n (intrinsicAsCandidate X.variety X.contact) x),
    ∃ a : AlgebraicSection X.contact.sequence.line.sheaf,
      restrictSection x.map
        (intrinsicHamiltonianSectionField X.variety X.contact a) = v

def HamiltonianEvaluation : Prop :=
  ∀ (n : ℕ) (X : ContactFanoManifold n),
    SeparatesFirstJets X.variety X.contact.sequence.line → HamiltoniansSpan X

/-- SOURCE jet:transitive. Algebraization and the faithful
anticanonical representation are part of this obligation. -/
def AlgebraicIntegration : Prop :=
  ∀ (n : ℕ) (X : ContactFanoManifold n),
    HamiltoniansSpan X → Nonempty (AlgebraicContactAction X)

/-! ## E. Projective coordinates and the actual adjoint-image target -/

/-- An explicit C-scalar as a unit-sheaf endomorphism on Spec C. -/
def scalarUnitSection (c : ℂ) : AlgebraicSection (structureModule ComplexBase) :=
  sectionFromValue (E := structureModule ComplexBase)
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)



def TupleGenerates {X : Scheme} {N : ℕ} (L : LineBundle X)
    (a : Fin (N+1) → AlgebraicSection L.sheaf) : Prop :=
  Epi (Sigma.desc a : (∐ (fun _ : Fin (N+1) => structureModule X)) ⟶ L.sheaf)

/-- The tautological quotient on the ACTUAL Proj scheme, specified by its universal property for all test
schemes and all generating tuples. It constrains the line and tuple together.
It does not yet identify this presentation with the fixed homogeneous variables:
pullback by a projective automorphism preserves the stated universal property. -/
structure ProjectiveCoordinates (N : ℕ) where
  hyperplane : LineBundle (ComplexProjectiveSpace N)
  coordinate : Fin (N+1) → AlgebraicSection hyperplane.sheaf
  generates : TupleGenerates hyperplane coordinate
  universal : ∀ (T : Scheme) (sT : T ⟶ ComplexBase) (L : LineBundle T)
    (a : Fin (N+1) → AlgebraicSection L.sheaf), TupleGenerates L a →
    ∃! f : PointsOver T sT (ComplexProjectiveSpace N) (projectiveBaseMap N),
      ∃ e : pullbackModule f.val hyperplane.sheaf ≅ L.sheaf,
        ∀ i, pullSection f.val (coordinate i) ≫ e.hom = a i

/-- **Published input (universal quotient on projective space).**
`P^N` carries `O(1)` and its `N+1` tautological generating sections, and this
pair represents invertible sheaves equipped with a generating tuple.  This is
the universal property of projective space (Stacks Project, Section 27.13,
in particular Lemma 27.13.1, Tag 01ND). -/
theorem _root_.LeBrunSalamon.PublishedInputs.ProjectiveLineGeometry.projectiveCoordinates
    (N : ℕ) : Nonempty (ProjectiveCoordinates N) := by
  obtain ⟨L, hL, a, ha, h⟩ :=
    LeBrunSalamon.PublishedInputs.ProjectiveSpace.universalInvertibleQuotient ℂ N
  refine ⟨{ hyperplane := ⟨L, hL⟩
            coordinate := a
            generates := ha
            universal := ?_ }⟩
  intro T s F b hb
  have hmap := h T s F.sheaf F.locallyFree b hb
  simpa only [PointsOver, LeBrunSalamon.ProjectiveQuotient.toSpec,
    projectiveBaseMap, LeBrunSalamon.ProjectiveQuotient.constants,
    constantsToDegreeZero, LeBrunSalamon.ProjectiveQuotient.space] using hmap

/-- Project wrapper for the universal projective-coordinate presentation. -/
theorem projectiveCoordinates_exists (N : ℕ) : Nonempty (ProjectiveCoordinates N) :=
  LeBrunSalamon.PublishedInputs.ProjectiveLineGeometry.projectiveCoordinates N

def projectiveCoordinates (N : ℕ) : ProjectiveCoordinates N :=
  Classical.choice (projectiveCoordinates_exists N)

/-- Homogeneous coordinates are tied to the universal quotient. An
arbitrary bijection between complex points and lines is not accepted. -/
def ProjectiveCoordinates.Represents {N : ℕ} (P : ProjectiveCoordinates N)
    (x : PointsOver ComplexBase (𝟙 ComplexBase)
      (ComplexProjectiveSpace N) (projectiveBaseMap N)) (v : Fin (N+1) → ℂ) : Prop :=
  v ≠ 0 ∧ ∃ e : pullbackModule x.val P.hyperplane.sheaf ≅ structureModule ComplexBase,
    ∀ i, pullSection x.val (P.coordinate i) ≫ e.hom = scalarUnitSection (v i)



noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton

namespace ProjectiveCoordinateProof

/-- The normalized scalar section is the actual scalar endomorphism. -/
theorem scalarUnitSection_eq_scalarEnd (c : ℂ) :
    scalarUnitSection c = GlobalScalars.scalarEnd (structureModule ComplexBase)
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) := by
  apply (sectionValue_bijective (structureModule ComplexBase)).injective
  rw [scalarUnitSection, sectionFromValue_spec]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c =
    (GlobalScalars.scalarEnd (structureModule ComplexBase)
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)).app ⊤ (1 : RingSections ComplexBase ⊤)
  simp [GlobalScalars.scalarEnd_app, smul_eq_mul]

/-- Global unit-sheaf endomorphisms on Spec C are determined by their scalar. -/
theorem scalarUnitSection_injective : Function.Injective scalarUnitSection := by
  intro c d h
  have hh := congrArg
    (fun a : AlgebraicSection (structureModule ComplexBase) =>
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (sectionValue a)) h
  simpa only [scalarUnitSection, sectionFromValue_spec, Iso.inv_hom_id_apply] using hh

/-- Every actual endomorphism of the unit sheaf on Spec C has this form. -/
theorem scalarUnitSection_surjective : Function.Surjective scalarUnitSection := by
  intro a
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (sectionValue a), ?_⟩
  apply (sectionValue_bijective (structureModule ComplexBase)).injective
  rw [scalarUnitSection, sectionFromValue_spec]
  exact Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of ℂ)) (sectionValue a)

/-- Scalar multiplication agrees with composition of the actual sections. -/
theorem scalarUnitSection_mul (c d : ℂ) :
    scalarUnitSection (c * d) = scalarUnitSection c ≫ scalarUnitSection d := by
  simp only [scalarUnitSection_eq_scalarEnd, map_mul, GlobalScalars.scalarEnd_mul]

/-- A nonzero scalar acts by an isomorphism of the actual unit sheaf. -/
theorem scalarUnitSection_isIso (c : ℂ) (hc : c ≠ 0) :
    IsIso (scalarUnitSection c) := by
  let u : (RingSections ComplexBase ⊤)ˣ :=
    Units.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom.toMonoidHom
      (Units.mk0 c hc)
  rw [scalarUnitSection_eq_scalarEnd]
  change IsIso (GlobalScalars.scalarIso (structureModule ComplexBase) u).hom
  infer_instance

/-- A nonzero tuple generates the trivial line, also when N is zero. -/
theorem scalarUnitTuple_generates {N : ℕ}
    (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    TupleGenerates (trivialLine ComplexBase) (fun i => scalarUnitSection (v i)) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    funext i
    change v i = 0
    by_contra hi
    exact h ⟨i, hi⟩
  letI : IsIso (scalarUnitSection (v i)) := scalarUnitSection_isIso (v i) hi
  change Epi (Sigma.desc (fun j => scalarUnitSection (v j)))
  exact epi_of_epi_fac (Sigma.ι_comp_desc (fun j => scalarUnitSection (v j)) i)

/-- The supplied quotient universal property supplies a unique actual map. -/
theorem projectiveCoordinates_pointOfVector {N : ℕ} (P : ProjectiveCoordinates N)
    (v : Fin (N+1) → ℂ) (hv : v ≠ 0) :
    ∃! x, P.Represents x v := by
  obtain ⟨x, hx, huniq⟩ := P.universal ComplexBase (𝟙 ComplexBase)
    (trivialLine ComplexBase) (fun i => scalarUnitSection (v i))
    (scalarUnitTuple_generates v hv)
  refine ⟨x, ⟨hv, hx⟩, ?_⟩
  intro y hy
  exact huniq y hy.2

/-- Frame change has precisely the orientation w = c • v. -/
theorem projectiveCoordinates_samePoint_iff {N : ℕ} (P : ProjectiveCoordinates N)
    (x y : PointsOver ComplexBase (𝟙 ComplexBase)
      (ComplexProjectiveSpace N) (projectiveBaseMap N)) (v w : Fin (N+1) → ℂ)
    (hx : P.Represents x v) (hy : P.Represents y w) :
    x = y ↔ ∃ c : ℂ, c ≠ 0 ∧ w = c • v := by
  constructor
  · intro hxy
    subst y
    obtain ⟨_, e, he⟩ := hx
    obtain ⟨hw, f, hf⟩ := hy
    obtain ⟨c, hc⟩ := scalarUnitSection_surjective (e.inv ≫ f.hom)
    have hcw : w = c • v := by
      funext i
      change w i = c * v i
      apply scalarUnitSection_injective
      calc
        scalarUnitSection (w i) = pullSection x.val (P.coordinate i) ≫ f.hom :=
          (hf i).symm
        _ = (pullSection x.val (P.coordinate i) ≫ e.hom) ≫ (e.inv ≫ f.hom) := by
          simp only [Category.assoc, e.hom_inv_id_assoc]
        _ = scalarUnitSection (v i) ≫ scalarUnitSection c := by rw [he i, hc]
        _ = scalarUnitSection (v i * c) := (scalarUnitSection_mul (v i) c).symm
        _ = scalarUnitSection (c * v i) := by rw [mul_comm]
    refine ⟨c, ?_, hcw⟩
    intro hc0
    apply hw
    rw [hcw, hc0, zero_smul]
  · rintro ⟨c, hc, hcw⟩
    obtain ⟨_, e, he⟩ := hx
    letI : IsIso (scalarUnitSection c) := scalarUnitSection_isIso c hc
    have hxw : P.Represents x w := by
      refine ⟨hy.1, e ≪≫ asIso (scalarUnitSection c), ?_⟩
      intro i
      change pullSection x.val (P.coordinate i) ≫
        (e.hom ≫ scalarUnitSection c) = scalarUnitSection (w i)
      rw [← Category.assoc, he i, ← scalarUnitSection_mul, hcw]
      change scalarUnitSection (v i * c) = scalarUnitSection (c * v i)
      rw [mul_comm]
    obtain ⟨_, _, huniq⟩ := projectiveCoordinates_pointOfVector P w hy.1
    exact (huniq x hxw).trans (huniq y hy).symm

end ProjectiveCoordinateProof

namespace ProjectiveCoordinateProof

/-- A rank-one sheaf has an actual frame after pullback to a complex point.
The frame is obtained by factoring the point through a local free frame. -/
theorem line_at_complex_point_trivial {Y : Scheme} (L : LineBundle Y)
    (x : ComplexBase ⟶ Y) :
    Nonempty (pullbackModule x L.sheaf ≅ structureModule ComplexBase) := by
  obtain ⟨q, hq, hr⟩ := L.locallyFree
  letI := hq
  have hcover := (_root_.Opens.coversTop_iff Y q.X).mp q.coversTop
  obtain ⟨i, hi⟩ := hcover.exists_mem (x (IsLocalRing.closedPoint ℂ))
  let U : Y.Opens := q.X i
  have hxU : Set.range x ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change x z ∈ U
    rw [Subsingleton.elim z (IsLocalRing.closedPoint ℂ)]
    exact hi
  let g := IsOpenImmersion.lift U.ι x hxU
  have hg : g ≫ U.ι = x := IsOpenImmersion.lift_fac U.ι x hxU
  let e : structureModule U.toScheme ≅ pullbackModule U.ι L.sheaf :=
    (coproductUniqueIso (fun _ : Fin 1 => structureModule U.toScheme)).symm ≪≫
      DominantSectionInjectivityProof.localFreePullbackIso q hr i
  let c : pullbackModule g (pullbackModule U.ι L.sheaf) ≅
      pullbackModule x L.sheaf :=
    (Scheme.Modules.pullbackComp g U.ι).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr hg).app L.sheaf
  exact ⟨c.symm ≪≫ (Scheme.Modules.pullback g).mapIso e.symm ≪≫ unitPullbackIso g⟩

/-- Pulling back a generating tuple and trivializing its line produces
a generating tuple of endomorphisms of the actual structure module. -/
theorem pulled_tuple_generates {Y : Scheme} {N : ℕ} (L : LineBundle Y)
    (a : Fin (N+1) → AlgebraicSection L.sheaf) (ha : TupleGenerates L a)
    (x : ComplexBase ⟶ Y)
    (e : pullbackModule x L.sheaf ≅ structureModule ComplexBase) :
    Epi (Sigma.desc (fun i => pullSection x (a i) ≫ e.hom)) := by
  let F : SheafOfModules.{0} Y.ringCatSheaf ⥤
      SheafOfModules.{0} ComplexBase.ringCatSheaf := Scheme.Modules.pullback x
  letI : F.IsLeftAdjoint :=
    (SheafOfModules.pullbackPushforwardAdjunction x.toRingCatSheafHom).isLeftAdjoint
  let q : SheafOfModules.free (R := Y.ringCatSheaf) (Fin (N+1)) ⟶ L.sheaf :=
    Sigma.desc a
  letI : Epi q := ha
  letI : Epi (F.map q) := inferInstance
  let c := SheafOfModules.mapFreeIso F (Fin (N+1)) (unitPullbackIso x).symm
  have h : Sigma.desc (fun i => pullSection x (a i) ≫ e.hom) =
      c.hom ≫ F.map q ≫ e.hom := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc]
    change pullSection x (a i) ≫ e.hom =
      SheafOfModules.ιFree i ≫ c.hom ≫ F.map q ≫ e.hom
    erw [SheafOfModules.ιFree_mapFreeIso_hom_assoc,
      ← Functor.map_comp_assoc]
    simp only [q, SheafOfModules.ιFree, Sigma.ι_comp_desc,
      pullSection, restrictSection, F, Iso.symm_hom, Category.assoc]
  rw [h]
  infer_instance

/-- A generating scalar tuple cannot vanish identically: the identity
endomorphism of the structure sheaf remains nonzero at Spec C. -/
theorem scalar_tuple_ne_zero {N : ℕ} (v : Fin (N+1) → ℂ)
    (hv : Epi (Sigma.desc (fun i => scalarUnitSection (v i)))) : v ≠ 0 := by
  intro hzero
  let q := Sigma.desc (fun i => scalarUnitSection (v i))
  letI : Epi q := hv
  have hq : q = 0 := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc, comp_zero]
    have hi : v i = 0 := congrFun hzero i
    rw [hi, scalarUnitSection_eq_scalarEnd]
    simp only [map_zero, GlobalScalars.scalarEnd_zero]
  have hid : (𝟙 (structureModule ComplexBase)) = 0 := by
    apply (cancel_epi q).mp
    simp only [Category.comp_id, comp_zero, hq]
  have hc := congrArg
    (fun f : structureModule ComplexBase ⟶ structureModule ComplexBase =>
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        (f.app ⊤ (1 : RingSections ComplexBase ⊤))) hid
  have hone : (1 : ℂ) = 0 := by simpa using hc
  exact one_ne_zero hone

end ProjectiveCoordinateProof

theorem projectiveCoordinates_representatives {N : ℕ} (P : ProjectiveCoordinates N)
    (x : PointsOver ComplexBase (𝟙 ComplexBase)
      (ComplexProjectiveSpace N) (projectiveBaseMap N)) :
    ∃ v, P.Represents x v := by
  classical
  obtain ⟨e⟩ := ProjectiveCoordinateProof.line_at_complex_point_trivial P.hyperplane x.val
  choose v hv using fun i => ProjectiveCoordinateProof.scalarUnitSection_surjective
    (pullSection x.val (P.coordinate i) ≫ e.hom)
  refine ⟨v, ?_, e, ?_⟩
  · apply ProjectiveCoordinateProof.scalar_tuple_ne_zero
    have he := ProjectiveCoordinateProof.pulled_tuple_generates P.hyperplane
      P.coordinate P.generates x.val e
    have htuple : (fun i => pullSection x.val (P.coordinate i) ≫ e.hom) =
        (fun i => scalarUnitSection (v i)) := by
      funext i
      exact (hv i).symm
    rwa [htuple] at he
  · intro i
    exact (hv i).symm

end

theorem projectiveCoordinates_samePoint_iff {N : ℕ} (P : ProjectiveCoordinates N)
    (x y : PointsOver ComplexBase (𝟙 ComplexBase)
      (ComplexProjectiveSpace N) (projectiveBaseMap N)) (v w : Fin (N+1) → ℂ)
    (hx : P.Represents x v) (hy : P.Represents y w) :
    x = y ↔ ∃ c : ℂ, c ≠ 0 ∧ w = c • v := by
  exact ProjectiveCoordinateProof.projectiveCoordinates_samePoint_iff P x y v w hx hy

/-- Existence, not just uniqueness up to scaling, of projective points. -/
theorem projectiveCoordinates_pointOfVector {N : ℕ} (P : ProjectiveCoordinates N)
    (v : Fin (N+1) → ℂ) (hv : v ≠ 0) :
    ∃! x, P.Represents x v := by
  exact ProjectiveCoordinateProof.projectiveCoordinates_pointOfVector P v hv

/-- The first coordinate point in the chosen universal presentation is a genuine
complex point. Equality with the explicit Proj-chart point [1:0] is not established. -/
def canonicalMarkedPoint : ProjectiveLinePoint canonicalProjectiveLine := by
  let v : Fin 2 → ℂ := Pi.single 0 1
  have hv : v ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simpa [v] using h0
  let x := Classical.choose (projectiveCoordinates_pointOfVector (projectiveCoordinates 1) v hv)
  exact ⟨x.val, x.property⟩

section AdjointTupleSection

set_option backward.isDefEq.respectTransparency false

namespace AdjointComparisonProof

open Core.ExternalTensorCoordinates

/-- The finite matrix of a linear map acts on tuples in any complex
module. The coefficients are the images of the actual standard vectors. -/
def transformValues {ι κ V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V]
    (T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) (a : ι → V) : κ → V :=
  fun j => ∑ i, T (Pi.single i 1) j • a i

theorem linearMap_coordinate {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) (a : ι → ℂ) (j : κ) :
    T a j = ∑ i, T (Pi.single i 1) j * a i := by
  have ha : a = ∑ i, a i • Pi.single i 1 := by
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using
      (LinearMap.sum_single_apply (fun _ : ι => ℂ) a).symm
  calc
    T a j = T (∑ i, a i • Pi.single i 1) j := congrArg (fun v => T v j) ha
    _ = ∑ i, a i * T (Pi.single i 1) j := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    _ = _ := Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem transformValues_id {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V] (a : ι → V) :
    transformValues (LinearMap.id : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) a = a := by
  funext j
  simp [transformValues, Pi.single_apply]

theorem transformValues_comp {ι κ «λ» V : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [AddCommGroup V] [Module ℂ V]
    (T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) (U : (κ → ℂ) →ₗ[ℂ] («λ» → ℂ))
    (a : ι → V) :
    transformValues U (transformValues T a) = transformValues (U.comp T) a := by
  funext k
  simp only [transformValues, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_smul]
  rw [LinearMap.comp_apply, linearMap_coordinate U (T (Pi.single i 1)) k]

theorem transformValues_map {ι κ V W : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) (q : V →ₗ[ℂ] W) (a : ι → V) (j : κ) :
    q (transformValues T a j) = transformValues T (fun i => q (a i)) j := by
  simp only [transformValues, map_sum, map_smul]

/-- The same finite linear combination of actual algebraic sections,
using the complex scalar structure from the specified structure map. -/
def transformSections {Y : Scheme} (s : Y ⟶ ComplexBase) {E : OModule Y}
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) (a : ι → AlgebraicSection E) :
    κ → AlgebraicSection E :=
  fun j => sectionFromValue
    (transformValues (V := ComplexSections s E) T (fun i => (sectionValue (a i) : ComplexSections s E)) j)

theorem transformSections_value {Y : Scheme} (s : Y ⟶ ComplexBase) {E : OModule Y}
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) (a : ι → AlgebraicSection E) (j : κ) :
    (sectionValue (transformSections s T a j) : ComplexSections s E) =
      transformValues (V := ComplexSections s E) T (fun i => (sectionValue (a i) : ComplexSections s E)) j :=
  sectionFromValue_spec _

theorem transformSections_id {Y : Scheme} (s : Y ⟶ ComplexBase) {E : OModule Y}
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → AlgebraicSection E) :
    transformSections s (LinearMap.id : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) a = a := by
  funext j
  simp only [transformSections, transformValues_id, sectionFromValue_sectionValue]

theorem transformSections_comp {Y : Scheme} (s : Y ⟶ ComplexBase) {E : OModule Y}
    {ι κ «λ» : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) (U : (κ → ℂ) →ₗ[ℂ] («λ» → ℂ))
    (a : ι → AlgebraicSection E) :
    transformSections s U (transformSections s T a) = transformSections s (U.comp T) a := by
  funext j
  apply (sectionValue_bijective E).injective
  simp only [transformSections_value]
  exact congrFun (transformValues_comp (V := ComplexSections s E) T U
    (fun i => (sectionValue (a i) : ComplexSections s E))) j

theorem transformSections_inverse {Y : Scheme} (s : Y ⟶ ComplexBase) {E : OModule Y}
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (T : (ι → ℂ) ≃ₗ[ℂ] (κ → ℂ)) (a : ι → AlgebraicSection E) :
    transformSections s T.symm.toLinearMap (transformSections s T.toLinearMap a) = a := by
  rw [transformSections_comp]
  have h : T.symm.toLinearMap.comp T.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro v
    change T.symm (T v) = v
    exact T.symm_apply_apply v
  rw [h, transformSections_id]

def postLinear {Y : Scheme} (s : Y ⟶ ComplexBase) {E F : OModule Y} (q : E ⟶ F) :
    ComplexSections s E →ₗ[ℂ] ComplexSections s F where
  toFun := q.app ⊤
  map_add' := (q.app ⊤).hom.map_add
  map_smul' := by
    intro c a
    exact Scheme.Modules.Hom.app_smul q (U := ⊤) (constants s ⊤ c) a

theorem transformSections_post {Y : Scheme} (s : Y ⟶ ComplexBase) {E F : OModule Y}
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) (a : ι → AlgebraicSection E)
    (q : E ⟶ F) (j : κ) :
    transformSections s T a j ≫ q = transformSections s T (fun i => a i ≫ q) j := by
  apply (sectionValue_bijective F).injective
  rw [sectionValue_comp, transformSections_value, transformSections_value]
  exact transformValues_map T (postLinear s q)
    (fun i => (sectionValue (a i) : ComplexSections s E)) j

theorem pullLinear_sectionValue {Y Z : Scheme} (f : Y ⟶ Z)
    (sY : Y ⟶ ComplexBase) (sZ : Z ⟶ ComplexBase) (hf : f ≫ sZ = sY)
    {E : OModule Z} (a : AlgebraicSection E) :
    pullLinear f sY sZ hf E (sectionValue a) = sectionValue (pullSection f a) := by
  change sectionValue (pullSection f (sectionFromValue (sectionValue a))) =
    sectionValue (pullSection f a)
  rw [sectionFromValue_sectionValue]

theorem transformSections_pull {Y Z : Scheme} (f : Y ⟶ Z)
    (sY : Y ⟶ ComplexBase) (sZ : Z ⟶ ComplexBase) (hf : f ≫ sZ = sY)
    {E : OModule Z} {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) (a : ι → AlgebraicSection E) (j : κ) :
    pullSection f (transformSections sZ T a j) =
      transformSections sY T (fun i => pullSection f (a i)) j := by
  apply (sectionValue_bijective (pullbackModule f E)).injective
  rw [← pullLinear_sectionValue f sY sZ hf, transformSections_value,
    transformSections_value]
  simpa only [pullLinear_sectionValue] using
    transformValues_map T (pullLinear f sY sZ hf E)
      (fun i => (sectionValue (a i) : ComplexSections sZ E)) j

/-- An invertible constant matrix preserves generation of the actual
line sheaf. The old quotient factors through the new tuple quotient. -/
theorem tupleGenerates_transform {Y : Scheme} (s : Y ⟶ ComplexBase)
    {N M : ℕ} (L : LineBundle Y)
    (T : (Fin (N+1) → ℂ) ≃ₗ[ℂ] (Fin (M+1) → ℂ))
    (a : Fin (N+1) → AlgebraicSection L.sheaf) (ha : TupleGenerates L a) :
    TupleGenerates L (transformSections s T.toLinearMap a) := by
  classical
  let b := transformSections s T.toLinearMap a
  let q := Sigma.desc b
  let j : Fin (M+1) → AlgebraicSection (∐ fun _ : Fin (M+1) => structureModule Y) :=
    fun k => Sigma.ι (fun _ : Fin (M+1) => structureModule Y) k
  let u := Sigma.desc (transformSections s T.symm.toLinearMap j)
  have hfac : u ≫ q = Sigma.desc a := by
    apply Sigma.hom_ext
    intro i
    dsimp only [u]
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, transformSections_post]
    have hq : (fun k => j k ≫ q) = b := by
      funext k
      exact Sigma.ι_comp_desc b k
    rw [hq]
    exact congrFun (transformSections_inverse s T a) i
  letI : Epi (Sigma.desc a) := ha
  exact epi_of_epi_fac hfac

/-- At Spec C the matrix acts on the exact normalized scalar sections. -/
theorem transformSections_scalar {N M : ℕ}
    (T : (Fin (N+1) → ℂ) →ₗ[ℂ] (Fin (M+1) → ℂ))
    (a : Fin (N+1) → ℂ) (j : Fin (M+1)) :
    transformSections (𝟙 ComplexBase) T (fun i => scalarUnitSection (a i)) j =
      scalarUnitSection (T a j) := by
  apply (sectionValue_bijective (structureModule ComplexBase)).injective
  rw [transformSections_value]
  simp only [scalarUnitSection, sectionFromValue_spec]
  rw [linearMap_coordinate T a j, map_sum]
  change (∑ i, constants (𝟙 ComplexBase) ⊤ (T (Pi.single i 1) j) *
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv (a i)) = _
  simp only [constants_top, Scheme.Hom.id_appTop, CategoryTheory.id_apply, map_mul]

end AdjointComparisonProof

end AdjointTupleSection


section AdjointProjectiveSection

set_option backward.isDefEq.respectTransparency false

namespace AdjointComparisonProof

/-- Inverse matrices give inverse actual projective maps. This uses
the specified quotient universal property, including its line isomorphism. -/
theorem projective_composite_identity {N M : ℕ}
    (P : ProjectiveCoordinates N) (Q : ProjectiveCoordinates M)
    (T : (Fin (N+1) → ℂ) ≃ₗ[ℂ] (Fin (M+1) → ℂ))
    (f : PointsOver (ComplexProjectiveSpace N) (projectiveBaseMap N)
      (ComplexProjectiveSpace M) (projectiveBaseMap M))
    (g : PointsOver (ComplexProjectiveSpace M) (projectiveBaseMap M)
      (ComplexProjectiveSpace N) (projectiveBaseMap N))
    (l : pullbackModule f.val Q.hyperplane.sheaf ≅ P.hyperplane.sheaf)
    (k : pullbackModule g.val P.hyperplane.sheaf ≅ Q.hyperplane.sheaf)
    (hf : ∀ j, pullSection f.val (Q.coordinate j) ≫ l.hom =
      transformSections (projectiveBaseMap N) T.toLinearMap P.coordinate j)
    (hg : ∀ i, pullSection g.val (P.coordinate i) ≫ k.hom =
      transformSections (projectiveBaseMap M) T.symm.toLinearMap Q.coordinate i) :
    f.val ≫ g.val = 𝟙 (ComplexProjectiveSpace N) := by
  let p := (Scheme.Modules.pullbackComp f.val g.val).app P.hyperplane.sheaf
  let c : pullbackModule (f.val ≫ g.val) P.hyperplane.sheaf ≅ P.hyperplane.sheaf :=
    p.symm ≪≫ (Scheme.Modules.pullback f.val).mapIso k ≪≫ l
  have hc (i : Fin (N+1)) :
      pullSection (f.val ≫ g.val) (P.coordinate i) ≫ c.hom = P.coordinate i := by
    calc
      _ = pullSection f.val (pullSection g.val (P.coordinate i) ≫ k.hom) ≫ l.hom := by
        change pullSection (f.val ≫ g.val) (P.coordinate i) ≫
          (p.inv ≫ (Scheme.Modules.pullback f.val).map k.hom ≫ l.hom) = _
        rw [← LeBrunSalamon.Refinement.CanonicalPullbackSectionProof.pullSection_comp]
        change (pullSection f.val (pullSection g.val (P.coordinate i)) ≫ p.hom) ≫
          (p.inv ≫ (Scheme.Modules.pullback f.val).map k.hom ≫ l.hom) = _
        simp only [Category.assoc, p.hom_inv_id_assoc]
        rw [ExternalExchangeCoherenceProof.pullSection_map, Category.assoc]
      _ = pullSection f.val
          (transformSections (projectiveBaseMap M) T.symm.toLinearMap Q.coordinate i) ≫ l.hom := by
        rw [hg i]
      _ = transformSections (projectiveBaseMap N) T.symm.toLinearMap
          (fun j => pullSection f.val (Q.coordinate j)) i ≫ l.hom := by
        rw [transformSections_pull f.val (projectiveBaseMap N) (projectiveBaseMap M) f.property]
      _ = transformSections (projectiveBaseMap N) T.symm.toLinearMap
          (fun j => pullSection f.val (Q.coordinate j) ≫ l.hom) i :=
        transformSections_post _ _ _ _ _
      _ = transformSections (projectiveBaseMap N) T.symm.toLinearMap
          (transformSections (projectiveBaseMap N) T.toLinearMap P.coordinate) i := by
        simp_rw [hf]
      _ = P.coordinate i := congrFun
        (transformSections_inverse (projectiveBaseMap N) T P.coordinate) i
  let fg : PointsOver (ComplexProjectiveSpace N) (projectiveBaseMap N)
      (ComplexProjectiveSpace N) (projectiveBaseMap N) :=
    ⟨f.val ≫ g.val, by rw [Category.assoc, g.property, f.property]⟩
  let idp : PointsOver (ComplexProjectiveSpace N) (projectiveBaseMap N)
      (ComplexProjectiveSpace N) (projectiveBaseMap N) :=
    ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨a, ha, hu⟩ := P.universal (ComplexProjectiveSpace N) (projectiveBaseMap N)
    P.hyperplane P.coordinate P.generates
  have hfg : fg = a := hu fg ⟨c, hc⟩
  have hid : idp = a := hu idp
    ⟨(Scheme.Modules.pullbackId (ComplexProjectiveSpace N)).app P.hyperplane.sheaf,
      fun i => ExternalExchangeCoherenceProof.pullSection_id (P.coordinate i)⟩
  exact congrArg Subtype.val (hfg.trans hid.symm)

/-- The ordinary linear change of homogeneous coordinates produces an
actual isomorphism of the supplied projective schemes, over C and with
the exact transformed quotient tuple. -/
theorem projectiveIso_of_linearEquiv {N M : ℕ}
    (P : ProjectiveCoordinates N) (Q : ProjectiveCoordinates M)
    (T : (Fin (N+1) → ℂ) ≃ₗ[ℂ] (Fin (M+1) → ℂ)) :
    ∃ e : ComplexProjectiveSpace N ≅ ComplexProjectiveSpace M,
      e.hom ≫ projectiveBaseMap M = projectiveBaseMap N ∧
      ∃ l : pullbackModule e.hom Q.hyperplane.sheaf ≅ P.hyperplane.sheaf,
        ∀ j, pullSection e.hom (Q.coordinate j) ≫ l.hom =
          transformSections (projectiveBaseMap N) T.toLinearMap P.coordinate j := by
  obtain ⟨f, ⟨l, hl⟩, hfuniq⟩ := Q.universal (ComplexProjectiveSpace N)
    (projectiveBaseMap N) P.hyperplane
    (transformSections (projectiveBaseMap N) T.toLinearMap P.coordinate)
    (tupleGenerates_transform (projectiveBaseMap N) P.hyperplane T P.coordinate P.generates)
  obtain ⟨g, ⟨k, hk⟩, hguniq⟩ := P.universal (ComplexProjectiveSpace M)
    (projectiveBaseMap M) Q.hyperplane
    (transformSections (projectiveBaseMap M) T.symm.toLinearMap Q.coordinate)
    (tupleGenerates_transform (projectiveBaseMap M) Q.hyperplane T.symm Q.coordinate Q.generates)
  let e : ComplexProjectiveSpace N ≅ ComplexProjectiveSpace M :=
    { hom := f.val
      inv := g.val
      hom_inv_id := projective_composite_identity P Q T f g l k hl hk
      inv_hom_id := by
        exact projective_composite_identity Q P T.symm g f k l hk hl }
  exact ⟨e, f.property, l, hl⟩

/-- Representation of points transforms through the same actual line
pullback comparison. The matrix and its scalar normalization are explicit. -/
theorem represents_transport {N M : ℕ}
    (P : ProjectiveCoordinates N) (Q : ProjectiveCoordinates M)
    (T : (Fin (N+1) → ℂ) ≃ₗ[ℂ] (Fin (M+1) → ℂ))
    (f : ComplexProjectiveSpace N ⟶ ComplexProjectiveSpace M)
    (hf : f ≫ projectiveBaseMap M = projectiveBaseMap N)
    (l : pullbackModule f Q.hyperplane.sheaf ≅ P.hyperplane.sheaf)
    (hl : ∀ j, pullSection f (Q.coordinate j) ≫ l.hom =
      transformSections (projectiveBaseMap N) T.toLinearMap P.coordinate j)
    (x : PointsOver ComplexBase (𝟙 ComplexBase)
      (ComplexProjectiveSpace N) (projectiveBaseMap N))
    (v : Fin (N+1) → ℂ) (hv : P.Represents x v) :
    Q.Represents ⟨x.val ≫ f, by rw [Category.assoc, hf, x.property]⟩ (T v) := by
  obtain ⟨hvn, a, ha⟩ := hv
  have hTv : T v ≠ 0 := by
    intro h
    exact hvn (T.injective (h.trans (map_zero T).symm))
  let p := (Scheme.Modules.pullbackComp x.val f).app Q.hyperplane.sheaf
  let c : pullbackModule (x.val ≫ f) Q.hyperplane.sheaf ≅ structureModule ComplexBase :=
    p.symm ≪≫ (Scheme.Modules.pullback x.val).mapIso l ≪≫ a
  refine ⟨hTv, c, ?_⟩
  intro j
  calc
    _ = pullSection x.val (pullSection f (Q.coordinate j) ≫ l.hom) ≫ a.hom := by
      change pullSection (x.val ≫ f) (Q.coordinate j) ≫
        (p.inv ≫ (Scheme.Modules.pullback x.val).map l.hom ≫ a.hom) = _
      rw [← LeBrunSalamon.Refinement.CanonicalPullbackSectionProof.pullSection_comp]
      change (pullSection x.val (pullSection f (Q.coordinate j)) ≫ p.hom) ≫
        (p.inv ≫ (Scheme.Modules.pullback x.val).map l.hom ≫ a.hom) = _
      simp only [Category.assoc, p.hom_inv_id_assoc]
      rw [ExternalExchangeCoherenceProof.pullSection_map, Category.assoc]
    _ = pullSection x.val
        (transformSections (projectiveBaseMap N) T.toLinearMap P.coordinate j) ≫ a.hom := by
      rw [hl j]
    _ = transformSections (𝟙 ComplexBase) T.toLinearMap
        (fun i => pullSection x.val (P.coordinate i)) j ≫ a.hom := by
      rw [transformSections_pull x.val (𝟙 ComplexBase) (projectiveBaseMap N) x.property]
    _ = transformSections (𝟙 ComplexBase) T.toLinearMap
        (fun i => pullSection x.val (P.coordinate i) ≫ a.hom) j :=
      transformSections_post _ _ _ _ _
    _ = transformSections (𝟙 ComplexBase) T.toLinearMap
        (fun i => scalarUnitSection (v i)) j := by simp_rw [ha]
    _ = scalarUnitSection (T v j) := transformSections_scalar _ _ _

end AdjointComparisonProof

end AdjointProjectiveSection


structure SimpleLieData where
  carrier : Type
  [lieRing : LieRing carrier]
  [lieAlgebra : LieAlgebra ℂ carrier]
  [finite : Module.Finite ℂ carrier]
  simple : IsSimpleComplexLieAlgebra carrier

attribute [instance] SimpleLieData.lieRing SimpleLieData.lieAlgebra SimpleLieData.finite

/-- Orbit dimension in characteristic zero is rank(ad v). -/
def adjointRank (G : SimpleLieData) (v : G.carrier) : ℕ :=
  Module.finrank ℂ (LinearMap.range ((LieAlgebra.ad ℂ G.carrier) v))

/-- Intrinsic minimality among NONZERO nilpotents, not a marked-orbit
label and not an arbitrary bracket-preserving group action. -/
def IsMinimalNilpotent (G : SimpleLieData) (v : G.carrier) : Prop :=
  v ≠ 0 ∧ IsAdjointNilpotent v ∧
    ∀ w : G.carrier, w ≠ 0 → IsAdjointNilpotent w → adjointRank G v ≤ adjointRank G w

/-- Trace of ad(a) ad(b), with no convention-dependent Killing factor. -/
def killingValue (G : SimpleLieData) (a b : G.carrier) : ℂ :=
  LinearMap.trace ℂ G.carrier
    (((LieAlgebra.ad ℂ G.carrier) a).comp ((LieAlgebra.ad ℂ G.carrier) b))

theorem minimalNilpotent_smul (G : SimpleLieData) (v : G.carrier)
    (c : ℂ) (hc : c ≠ 0) : IsMinimalNilpotent G (c • v) ↔ IsMinimalNilpotent G v := by
  have hnil (w : G.carrier) (b : ℂ) (hw : IsAdjointNilpotent w) :
      IsAdjointNilpotent (b • w) := by
    unfold IsAdjointNilpotent adjointRepresentation at *
    rw [map_smul]
    exact hw.smul b
  have hrank (w : G.carrier) (b : ℂ) (hb : b ≠ 0) :
      adjointRank G (b • w) = adjointRank G w := by
    unfold adjointRank
    rw [map_smul, LinearMap.range_smul _ b hb]
  have hforward (w : G.carrier) (b : ℂ) (hb : b ≠ 0)
      (hw : IsMinimalNilpotent G w) : IsMinimalNilpotent G (b • w) := by
    refine ⟨smul_ne_zero hb hw.1, hnil w b hw.2.1, ?_⟩
    intro z hz hznil
    rw [hrank w b hb]
    exact hw.2.2 z hz hznil
  constructor
  · intro h
    have h' := hforward (c • v) c⁻¹ (inv_ne_zero hc) h
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h'
  · exact hforward v c hc


namespace AdjointComparisonProof

/-- A Lie equivalence conjugates the actual adjoint endomorphism, so it
preserves the original nilpotence predicate. -/
theorem adjointNilpotent_equiv {G H : SimpleLieData}
    (e : G.carrier ≃ₗ⁅ℂ⁆ H.carrier) (v : G.carrier) :
    IsAdjointNilpotent (e v) ↔ IsAdjointNilpotent v := by
  change IsNilpotent ((LieAlgebra.ad ℂ H.carrier) (e v)) ↔
    IsNilpotent ((LieAlgebra.ad ℂ G.carrier) v)
  rw [← LieAlgebra.conj_ad_apply e v]
  change IsNilpotent (e.toLinearEquiv.conjRingEquiv ((LieAlgebra.ad ℂ G.carrier) v)) ↔
    IsNilpotent ((LieAlgebra.ad ℂ G.carrier) v)
  exact IsNilpotent.map_iff (f := e.toLinearEquiv.conjRingEquiv)
    e.toLinearEquiv.conjRingEquiv.injective

/-- The rank used to define the minimal orbit is preserved by the same
actual conjugation, with no choice of orbit representative. -/
theorem adjointRank_equiv {G H : SimpleLieData}
    (e : G.carrier ≃ₗ⁅ℂ⁆ H.carrier) (v : G.carrier) :
    adjointRank H (e v) = adjointRank G v := by
  unfold adjointRank
  rw [← LieAlgebra.conj_ad_apply e v, LinearEquiv.conj_apply,
    LinearEquiv.range_comp, LinearMap.range_comp,
    e.toLinearEquiv.finrank_map_eq]

/-- Minimality among all nonzero nilpotents is invariant under a Lie
equivalence, rather than under an arbitrarily specified group action. -/
theorem minimalNilpotent_equiv {G H : SimpleLieData}
    (e : G.carrier ≃ₗ⁅ℂ⁆ H.carrier) (v : G.carrier) :
    IsMinimalNilpotent H (e v) ↔ IsMinimalNilpotent G v := by
  have forward {A B : SimpleLieData} (q : A.carrier ≃ₗ⁅ℂ⁆ B.carrier)
      (a : A.carrier) (ha : IsMinimalNilpotent A a) :
      IsMinimalNilpotent B (q a) := by
    refine ⟨?_, (adjointNilpotent_equiv q a).mpr ha.2.1, ?_⟩
    · intro hz
      apply ha.1
      exact q.injective (hz.trans (map_zero q).symm)
    · intro b hb hnil
      obtain ⟨c, rfl⟩ := q.surjective b
      change adjointRank B (q a) ≤ adjointRank B (q c)
      rw [adjointRank_equiv q a, adjointRank_equiv q c]
      apply ha.2.2 c
      · intro hc
        exact hb (hc ▸ map_zero q)
      · exact (adjointNilpotent_equiv q c).mp hnil
  constructor
  · intro hv
    simpa only [LieEquiv.symm_apply_apply] using forward e.symm (e v) hv
  · exact forward e v

/-- The Killing scalar convention in the presentation is exactly the
trace convention preserved by Lie equivalences. -/
theorem killingValue_equiv {G H : SimpleLieData}
    (e : G.carrier ≃ₗ⁅ℂ⁆ H.carrier) (v w : G.carrier) :
    killingValue H (e v) (e w) = killingValue G v w := by
  unfold killingValue
  rw [← LieAlgebra.conj_ad_apply e v, ← LieAlgebra.conj_ad_apply e w,
    ← LinearEquiv.conj_comp, LinearMap.trace_conj']

end AdjointComparisonProof


/-- Extend the bracket to O_X(U) by its structure constants in b. -/
def bracketCoordinates (G : SimpleLieData) {N : ℕ}
    (b : Module.Basis (Fin (N+1)) ℂ G.carrier) {X : Scheme}
    (s : X ⟶ ComplexBase) (U : X.Opens)
    (a w : Fin (N+1) → RingSections X U) (i : Fin (N+1)) : RingSections X U :=
  ∑ j, ∑ k, complexConstant s U (b.repr ⁅b j, b k⁆ i) * a j * w k

def killingCoordinates (G : SimpleLieData) {N : ℕ}
    (b : Module.Basis (Fin (N+1)) ℂ G.carrier) {X : Scheme}
    (s : X ⟶ ComplexBase) (U : X.Opens)
    (w a : Fin (N+1) → RingSections X U) : RingSections X U :=
  ∑ j, ∑ k, complexConstant s U (killingValue G (b j) (b k)) * w j * a k

/-- A closed embedding onto the projectivized minimal nilpotent locus,
with the CORRECT polarization and canonical KKS contact hyperplanes.
Smoothness/reducedness makes the complex-point image condition determine
the reduced closed subscheme. The local differential condition below
identifies contact structures, not just underlying varieties.

If w is a local lift of a projective point and v a tangent field, then
v is canonical-contact iff dw(v)=[a,w]+k*w and Killing(w,a)=0. All opens
used here are affine, so the locally surjective orbit-tangent map has
surjective sections. The condition is invariant under w -> unit*w. -/
structure AdjointContactPresentation {n : ℕ} (X : ContactFanoManifold n) where
  algebra : SimpleLieData
  ambientDimension : ℕ
  basis : Module.Basis (Fin (ambientDimension+1)) ℂ algebra.carrier
  coordinates : ProjectiveCoordinates ambientDimension
  embedding : X.variety.scheme ⟶ ComplexProjectiveSpace ambientDimension
  closed : IsClosedImmersion embedding
  overC : embedding ≫ projectiveBaseMap ambientDimension = X.variety.structureMap
  polarization : pullbackModule embedding coordinates.hyperplane.sheaf ≅
    X.contact.sequence.line.sheaf
  image : ∀ z : PointsOver ComplexBase (𝟙 ComplexBase)
      (ComplexProjectiveSpace ambientDimension) (projectiveBaseMap ambientDimension),
    (∃ x : ComplexPoint X.variety, x.map ≫ embedding = z.val) ↔
      ∃ e : algebra.carrier, IsMinimalNilpotent algebra e ∧
        coordinates.Represents z (fun i => basis.repr e i)
  canonicalContact : ∀ (F : AffineLineFrame X.contact.sequence.line)
      (v : SectionsOn (tangentSheaf X.variety.structureMap) F.openSet),
    let w := fun i => F.localCoefficient
      (pullSection embedding (coordinates.coordinate i) ≫ polarization.hom)
    localContactValue X.contact F v = 0 ↔
      ∃ (a : Fin (ambientDimension+1) → RingSections X.variety.scheme F.openSet)
        (k : RingSections X.variety.scheme F.openSet),
        (∀ i, tangentActs X.variety.structureMap F.openSet v (w i) =
          bracketCoordinates algebra basis X.variety.structureMap F.openSet a w i + k * w i) ∧
        killingCoordinates algebra basis X.variety.structureMap F.openSet w a = 0

namespace AdjointComparisonProof

/-- Equivalent Lie algebras have the same actual ambient projective dimension. -/
theorem ambientDimension_eq {n : ℕ} {X Y : ContactFanoManifold n}
    (A : AdjointContactPresentation X) (B : AdjointContactPresentation Y)
    (e : A.algebra.carrier ≃ₗ⁅ℂ⁆ B.algebra.carrier) :
    A.ambientDimension = B.ambientDimension := by
  have h := e.toLinearEquiv.finrank_eq
  rw [Module.finrank_eq_card_basis A.basis, Module.finrank_eq_card_basis B.basis] at h
  simpa only [Fintype.card_fin, Nat.add_right_cancel_iff] using h

/-- The genuine change of homogeneous coordinates determined by the two
bases and the supplied Lie equivalence. -/
def coordinateEquiv {n : ℕ} {X Y : ContactFanoManifold n}
    (A : AdjointContactPresentation X) (B : AdjointContactPresentation Y)
    (e : A.algebra.carrier ≃ₗ⁅ℂ⁆ B.algebra.carrier) :
    (Fin (A.ambientDimension+1) → ℂ) ≃ₗ[ℂ]
      (Fin (B.ambientDimension+1) → ℂ) :=
  (A.basis.equivFun.symm.trans e.toLinearEquiv).trans B.basis.equivFun

theorem coordinateEquiv_repr {n : ℕ} {X Y : ContactFanoManifold n}
    (A : AdjointContactPresentation X) (B : AdjointContactPresentation Y)
    (e : A.algebra.carrier ≃ₗ⁅ℂ⁆ B.algebra.carrier) (v : A.algebra.carrier) :
    coordinateEquiv A B e (fun i => A.basis.repr v i) =
      fun j => B.basis.repr (e v) j := by
  change B.basis.equivFun (e (A.basis.equivFun.symm (A.basis.equivFun v))) =
    B.basis.equivFun (e v)
  rw [A.basis.equivFun.symm_apply_apply]

/-- Each coordinate is the stated constant matrix combination. -/
theorem coordinateEquiv_apply {n : ℕ} {X Y : ContactFanoManifold n}
    (A : AdjointContactPresentation X) (B : AdjointContactPresentation Y)
    (e : A.algebra.carrier ≃ₗ⁅ℂ⁆ B.algebra.carrier)
    (v : Fin (A.ambientDimension+1) → ℂ) (j : Fin (B.ambientDimension+1)) :
    coordinateEquiv A B e v j =
      ∑ i, B.basis.repr (e (A.basis i)) j * v i := by
  let T : A.algebra.carrier →ₗ[ℂ] ℂ :=
    (LinearMap.proj j).comp (B.basis.equivFun.toLinearMap.comp e.toLinearEquiv.toLinearMap)
  change T (A.basis.equivFun.symm v) = ∑ i, T (A.basis i) * v i
  rw [Module.Basis.equivFun_symm_apply, map_sum]
  simp only [map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- A closed point in one closed image is in the other whenever the
actual complex-valued morphisms have this image inclusion. -/
theorem closedPoint_range_mono {Y Z W : Scheme}
    (s : W ⟶ ComplexBase) [LocallyOfFiniteType s]
    (f : Y ⟶ W) (g : Z ⟶ W) [IsClosedImmersion f] [IsClosedImmersion g]
    (hpoints : ∀ p : ComplexBase ⟶ W, p ≫ s = 𝟙 ComplexBase →
      (∃ a : ComplexBase ⟶ Y, a ≫ f = p) →
        ∃ b : ComplexBase ⟶ Z, b ≫ g = p)
    {w : W} (hw : IsClosed {w}) (hf : w ∈ Set.range f) : w ∈ Set.range g := by
  obtain ⟨v, rfl⟩ := hf
  have hpre : f ⁻¹' ({f v} : Set W) = ({v} : Set Y) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact f.isClosedEmbedding.injective.eq_iff
  have hv : IsClosed ({v} : Set Y) := by
    rw [← hpre]
    exact hw.preimage f.continuous
  let p := pointOfClosedPoint (f ≫ s) v hv
  have hp : (p ≫ f) ≫ s = 𝟙 ComplexBase := by
    simpa only [p, Category.assoc] using pointOfClosedPoint_comp (f ≫ s) v hv
  obtain ⟨q, hq⟩ := hpoints (p ≫ f) hp ⟨p, rfl⟩
  refine ⟨q (IsLocalRing.closedPoint ℂ), ?_⟩
  have he := congrArg (fun r : ComplexBase ⟶ W => r (IsLocalRing.closedPoint ℂ)) hq
  exact (Scheme.Hom.comp_apply q g _).symm.trans
    (he.trans ((Scheme.Hom.comp_apply p f _).trans
      (congrArg f (pointOfClosedPoint_apply (f ≫ s) v hv _))))

/-- Equality of actual complex-point images determines the full closed
subsets, by the existing Jacobson theorem over the algebraically closed base. -/
theorem range_eq_of_complexPoint_images {Y Z W : Scheme}
    (s : W ⟶ ComplexBase) [LocallyOfFiniteType s]
    (f : Y ⟶ W) (g : Z ⟶ W) [IsClosedImmersion f] [IsClosedImmersion g]
    (hpoints : ∀ p : ComplexBase ⟶ W, p ≫ s = 𝟙 ComplexBase →
      ((∃ a : ComplexBase ⟶ Y, a ≫ f = p) ↔
        ∃ b : ComplexBase ⟶ Z, b ≫ g = p)) : Set.range f = Set.range g := by
  letI : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace s
  have hc : Set.range f ∩ closedPoints W =
      Set.range g ∩ closedPoints W := by
    ext w
    constructor
    · rintro ⟨hwf, hw⟩
      exact ⟨closedPoint_range_mono s f g
        (fun p hp => (hpoints p hp).mp) hw hwf, hw⟩
    · rintro ⟨hwg, hw⟩
      exact ⟨closedPoint_range_mono s g f
        (fun p hp => (hpoints p hp).mpr) hw hwg, hw⟩
  calc
    Set.range f = closure (Set.range f ∩ closedPoints W) :=
      (closure_inter_closedPoints f.isClosedEmbedding.isClosed_range).symm
    _ = closure (Set.range g ∩ closedPoints W) := congrArg closure hc
    _ = Set.range g := closure_inter_closedPoints g.isClosedEmbedding.isClosed_range

/-- Reducedness of the source makes the actual kernel ideal sheaf radical. -/
theorem kernel_radical {Y Z : Scheme} (f : Y ⟶ Z) [QuasiCompact f]
    [AlgebraicGeometry.IsReduced Y] : f.ker.radical = f.ker := by
  apply Scheme.IdealSheafData.ext
  funext U
  simp only [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply,
    RingHom.ker_eq_comap_bot, ← Ideal.comap_radical, Ideal.radical_bot_of_isReduced]

/-- Equal closed images of reduced schemes give equal actual ideal sheaves. -/
theorem kernel_eq_of_range_eq {Y Z W : Scheme} (f : Y ⟶ W) (g : Z ⟶ W)
    [QuasiCompact f] [QuasiCompact g]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Z]
    (h : Set.range f = Set.range g) : f.ker = g.ker := by
  have hs : f.ker.support = g.ker.support := by
    apply SetLike.coe_injective
    rw [Scheme.Hom.support_ker, Scheme.Hom.support_ker, h]
  have hi := congrArg (Scheme.IdealSheafData.vanishingIdeal (X := W)) hs
  rw [Scheme.IdealSheafData.vanishingIdeal_support,
    Scheme.IdealSheafData.vanishingIdeal_support, kernel_radical f, kernel_radical g] at hi
  exact hi

/-- The isomorphism is constructed by the universal property of the
closed immersions, and its equation over the ambient scheme is retained. -/
theorem closedIso_of_complexPoint_images {Y Z W : Scheme}
    (s : W ⟶ ComplexBase) [LocallyOfFiniteType s]
    (f : Y ⟶ W) (g : Z ⟶ W) [IsClosedImmersion f] [IsClosedImmersion g]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Z]
    (hpoints : ∀ p : ComplexBase ⟶ W, p ≫ s = 𝟙 ComplexBase →
      ((∃ a : ComplexBase ⟶ Y, a ≫ f = p) ↔
        ∃ b : ComplexBase ⟶ Z, b ≫ g = p)) :
    ∃ e : Y ≅ Z, e.hom ≫ g = f := by
  have hk : g.ker = f.ker := kernel_eq_of_range_eq g f
    (range_eq_of_complexPoint_images s f g hpoints).symm
  let q := IsClosedImmersion.lift g f hk.le
  letI : IsIso q := IsClosedImmersion.isIso_lift g f hk
  exact ⟨asIso q, IsClosedImmersion.lift_fac g f hk.le⟩

/-- The supplied projective coefficient map is of finite type, by the
actual homogeneous polynomial algebra over its degree-zero part. -/
theorem projectiveBase_locallyOfFiniteType (N : ℕ) :
    LocallyOfFiniteType (projectiveBaseMap N) := by
  let grading := MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ
  let A := MvPolynomial (Fin (N+1)) ℂ
  letI : IsScalarTower ℂ (grading 0) A :=
    IsScalarTower.of_algebraMap_eq (R := ℂ) (S := ↥(grading 0)) (A := A) (fun _ => rfl)
  letI : Algebra.FiniteType (grading 0) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ (grading 0) A
  change LocallyOfFiniteType (Proj.toSpecZero grading ≫ (zeroDegreeSchemeIso N).hom)
  infer_instance

/-- The two actual closed embeddings have the same complex-point
image after the genuine linear projective coordinate change. -/
theorem embeddingImage_transport {n : ℕ} {X Y : ContactFanoManifold n}
    (A : AdjointContactPresentation X) (B : AdjointContactPresentation Y)
    (e : A.algebra.carrier ≃ₗ⁅ℂ⁆ B.algebra.carrier)
    (j : ComplexProjectiveSpace A.ambientDimension ≅
      ComplexProjectiveSpace B.ambientDimension)
    (hj : j.hom ≫ projectiveBaseMap B.ambientDimension =
      projectiveBaseMap A.ambientDimension)
    (l : pullbackModule j.hom B.coordinates.hyperplane.sheaf ≅
      A.coordinates.hyperplane.sheaf)
    (hl : ∀ k, pullSection j.hom (B.coordinates.coordinate k) ≫ l.hom =
      transformSections (projectiveBaseMap A.ambientDimension)
        (coordinateEquiv A B e).toLinearMap A.coordinates.coordinate k)
    (p : ComplexBase ⟶ ComplexProjectiveSpace B.ambientDimension)
    (hp : p ≫ projectiveBaseMap B.ambientDimension = 𝟙 ComplexBase) :
    (∃ a : ComplexBase ⟶ X.variety.scheme, a ≫ (A.embedding ≫ j.hom) = p) ↔
      ∃ b : ComplexBase ⟶ Y.variety.scheme, b ≫ B.embedding = p := by
  constructor
  · rintro ⟨a, ha⟩
    have haC : a ≫ X.variety.structureMap = 𝟙 ComplexBase := by
      calc
        _ = a ≫ (A.embedding ≫ (j.hom ≫ projectiveBaseMap B.ambientDimension)) := by
          rw [hj, A.overC]
        _ = (a ≫ (A.embedding ≫ j.hom)) ≫ projectiveBaseMap B.ambientDimension := by
          simp only [Category.assoc]
        _ = p ≫ projectiveBaseMap B.ambientDimension :=
          congrArg (fun f => f ≫ projectiveBaseMap B.ambientDimension) ha
        _ = 𝟙 ComplexBase := hp
    let x : ComplexPoint X.variety := ⟨a, haC⟩
    let z : PointsOver ComplexBase (𝟙 ComplexBase)
        (ComplexProjectiveSpace A.ambientDimension) (projectiveBaseMap A.ambientDimension) :=
      ⟨a ≫ A.embedding, by rw [Category.assoc, A.overC, haC]⟩
    obtain ⟨v, hv, hz⟩ := (A.image z).mp ⟨x, rfl⟩
    have ht := represents_transport A.coordinates B.coordinates (coordinateEquiv A B e)
      j.hom hj l hl z (fun i => A.basis.repr v i) hz
    have heq : (⟨z.val ≫ j.hom, by rw [Category.assoc, hj, z.property]⟩ :
        PointsOver ComplexBase (𝟙 ComplexBase) (ComplexProjectiveSpace B.ambientDimension)
          (projectiveBaseMap B.ambientDimension)) = ⟨p, hp⟩ := by
      apply Subtype.ext
      simpa only [z, Category.assoc] using ha
    rw [heq, coordinateEquiv_repr] at ht
    obtain ⟨y, hy⟩ := (B.image ⟨p, hp⟩).mpr
      ⟨e v, (minimalNilpotent_equiv e v).mpr hv, ht⟩
    exact ⟨y.map, hy⟩
  · rintro ⟨b, hb⟩
    have hbC : b ≫ Y.variety.structureMap = 𝟙 ComplexBase := by
      rw [← B.overC, ← Category.assoc, hb, hp]
    let y : ComplexPoint Y.variety := ⟨b, hbC⟩
    obtain ⟨w, hw, hpw⟩ := (B.image ⟨p, hp⟩).mp ⟨y, hb⟩
    let v := e.symm w
    have hv : IsMinimalNilpotent A.algebra v := (minimalNilpotent_equiv e.symm w).mpr hw
    have hvc : (fun i => A.basis.repr v i) ≠ 0 := by
      intro h
      apply hv.1
      apply A.basis.equivFun.injective
      simpa only [map_zero, Module.Basis.equivFun_apply] using h
    obtain ⟨z, hz, huniq⟩ := projectiveCoordinates_pointOfVector A.coordinates
      (fun i => A.basis.repr v i) hvc
    have ht := represents_transport A.coordinates B.coordinates (coordinateEquiv A B e)
      j.hom hj l hl z (fun i => A.basis.repr v i) hz
    rw [coordinateEquiv_repr] at ht
    have hev : e v = w := e.apply_symm_apply w
    rw [hev] at ht
    have heq : (⟨z.val ≫ j.hom, by rw [Category.assoc, hj, z.property]⟩ :
        PointsOver ComplexBase (𝟙 ComplexBase) (ComplexProjectiveSpace B.ambientDimension)
          (projectiveBaseMap B.ambientDimension)) = ⟨p, hp⟩ := by
      apply (projectiveCoordinates_samePoint_iff B.coordinates _ _ _ _ ht hpw).mpr
      exact ⟨1, one_ne_zero, (one_smul ℂ (fun i => B.basis.repr w i)).symm⟩
    obtain ⟨x, hx⟩ := (A.image z).mpr ⟨v, hv, hz⟩
    refine ⟨x.map, ?_⟩
    rw [← Category.assoc, hx]
    exact congrArg Subtype.val heq

/-- The comparison of adjoint images is an actual scheme isomorphism
over C. The ambient coordinate and line comparisons are retained for
the subsequent canonical-contact calculation. -/
theorem adjointSchemeIso {n : ℕ} {X Y : ContactFanoManifold n}
    (A : AdjointContactPresentation X) (B : AdjointContactPresentation Y)
    (e : A.algebra.carrier ≃ₗ⁅ℂ⁆ B.algebra.carrier) :
    ∃ (j : ComplexProjectiveSpace A.ambientDimension ≅
          ComplexProjectiveSpace B.ambientDimension)
      (l : pullbackModule j.hom B.coordinates.hyperplane.sheaf ≅
          A.coordinates.hyperplane.sheaf)
      (f : X.variety.scheme ≅ Y.variety.scheme),
      j.hom ≫ projectiveBaseMap B.ambientDimension = projectiveBaseMap A.ambientDimension ∧
      (∀ k, pullSection j.hom (B.coordinates.coordinate k) ≫ l.hom =
        transformSections (projectiveBaseMap A.ambientDimension)
          (coordinateEquiv A B e).toLinearMap A.coordinates.coordinate k) ∧
      f.hom ≫ B.embedding = A.embedding ≫ j.hom ∧
      f.hom ≫ Y.variety.structureMap = X.variety.structureMap := by
  obtain ⟨j, hj, l, hl⟩ := projectiveIso_of_linearEquiv A.coordinates B.coordinates
    (coordinateEquiv A B e)
  letI : IsClosedImmersion A.embedding := A.closed
  letI : IsClosedImmersion B.embedding := B.closed
  letI : LocallyOfFiniteType (projectiveBaseMap B.ambientDimension) :=
    projectiveBase_locallyOfFiniteType B.ambientDimension
  letI : AlgebraicGeometry.IsReduced X.variety.scheme :=
    LeBrunSalamon.SchemeStandardInputs.smooth_complex_reduced X.variety.structureMap
  letI : AlgebraicGeometry.IsReduced Y.variety.scheme :=
    LeBrunSalamon.SchemeStandardInputs.smooth_complex_reduced Y.variety.structureMap
  obtain ⟨f, hf⟩ := closedIso_of_complexPoint_images
    (projectiveBaseMap B.ambientDimension) (A.embedding ≫ j.hom) B.embedding
    (embeddingImage_transport A B e j hj l hl)
  refine ⟨j, l, f, hj, hl, hf, ?_⟩
  rw [← B.overC, ← Category.assoc, hf, Category.assoc, hj, A.overC]

section AdjointPolarizationLocal

set_option backward.isDefEq.respectTransparency false

def coordinateSection {n : ℕ} {X : ContactFanoManifold n}
    (A : AdjointContactPresentation X) (i : Fin (A.ambientDimension+1)) :
    AlgebraicSection X.contact.sequence.line.sheaf :=
  pullSection A.embedding (A.coordinates.coordinate i) ≫ A.polarization.hom

def squareLineComparison {n : ℕ} {X Y : ContactFanoManifold n}
    (A : AdjointContactPresentation X) (B : AdjointContactPresentation Y)
    (j : ComplexProjectiveSpace A.ambientDimension ≅
      ComplexProjectiveSpace B.ambientDimension)
    (f : X.variety.scheme ≅ Y.variety.scheme)
    (hf : f.hom ≫ B.embedding = A.embedding ≫ j.hom) :
    pullbackModule f.hom (pullbackModule B.embedding B.coordinates.hyperplane.sheaf) ≅
      pullbackModule A.embedding (pullbackModule j.hom B.coordinates.hyperplane.sheaf) :=
  (Scheme.Modules.pullbackComp f.hom B.embedding).app B.coordinates.hyperplane.sheaf ≪≫
    (Scheme.Modules.pullbackCongr hf).app B.coordinates.hyperplane.sheaf ≪≫
      ((Scheme.Modules.pullbackComp A.embedding j.hom).app B.coordinates.hyperplane.sheaf).symm

theorem squareLineComparison_section {n : ℕ} {X Y : ContactFanoManifold n}
    (A : AdjointContactPresentation X) (B : AdjointContactPresentation Y)
    (j : ComplexProjectiveSpace A.ambientDimension ≅
      ComplexProjectiveSpace B.ambientDimension)
    (f : X.variety.scheme ≅ Y.variety.scheme)
    (hf : f.hom ≫ B.embedding = A.embedding ≫ j.hom)
    (a : AlgebraicSection B.coordinates.hyperplane.sheaf) :
    pullSection f.hom (pullSection B.embedding a) ≫
        (squareLineComparison A B j f hf).hom =
      pullSection A.embedding (pullSection j.hom a) := by
  let p := (Scheme.Modules.pullbackComp A.embedding j.hom).app B.coordinates.hyperplane.sheaf
  apply (cancel_mono p.hom).1
  calc
    _ = pullSection f.hom (pullSection B.embedding a) ≫
        (Scheme.Modules.pullbackComp f.hom B.embedding).hom.app B.coordinates.hyperplane.sheaf ≫
        (Scheme.Modules.pullbackCongr hf).hom.app B.coordinates.hyperplane.sheaf := by
      simp only [squareLineComparison, Iso.trans_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom,
        Category.assoc, p, Iso.inv_hom_id_app, Category.comp_id]
    _ = pullSection (f.hom ≫ B.embedding) a ≫
        (Scheme.Modules.pullbackCongr hf).hom.app B.coordinates.hyperplane.sheaf := by
      rw [← Category.assoc, LeBrunSalamon.Refinement.CanonicalPullbackSectionProof.pullSection_comp]
    _ = pullSection (A.embedding ≫ j.hom) a :=
      ExternalExchangeCoherenceProof.pullSection_congr hf a
    _ = pullSection A.embedding (pullSection j.hom a) ≫ p.hom :=
      (LeBrunSalamon.Refinement.CanonicalPullbackSectionProof.pullSection_comp A.embedding j.hom a).symm

/-- The two original contact quotient lines are compared through the
actual polarizations, the ambient linear map and the commutative square. -/
def polarizationComparison {n : ℕ} {X Y : ContactFanoManifold n}
    (A : AdjointContactPresentation X) (B : AdjointContactPresentation Y)
    (j : ComplexProjectiveSpace A.ambientDimension ≅
      ComplexProjectiveSpace B.ambientDimension)
    (l : pullbackModule j.hom B.coordinates.hyperplane.sheaf ≅
      A.coordinates.hyperplane.sheaf)
    (f : X.variety.scheme ≅ Y.variety.scheme)
    (hf : f.hom ≫ B.embedding = A.embedding ≫ j.hom) :
    pullbackModule f.hom Y.contact.sequence.line.sheaf ≅ X.contact.sequence.line.sheaf :=
  (Scheme.Modules.pullback f.hom).mapIso B.polarization.symm ≪≫
    squareLineComparison A B j f hf ≪≫
      (Scheme.Modules.pullback A.embedding).mapIso l ≪≫ A.polarization

theorem polarizationComparison_coordinate {n : ℕ} {X Y : ContactFanoManifold n}
    (A : AdjointContactPresentation X) (B : AdjointContactPresentation Y)
    (e : A.algebra.carrier ≃ₗ⁅ℂ⁆ B.algebra.carrier)
    (j : ComplexProjectiveSpace A.ambientDimension ≅
      ComplexProjectiveSpace B.ambientDimension)
    (l : pullbackModule j.hom B.coordinates.hyperplane.sheaf ≅
      A.coordinates.hyperplane.sheaf)
    (hl : ∀ k, pullSection j.hom (B.coordinates.coordinate k) ≫ l.hom =
      transformSections (projectiveBaseMap A.ambientDimension)
        (coordinateEquiv A B e).toLinearMap A.coordinates.coordinate k)
    (f : X.variety.scheme ≅ Y.variety.scheme)
    (hf : f.hom ≫ B.embedding = A.embedding ≫ j.hom)
    (k : Fin (B.ambientDimension+1)) :
    pullSection f.hom (coordinateSection B k) ≫
        (polarizationComparison A B j l f hf).hom =
      transformSections X.variety.structureMap (coordinateEquiv A B e).toLinearMap
        (coordinateSection A) k := by
  let pb := (Scheme.Modules.pullback f.hom).mapIso B.polarization
  calc
    _ = pullSection f.hom (pullSection B.embedding (B.coordinates.coordinate k)) ≫
        (squareLineComparison A B j f hf).hom ≫
          (Scheme.Modules.pullback A.embedding).map l.hom ≫ A.polarization.hom := by
      rw [coordinateSection, ExternalExchangeCoherenceProof.pullSection_map]
      change (_ ≫ pb.hom) ≫
        (pb.inv ≫ (squareLineComparison A B j f hf).hom ≫
          (Scheme.Modules.pullback A.embedding).map l.hom ≫ A.polarization.hom) = _
      simp only [Category.assoc, pb.hom_inv_id_assoc]
    _ = pullSection A.embedding (pullSection j.hom (B.coordinates.coordinate k)) ≫
        (Scheme.Modules.pullback A.embedding).map l.hom ≫ A.polarization.hom := by
      rw [← Category.assoc, ← Category.assoc, squareLineComparison_section,
        Category.assoc]
    _ = pullSection A.embedding
        (pullSection j.hom (B.coordinates.coordinate k) ≫ l.hom) ≫ A.polarization.hom := by
      rw [ExternalExchangeCoherenceProof.pullSection_map, Category.assoc]
    _ = pullSection A.embedding
        (transformSections (projectiveBaseMap A.ambientDimension)
          (coordinateEquiv A B e).toLinearMap A.coordinates.coordinate k) ≫
        A.polarization.hom := by rw [hl k]
    _ = transformSections X.variety.structureMap (coordinateEquiv A B e).toLinearMap
        (fun i => pullSection A.embedding (A.coordinates.coordinate i)) k ≫ A.polarization.hom := by
      rw [transformSections_pull A.embedding X.variety.structureMap
        (projectiveBaseMap A.ambientDimension) A.overC]
    _ = _ := transformSections_post _ _ _ _ _

end AdjointPolarizationLocal

end AdjointComparisonProof

section AdjointScalarExtension

set_option backward.isDefEq.respectTransparency false

namespace AdjointComparisonProof

open scoped TensorProduct

def scalarBasisCoordinates {G : SimpleLieData} {N : ℕ}
    (b : Module.Basis (Fin (N+1)) ℂ G.carrier)
    (R : Type*) [CommRing R] [Algebra ℂ R] :
    (Fin (N+1) → R) ≃ₗ[R] (R ⊗[ℂ] G.carrier) :=
  (b.baseChange R).equivFun.symm

theorem scalarBasisCoordinates_apply {G : SimpleLieData} {N : ℕ}
    (b : Module.Basis (Fin (N+1)) ℂ G.carrier)
    (R : Type*) [CommRing R] [Algebra ℂ R] (a : Fin (N+1) → R) :
    scalarBasisCoordinates b R a = ∑ i, a i ⊗ₜ[ℂ] b i := by
  rw [scalarBasisCoordinates, Module.Basis.equivFun_symm_apply]
  simp only [Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem scalarBasisCoordinates_tmul {G : SimpleLieData} {N : ℕ}
    (b : Module.Basis (Fin (N+1)) ℂ G.carrier)
    (R : Type*) [CommRing R] [Algebra ℂ R] (a : R) (v : G.carrier) (i : Fin (N+1)) :
    (scalarBasisCoordinates b R).symm (a ⊗ₜ[ℂ] v) i =
      algebraMap ℂ R (b.repr v i) * a := by
  change (b.baseChange R).repr (a ⊗ₜ[ℂ] v) i = _
  rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def]

def scalarBracketCoordinates (G : SimpleLieData) {N : ℕ}
    (b : Module.Basis (Fin (N+1)) ℂ G.carrier)
    (R : Type*) [CommRing R] [Algebra ℂ R]
    (a w : Fin (N+1) → R) : Fin (N+1) → R :=
  fun i => ∑ j, ∑ k, algebraMap ℂ R (b.repr ⁅b j, b k⁆ i) * a j * w k

def scalarKillingCoordinates (G : SimpleLieData) {N : ℕ}
    (b : Module.Basis (Fin (N+1)) ℂ G.carrier)
    (R : Type*) [CommRing R] [Algebra ℂ R]
    (w a : Fin (N+1) → R) : R :=
  ∑ j, ∑ k, algebraMap ℂ R (killingValue G (b j) (b k)) * w j * a k

theorem scalarBasisCoordinates_bracket {G : SimpleLieData} {N : ℕ}
    (b : Module.Basis (Fin (N+1)) ℂ G.carrier)
    (R : Type*) [CommRing R] [Algebra ℂ R] (a w : Fin (N+1) → R) :
    scalarBasisCoordinates b R (scalarBracketCoordinates G b R a w) =
      ⁅scalarBasisCoordinates b R a, scalarBasisCoordinates b R w⁆ := by
  apply (scalarBasisCoordinates b R).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  funext i
  rw [scalarBasisCoordinates_apply, scalarBasisCoordinates_apply, sum_lie_sum]
  simp only [LieAlgebra.ExtendScalars.bracket_tmul,
    map_sum, Finset.sum_apply, scalarBasisCoordinates_tmul, scalarBracketCoordinates]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem scalarBasisCoordinates_killing {G : SimpleLieData} {N : ℕ}
    (b : Module.Basis (Fin (N+1)) ℂ G.carrier)
    (R : Type*) [CommRing R] [Algebra ℂ R] (w a : Fin (N+1) → R) :
    scalarKillingCoordinates G b R w a =
      (_root_.killingForm ℂ G.carrier).baseChange R
        (scalarBasisCoordinates b R w) (scalarBasisCoordinates b R a) := by
  rw [scalarBasisCoordinates_apply, scalarBasisCoordinates_apply,
    map_sum ((_root_.killingForm ℂ G.carrier).baseChange R), LinearMap.sum_apply]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.BilinForm.baseChange_tmul,
    Algebra.smul_def, _root_.killingForm_apply_apply,
    scalarKillingCoordinates, killingValue]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

def scalarLieMap {G H : SimpleLieData} (e : G.carrier ≃ₗ⁅ℂ⁆ H.carrier)
    (R : Type*) [CommRing R] [Algebra ℂ R] :
    (R ⊗[ℂ] G.carrier) →ₗ⁅ℂ⁆ (R ⊗[ℂ] H.carrier) :=
  LieAlgebra.ExtendScalars.map (AlgHom.id ℂ R) e.toLieHom

theorem scalarLieMap_tmul {G H : SimpleLieData} (e : G.carrier ≃ₗ⁅ℂ⁆ H.carrier)
    (R : Type*) [CommRing R] [Algebra ℂ R] (a : R) (v : G.carrier) :
    scalarLieMap e R (a ⊗ₜ[ℂ] v) = a ⊗ₜ[ℂ] e v := rfl

/-- Killing invariance survives arbitrary commutative scalar extension.
This is a bilinear tensor calculation, using the actual trace pairing. -/
theorem scalarLieMap_killing {G H : SimpleLieData} (e : G.carrier ≃ₗ⁅ℂ⁆ H.carrier)
    (R : Type*) [CommRing R] [Algebra ℂ R]
    (u v : R ⊗[ℂ] G.carrier) :
    (_root_.killingForm ℂ H.carrier).baseChange R
        (scalarLieMap e R u) (scalarLieMap e R v) =
      (_root_.killingForm ℂ G.carrier).baseChange R u v := by
  induction u using TensorProduct.inductionOn with
  | tmul a u =>
      induction v using TensorProduct.inductionOn with
      | tmul b v =>
          simp only [scalarLieMap_tmul, LinearMap.BilinForm.baseChange_tmul,
            LieAlgebra.killingForm_of_equiv_apply]
      | add v w hv hw =>
          simp only [map_add, hv, hw]
  | add u v hu hv =>
      simp only [map_add, LinearMap.add_apply, hu, hv]

theorem coordinateEquiv_standard {n : ℕ} {X Y : ContactFanoManifold n}
    (A : AdjointContactPresentation X) (B : AdjointContactPresentation Y)
    (e : A.algebra.carrier ≃ₗ⁅ℂ⁆ B.algebra.carrier)
    (i : Fin (A.ambientDimension+1)) (j : Fin (B.ambientDimension+1)) :
    coordinateEquiv A B e (Pi.single i 1) j = B.basis.repr (e (A.basis i)) j := by
  rw [coordinateEquiv_apply]
  simp [Pi.single_apply]

theorem scalarLieMap_coordinates {n : ℕ} {X Y : ContactFanoManifold n}
    (A : AdjointContactPresentation X) (B : AdjointContactPresentation Y)
    (e : A.algebra.carrier ≃ₗ⁅ℂ⁆ B.algebra.carrier)
    (R : Type*) [CommRing R] [Algebra ℂ R]
    (a : Fin (A.ambientDimension+1) → R) :
    scalarLieMap e R (scalarBasisCoordinates A.basis R a) =
      scalarBasisCoordinates B.basis R
        (transformValues (coordinateEquiv A B e).toLinearMap a) := by
  apply (scalarBasisCoordinates B.basis R).symm.injective
  rw [LinearEquiv.symm_apply_apply, scalarBasisCoordinates_apply, map_sum, map_sum]
  funext j
  simp only [Finset.sum_apply, scalarLieMap_tmul, scalarBasisCoordinates_tmul,
    transformValues, LinearEquiv.coe_coe, coordinateEquiv_standard, Algebra.smul_def]

theorem scalarBracketCoordinates_equiv {n : ℕ} {X Y : ContactFanoManifold n}
    (A : AdjointContactPresentation X) (B : AdjointContactPresentation Y)
    (e : A.algebra.carrier ≃ₗ⁅ℂ⁆ B.algebra.carrier)
    (R : Type*) [CommRing R] [Algebra ℂ R]
    (a w : Fin (A.ambientDimension+1) → R) :
    scalarBracketCoordinates B.algebra B.basis R
        (transformValues (coordinateEquiv A B e).toLinearMap a)
        (transformValues (coordinateEquiv A B e).toLinearMap w) =
      transformValues (coordinateEquiv A B e).toLinearMap
        (scalarBracketCoordinates A.algebra A.basis R a w) := by
  apply (scalarBasisCoordinates B.basis R).injective
  rw [scalarBasisCoordinates_bracket, ← scalarLieMap_coordinates,
    ← scalarLieMap_coordinates, ← (scalarLieMap e R).map_lie,
    ← scalarBasisCoordinates_bracket, scalarLieMap_coordinates]

theorem scalarKillingCoordinates_equiv {n : ℕ} {X Y : ContactFanoManifold n}
    (A : AdjointContactPresentation X) (B : AdjointContactPresentation Y)
    (e : A.algebra.carrier ≃ₗ⁅ℂ⁆ B.algebra.carrier)
    (R : Type*) [CommRing R] [Algebra ℂ R]
    (w a : Fin (A.ambientDimension+1) → R) :
    scalarKillingCoordinates B.algebra B.basis R
        (transformValues (coordinateEquiv A B e).toLinearMap w)
        (transformValues (coordinateEquiv A B e).toLinearMap a) =
      scalarKillingCoordinates A.algebra A.basis R w a := by
  rw [scalarBasisCoordinates_killing, scalarBasisCoordinates_killing,
    ← scalarLieMap_coordinates, ← scalarLieMap_coordinates, scalarLieMap_killing]

theorem transformValues_inverse {ι κ V : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [AddCommGroup V] [Module ℂ V]
    (T : (ι → ℂ) ≃ₗ[ℂ] (κ → ℂ)) (a : ι → V) :
    transformValues T.symm.toLinearMap (transformValues T.toLinearMap a) = a := by
  rw [transformValues_comp]
  have h : T.symm.toLinearMap.comp T.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro v
    change T.symm (T v) = v
    exact T.symm_apply_apply v
  rw [h, transformValues_id]

theorem transformValues_add {ι κ V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V]
    (T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) (a b : ι → V) :
    transformValues T (a + b) = transformValues T a + transformValues T b := by
  funext j
  simp only [transformValues, Pi.add_apply, smul_add, Finset.sum_add_distrib]

theorem transformValues_mul {ι κ R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] [Algebra ℂ R]
    (T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) (k : R) (a : ι → R) (j : κ) :
    transformValues T (fun i => k * a i) j = k * transformValues T a j := by
  simp only [transformValues, Algebra.smul_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem coordinateEquiv_symm {n : ℕ} {X Y : ContactFanoManifold n}
    (A : AdjointContactPresentation X) (B : AdjointContactPresentation Y)
    (e : A.algebra.carrier ≃ₗ⁅ℂ⁆ B.algebra.carrier) :
    coordinateEquiv B A e.symm = (coordinateEquiv A B e).symm := by
  apply LinearEquiv.ext
  intro v
  rfl

/-- The ordinary scalar form of the KKS hyperplane equation. It has
no contact-manifold conclusion and is tested on the actual derivation. -/
def scalarCanonicalCondition (G : SimpleLieData) {N : ℕ}
    (b : Module.Basis (Fin (N+1)) ℂ G.carrier)
    (R : Type*) [CommRing R] [Algebra ℂ R]
    (D : Derivation ℂ R R) (w : Fin (N+1) → R) : Prop :=
  ∃ (a : Fin (N+1) → R) (k : R),
    (∀ i, D (w i) = scalarBracketCoordinates G b R a w i + k * w i) ∧
      scalarKillingCoordinates G b R w a = 0

theorem scalarCanonicalCondition_transport {n : ℕ} {X Y : ContactFanoManifold n}
    (A : AdjointContactPresentation X) (B : AdjointContactPresentation Y)
    (e : A.algebra.carrier ≃ₗ⁅ℂ⁆ B.algebra.carrier)
    (R : Type*) [CommRing R] [Algebra ℂ R] (D : Derivation ℂ R R)
    (w : Fin (A.ambientDimension+1) → R)
    (h : scalarCanonicalCondition A.algebra A.basis R D w) :
    scalarCanonicalCondition B.algebra B.basis R D
      (transformValues (coordinateEquiv A B e).toLinearMap w) := by
  obtain ⟨a, k, ha, hk⟩ := h
  refine ⟨transformValues (coordinateEquiv A B e).toLinearMap a, k, ?_, ?_⟩
  · intro j
    have hmap : D (transformValues (coordinateEquiv A B e).toLinearMap w j) =
        transformValues (coordinateEquiv A B e).toLinearMap (fun i => D (w i)) j := by
      exact transformValues_map (coordinateEquiv A B e).toLinearMap D.toLinearMap w j
    rw [hmap]
    have hd : (fun i => D (w i)) =
        scalarBracketCoordinates A.algebra A.basis R a w + (fun i => k * w i) := by
      funext i
      exact ha i
    rw [hd, transformValues_add]
    change transformValues (coordinateEquiv A B e).toLinearMap
        (scalarBracketCoordinates A.algebra A.basis R a w) j +
      transformValues (coordinateEquiv A B e).toLinearMap (fun i => k * w i) j = _
    rw [transformValues_mul, ← scalarBracketCoordinates_equiv]
  · rw [scalarKillingCoordinates_equiv]
    exact hk

theorem scalarCanonicalCondition_equiv {n : ℕ} {X Y : ContactFanoManifold n}
    (A : AdjointContactPresentation X) (B : AdjointContactPresentation Y)
    (e : A.algebra.carrier ≃ₗ⁅ℂ⁆ B.algebra.carrier)
    (R : Type*) [CommRing R] [Algebra ℂ R] (D : Derivation ℂ R R)
    (w : Fin (A.ambientDimension+1) → R) :
    scalarCanonicalCondition B.algebra B.basis R D
        (transformValues (coordinateEquiv A B e).toLinearMap w) ↔
      scalarCanonicalCondition A.algebra A.basis R D w := by
  constructor
  · intro h
    have h' := scalarCanonicalCondition_transport B A e.symm R D
      (transformValues (coordinateEquiv A B e).toLinearMap w) h
    simpa only [coordinateEquiv_symm, transformValues_inverse] using h'
  · exact scalarCanonicalCondition_transport A B e R D w

theorem scalarBracketCoordinates_map {G : SimpleLieData} {N : ℕ}
    (b : Module.Basis (Fin (N+1)) ℂ G.carrier)
    {R S : Type*} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]
    (q : R →ₐ[ℂ] S) (a w : Fin (N+1) → R) (i : Fin (N+1)) :
    q (scalarBracketCoordinates G b R a w i) =
      scalarBracketCoordinates G b S (fun j => q (a j)) (fun j => q (w j)) i := by
  simp only [scalarBracketCoordinates, map_sum, map_mul, q.commutes]

theorem scalarKillingCoordinates_map {G : SimpleLieData} {N : ℕ}
    (b : Module.Basis (Fin (N+1)) ℂ G.carrier)
    {R S : Type*} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]
    (q : R →ₐ[ℂ] S) (w a : Fin (N+1) → R) :
    q (scalarKillingCoordinates G b R w a) =
      scalarKillingCoordinates G b S (fun j => q (w j)) (fun j => q (a j)) := by
  simp only [scalarKillingCoordinates, map_sum, map_mul, q.commutes]

/-- The scalar canonical equation is transported by an actual algebra
isomorphism that intertwines the actual derivations. -/
theorem scalarCanonicalCondition_ringEquiv {G : SimpleLieData} {N : ℕ}
    (b : Module.Basis (Fin (N+1)) ℂ G.carrier)
    {R S : Type*} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]
    (q : R ≃ₐ[ℂ] S) (D : Derivation ℂ R R) (E : Derivation ℂ S S)
    (hD : ∀ r, E (q r) = q (D r)) (w : Fin (N+1) → R) :
    scalarCanonicalCondition G b S E (fun i => q (w i)) ↔
      scalarCanonicalCondition G b R D w := by
  have hbracket (a z : Fin (N+1) → R) (i : Fin (N+1)) :
      q (scalarBracketCoordinates G b R a z i) =
        scalarBracketCoordinates G b S (fun j => q (a j)) (fun j => q (z j)) i := by
    simpa only [AlgEquiv.toAlgHom_apply] using
      scalarBracketCoordinates_map b q.toAlgHom a z i
  have hkilling (z a : Fin (N+1) → R) :
      q (scalarKillingCoordinates G b R z a) =
        scalarKillingCoordinates G b S (fun j => q (z j)) (fun j => q (a j)) := by
    simpa only [AlgEquiv.toAlgHom_apply] using
      scalarKillingCoordinates_map b q.toAlgHom z a
  constructor
  · rintro ⟨a, k, ha, hk⟩
    refine ⟨fun i => q.symm (a i), q.symm k, ?_, ?_⟩
    · intro i
      apply q.injective
      rw [map_add, map_mul, hbracket, q.apply_symm_apply, ← hD]
      simpa only [q.apply_symm_apply] using ha i
    · apply q.injective
      rw [map_zero, hkilling]
      simpa only [q.apply_symm_apply] using hk
  · rintro ⟨a, k, ha, hk⟩
    refine ⟨fun i => q (a i), q k, ?_, ?_⟩
    · intro i
      rw [hD, ha i, map_add, map_mul, hbracket]
    · rw [← hkilling, hk, map_zero]

end AdjointComparisonProof

end AdjointScalarExtension

/-- SOURCE hom:adjoint. Its proof must produce an actual closed
embedding and verify the KKS contact hyperplanes and polarization. -/
def HomogeneousClassification : Prop :=
  ∀ (n : ℕ) (X : ContactFanoManifold n),
    AlgebraicContactAction X → Nonempty (AdjointContactPresentation X)

def ContactFanoClassification : Prop :=
  ∀ (n : ℕ) (X : ContactFanoManifold n), Nonempty (AdjointContactPresentation X)

/- Exact adjointPresentations_contactIso header relocated to LSHamiltonianJets; see owners/calculus/adjoint_contact_relocation.json. -/

/-! ## F. Supporting homogeneous-geometry proof obligations -/

/-- Elementary group-theoretic step in hom:adjoint. Borel's theorem supplies x0 for the solvable radical;
normality spreads its fixedness to the whole transitive space; effectivity removes the radical. -/
theorem normal_fixedPoint_subgroup_trivial
    (G Z : Type*) [Group G] [MulAction G Z]
    (N : Subgroup G) [N.Normal] (x0 : Z)
    (hfixed : ∀ g : N, (g.val : G) • x0 = x0)
    (htrans : ∀ x y : Z, ∃ g : G, g • x = y)
    (heffective : ∀ g : G, (∀ x : Z, g • x = x) → g = 1) : N = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro g hg
  change g = 1
  apply heffective g
  intro x
  obtain ⟨h, rfl⟩ := htrans x0 x
  have hmem : h⁻¹ * g * h ∈ N :=
    (inferInstance : N.Normal).conj_mem' g hg h
  have hfix := hfixed ⟨h⁻¹ * g * h, hmem⟩
  calc
    g • (h • x0) = h • ((h⁻¹ * g * h) • x0) := by
      simp only [mul_smul, smul_inv_smul]
    _ = h • x0 := congrArg (fun z => h • z) hfix

/-- Euler tangent belongs to every nonzero nilpotent orbit; this is
where Jacobson--Morozov enters the cone/contact comparison. -/
theorem nilpotent_hasEulerLift (G : SimpleLieData) (e : G.carrier)
    (he : e ≠ 0) (hn : IsAdjointNilpotent e) :
    ∃ h : G.carrier, ⁅h, e⁆ = e := by sorry

theorem killing_lineStabilizer_zero (G : SimpleLieData) (e a : G.carrier)
    (he : e ≠ 0) (hn : IsAdjointNilpotent e)
    (ha : ∃ c : ℂ, ⁅a, e⁆ = c • e) : killingValue G e a = 0 := by
  obtain ⟨h, hh⟩ := nilpotent_hasEulerLift G e he hn
  obtain ⟨c, hc⟩ := ha
  change LieModule.traceForm ℂ G.carrier G.carrier e a = 0
  have hhe : LieModule.traceForm ℂ G.carrier G.carrier h e = 0 := by
    calc
      LieModule.traceForm ℂ G.carrier G.carrier h e =
          LieModule.traceForm ℂ G.carrier G.carrier h ⁅h, e⁆ := by rw [hh]
      _ = LieModule.traceForm ℂ G.carrier G.carrier ⁅h, h⁆ e :=
        (LieModule.traceForm_apply_lie_apply ℂ G.carrier G.carrier h h e).symm
      _ = 0 := by simp
  calc
    LieModule.traceForm ℂ G.carrier G.carrier e a =
        LieModule.traceForm ℂ G.carrier G.carrier ⁅h, e⁆ a := by rw [hh]
    _ = LieModule.traceForm ℂ G.carrier G.carrier h ⁅e, a⁆ :=
      LieModule.traceForm_apply_lie_apply ℂ G.carrier G.carrier h e a
    _ = LieModule.traceForm ℂ G.carrier G.carrier h (-(c • e)) := by
      rw [← lie_skew e a, hc]
    _ = 0 := by simp [hhe]


theorem adjointRank_even (G : SimpleLieData) (e : G.carrier) :
    Even (adjointRank G e) := by sorry

theorem minimalNilpotent_rank_positive (G : SimpleLieData) (e : G.carrier)
    (he : IsMinimalNilpotent G e) : 2 ≤ adjointRank G e := by
  obtain ⟨h, hh⟩ := nilpotent_hasEulerLift G e he.1 he.2.1
  have hp : 0 < adjointRank G e := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨-e, h, ?_⟩, ?_⟩
    · change ⁅e, h⁆ = -e
      rw [← lie_skew e h, hh]
    · intro hz
      have hz' : -e = 0 := congrArg Subtype.val hz
      exact he.1 (neg_eq_zero.mp hz')
  obtain ⟨k, hk⟩ := adjointRank_even G e
  omega


/-- The canonical contact condition is independent of multiplying a local lift w by a unit: the extra
derivative is absorbed in k*w. This lemma is ring-theoretic and can be proved before orbit geometry. -/
theorem projectiveTangent_frameChange
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (D : Derivation ℂ A A) (q : Aˣ) (r : ℕ)
    (w z : Fin r → A) (k : A)
    (h : ∀ i, D (w i) = z i + k * w i) :
    ∃ k' : A, ∀ i, D ((q : A) * w i) = (q : A) * z i + k' * ((q : A) * w i) := by
  refine ⟨k + D (q : A) * ((q⁻¹ : Aˣ) : A), ?_⟩
  intro i
  rw [Derivation.leibniz, h i]
  simp only [smul_eq_mul]
  calc
    (q : A) * (z i + k * w i) + w i * D (q : A) =
        (q : A) * z i + k * ((q : A) * w i) +
          D (q : A) * (((q⁻¹ : Aˣ) : A) * (q : A)) * w i := by
      rw [Units.inv_mul]
      ring
    _ = _ := by ring

/-! ## G. Actual Riemannian outputs and the classical twistor reduction -/

universe uR

/-- Bundling retains every structure in the original theorem. It does
not replace a manifold by a cardinality or an abstract space label. -/
structure ClosedRiemannianSpace (n : ℕ) where
  carrier : Type uR
  [metric : EMetricSpace carrier]
  [charts : ChartedSpace (Model n) carrier]
  [smooth : IsManifold (model n) ∞ carrier]
  [riemannian : RiemannianBundle (fun x : carrier => TangentSpace (model n) x)]
  [smoothMetric : IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (fun x : carrier => TangentSpace (model n) x)]
  [intrinsicDistance : IsRiemannianManifold (model n) carrier]
  [compact : CompactSpace carrier]
  [connected : ConnectedSpace carrier]
  [nonempty : Nonempty carrier]

attribute [instance] ClosedRiemannianSpace.metric ClosedRiemannianSpace.charts
  ClosedRiemannianSpace.smooth ClosedRiemannianSpace.riemannian
  ClosedRiemannianSpace.smoothMetric ClosedRiemannianSpace.intrinsicDistance
  ClosedRiemannianSpace.compact ClosedRiemannianSpace.connected ClosedRiemannianSpace.nonempty

structure ClosedPositiveQK (n : ℕ) where
  space : ClosedRiemannianSpace.{uR} n
  dimensionAtLeastEight : 2 ≤ n
  positive : IsPositiveQuaternionicKahler n space.carrier

/-- scale multiplies the METRIC TENSOR, not distance. Distances scale
by sqrt(scale). Smoothness of the inverse is required explicitly. -/
structure SmoothMetricHomothety {n : ℕ} (A B : ClosedRiemannianSpace.{uR} n) where
  equivalence : A.carrier ≃ B.carrier
  smooth : ContMDiff (model n) (model n) ∞ equivalence
  smoothInverse : ContMDiff (model n) (model n) ∞ equivalence.symm
  scale : ℝ
  scale_positive : 0 < scale
  metricEquation : ∀ (x : A.carrier) (u v : TangentSpace (model n) x),
    inner ℝ ((mfderiv (model n) (model n) equivalence x) u)
      ((mfderiv (model n) (model n) equivalence x) v) = scale * inner ℝ u v

/-- An actual global geodesic symmetry, expressed as a smooth isometry
fixing x with differential -id. HEq handles the dependent tangent-space
codomain; the accompanying fixed-point equality determines the transport. -/
structure PointSymmetry {n : ℕ} (A : ClosedRiemannianSpace.{uR} n) (x : A.carrier) where
  isometry : SmoothMetricHomothety.{uR} A A
  unitScale : isometry.scale = 1
  fixed : isometry.equivalence x = x
  involutive : Function.Involutive isometry.equivalence
  derivative : ∀ v : TangentSpace (model n) x,
    HEq ((mfderiv (model n) (model n) isometry.equivalence x) v) (-v)

/-- Intrinsic compact quaternionic symmetric model. Constructing the individual Wolf quotients is a later
implementation, not a label in place of a metric. Parallel curvature is a theorem, not a field. -/
structure SymmetricMetricModel (n : ℕ) where
  space : ClosedRiemannianSpace.{uR} n
  positive : IsPositiveQuaternionicKahler n space.carrier
  symmetries : ∀ x : space.carrier, Nonempty (PointSymmetry.{uR} space x)

structure SymmetricHomothety {n : ℕ} (A : ClosedRiemannianSpace.{uR} n) where
  target : SymmetricMetricModel.{uR} n
  map : SmoothMetricHomothety.{uR} A target.space

theorem globalSymmetries_parallelCurvature {n : ℕ} (S : SymmetricMetricModel.{uR} n) :
    IsLocallyRiemannianSymmetric n S.space.carrier := by sorry

theorem homothety_parallelCurvature {n : ℕ} {A B : ClosedRiemannianSpace.{uR} n}
    (f : SmoothMetricHomothety.{uR} A B)
    (hB : IsLocallyRiemannianSymmetric n B.carrier) :
    IsLocallyRiemannianSymmetric n A.carrier := by sorry

/-- A REDUCTION OUTPUT, not a definition of 'twistor space'.

To construct this certificate from the manuscript one must construct
Salamon's actual complex twistor manifold, algebraize it by Kodaira/GAGA,
identify the adjoint/Wolf model and invoke LeBrun's metric uniqueness.
The field `recover` is a theorem to prove, not an assumption that follows
from a point-set twistor bijection. It does not require the chosen complex
isomorphism to preserve a chosen real structure or fibration.

This formulation deliberately leaves analytic infrastructure as an
explicit classical proof cut, rather than inventing a weak TwistorOf
predicate that would make metric recovery false. -/
structure TwistorReductionOutput {n : ℕ} (M : ClosedPositiveQK.{uR} n) where
  contactFano : ContactFanoManifold n
  recover : AdjointContactPresentation contactFano → Nonempty (SymmetricHomothety.{uR} M.space)

/-- SOURCE twistor.tex, using the cited classical twistor, Wolf and
metric-uniqueness theorems. Does not use the contact-Fano classification. -/
def PositiveTwistorReduction : Prop :=
  ∀ (n : ℕ) (M : ClosedPositiveQK.{uR} n), Nonempty (TwistorReductionOutput.{uR} M)

def SymmetryImpliesParallel : Prop :=
  ∀ (n : ℕ) (S : SymmetricMetricModel.{uR} n),
    IsLocallyRiemannianSymmetric n S.space.carrier

def HomothetyPreservesParallel : Prop :=
  ∀ (n : ℕ) (A B : ClosedRiemannianSpace.{uR} n), SmoothMetricHomothety.{uR} A B →
    IsLocallyRiemannianSymmetric n B.carrier → IsLocallyRiemannianSymmetric n A.carrier

/-! ## H. Dependency-exposing project inputs and final assembly -/

/-- Every substantial arrow in the chosen manuscript proof is an
explicit theorem input. There is NO instance and NO existence theorem
for this package. Supplying it is the project, not a finished proof.

Even an admission-free assembly may still depend on admitted FOUNDATIONAL
definitions, e.g. universal sheaf constructions. Inspect its full axiom
trace, not just the absence of a local `sorry` token. -/
structure AlgebraicInputs (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) : Prop where
  nonprimitive : NonprimitiveBranch
  smoothing : PrimitiveSmoothing P p
  movingPairAndDescent : MovingPairAndDescent P p
  familyToDiagonal : FamilyToDiagonal P p
  symmetricJets : SymmetricJetCriterion
  Hamiltonians : HamiltonianEvaluation
  integration : AlgebraicIntegration
  classification : HomogeneousClassification

/-- Classical geometric bridge, independent of proofs of contact-Fano classification. -/
structure RiemannianInputs : Prop where
  twistor : PositiveTwistorReduction.{uR}
  symmetriesParallel : SymmetryImpliesParallel.{uR}
  homothetyParallel : HomothetyPreservesParallel.{uR}

/-- Eight algebraic inputs plus three Riemannian inputs; no admitted constructor. -/
structure ProjectInputs (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) : Prop where
  algebraic : AlgebraicInputs P p
  riemannian : RiemannianInputs.{uR}

/-- No use of Core.NormalizedContactKernel.separatesFirstJets, the
legacy first-jet target, or the admitted original conjecture occurs here. -/
theorem project_firstJets (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (H : AlgebraicInputs P p) {n : ℕ} (X : ContactFanoManifold n) :
    SeparatesFirstJets X.variety X.contact.sequence.line := by
  classical
  by_cases hp : HasPrimitiveContactPicard X.contact
  · obtain ⟨g⟩ := H.smoothing n X hp
    obtain ⟨D⟩ := H.movingPairAndDescent n X hp g
    obtain ⟨K, _hK⟩ := H.familyToDiagonal n X g D
    exact H.symmetricJets n X.variety X.contact K
  · exact H.nonprimitive n X hp

theorem project_Hamiltonians (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (H : AlgebraicInputs P p) {n : ℕ} (X : ContactFanoManifold n) : HamiltoniansSpan X :=
  H.Hamiltonians n X (project_firstJets P p H X)

theorem project_homogeneous (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (H : AlgebraicInputs P p) {n : ℕ} (X : ContactFanoManifold n) :
    Nonempty (AlgebraicContactAction X) :=
  H.integration n X (project_Hamiltonians P p H X)

/-- Algebraic main theorem, conditional on precisely named manuscript and classical inputs. The conclusion
includes polarization and contact compatibility on an actual closed minimal-nilpotent projective image. -/
theorem project_contactFanoClassification (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (H : AlgebraicInputs P p) : ContactFanoClassification := by
  intro n X
  obtain ⟨A⟩ := project_homogeneous P p H X
  exact H.classification n X A

/-- The stronger metric conclusion before transporting parallel curvature.
The target has actual global point symmetries, not merely a Wolf-family label. -/
theorem project_symmetricHomothety (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (H : ProjectInputs.{uR} P p)
    {n : ℕ} (M : ClosedPositiveQK.{uR} n) :
    Nonempty (SymmetricHomothety.{uR} M.space) := by
  obtain ⟨T⟩ := H.riemannian.twistor n M
  obtain ⟨A⟩ := project_contactFanoClassification P p H.algebraic n T.contactFano
  exact T.recover A

/-- Final curvature deduction from the stronger symmetric-homothety output. -/
theorem project_parallelCurvature (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (H : ProjectInputs.{uR} P p)
    {n : ℕ} (M : ClosedPositiveQK.{uR} n) :
    IsLocallyRiemannianSymmetric n M.space.carrier := by
  obtain ⟨S⟩ := project_symmetricHomothety P p H M
  exact H.riemannian.homothetyParallel n M.space S.target.space S.map
    (H.riemannian.symmetriesParallel n S.target)

section OriginalSignature

variable (n : ℕ) (M : Type uR)
variable [EMetricSpace M] [ChartedSpace (Model n) M]
variable [IsManifold (model n) ∞ M]
variable [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
variable [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
  (fun x : M => TangentSpace (model n) x)]
variable [IsRiemannianManifold (model n) M]
variable [Nonempty M] [CompactSpace M] [ConnectedSpace M]

/-- PREFERRED ROOT: the same mathematical conclusion as the original leBrunSalamon declaration, with all
project proof inputs visible. This theorem does NOT call that admitted original declaration. -/
theorem leBrunSalamon_fromProjectInputs
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) (H : ProjectInputs.{uR} P p)
    (hn : 2 ≤ n) (hQK : IsPositiveQuaternionicKahler n M) :
    IsLocallyRiemannianSymmetric n M := by
  let R : ClosedRiemannianSpace.{uR} n :=
    { carrier := M, metric := inferInstance, charts := inferInstance
      smooth := inferInstance, riemannian := inferInstance, smoothMetric := inferInstance
      intrinsicDistance := inferInstance, compact := inferInstance
      connected := inferInstance, nonempty := inferInstance }
  exact project_parallelCurvature P p H (⟨R, hn, hQK⟩ : ClosedPositiveQK.{uR} n)

/-- CANONICAL ROOT: all source choices are fixed; only the eleven
project theorem obligations remain as explicit input. -/
theorem leBrunSalamon_project
    (H : ProjectInputs.{uR} canonicalProjectiveLine canonicalMarkedPoint)
    (hn : 2 ≤ n) (hQK : IsPositiveQuaternionicKahler n M) :
    IsLocallyRiemannianSymmetric n M :=
  leBrunSalamon_fromProjectInputs n M canonicalProjectiveLine canonicalMarkedPoint H hn hQK

end OriginalSignature

/-- Compatibility with the previously introduced core; this does not use its older admitted final targets.
The kernel cut is now split into full-family construction and diagonal normalization. -/
def AlgebraicInputs.toCore (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (H : AlgebraicInputs P p) : ManuscriptCoreInputs P p where
  nonprimitive := H.nonprimitive
  smoothing := H.smoothing
  kernelConstruction := by
    intro n X hp g
    obtain ⟨D⟩ := H.movingPairAndDescent n X hp g
    obtain ⟨K, _⟩ := H.familyToDiagonal n X g D
    exact ⟨K⟩

end LeBrunSalamon.Skeleton

end
